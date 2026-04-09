'use strict';
require('dotenv').config();

const express = require('express');
const axios   = require('axios');
const cors    = require('cors');
const path    = require('path');
const crypto  = require('crypto');

const app  = express();
const PORT = parseInt(process.env.PORT, 10) || 3000;

const CACHE_TTL_MS  = parseInt(process.env.CACHE_TTL_MS, 10)  || 5 * 60 * 1000; // 5 min
const LOOKBACK_DAYS = parseInt(process.env.LOOKBACK_DAYS, 10) || 90;
const MAX_FILINGS   = parseInt(process.env.MAX_FILINGS,  10)  || 60; // max XML fetches per refresh

// ─── MIDDLEWARE ───────────────────────────────────────────────────────────────
app.use(cors());
app.use(express.json());
app.use(express.static(path.join(__dirname)));

// ─── IN-MEMORY CACHE ─────────────────────────────────────────────────────────
const cache = {
  trades:    [],
  timestamp: null,
  sources:   { house: 0, senate: 0 },
};

let refreshing = false; // prevent parallel duplicate refreshes

// ─── UTILITIES ────────────────────────────────────────────────────────────────

/** Normalise a raw ticker string → uppercase 1-5 letter symbol, or null. */
function cleanTicker(raw) {
  if (!raw || typeof raw !== 'string') return null;
  const t = raw.replace(/^\$/, '').toUpperCase().split(/[.\s,;]/)[0].trim();
  const SKIP = new Set(['N/A','NA','--','N','NONE','','N/A-','CASH','GOVT']);
  if (SKIP.has(t) || t.length < 1 || t.length > 5) return null;
  if (!/^[A-Z]{1,5}$/.test(t)) return null;
  return t;
}

/** Map raw trade-type string → 'buy' | 'sell' | null (null = ignore). */
function normalizeType(raw) {
  if (!raw) return null;
  const t = raw.toString().toLowerCase();
  if (t.includes('purchase') || t.includes('acqui')) return 'buy';
  if (t.includes('sale') || t.includes('sell'))      return 'sell';
  return null;
}

/** Map party string → 'D' | 'R' | 'I'. */
function normalizeParty(raw) {
  if (!raw) return 'I';
  const p = raw.toString().toLowerCase().trim();
  if (p === 'd' || p.startsWith('dem')) return 'D';
  if (p === 'r' || p.startsWith('rep')) return 'R';
  return 'I';
}

/** Derive 1-5 signal score from a bracket string like "$50,001 - $100,000". */
function scoreFromSizeLabel(lbl) {
  if (!lbl || typeof lbl !== 'string') return 2;
  if (/\$25,000,001|\$50,000,001|Over \$50|Over \$25/i.test(lbl)) return 5;
  if (/\$5,000,001|\$25,000,000/i.test(lbl))                       return 5;
  if (/\$1,000,001/i.test(lbl))                                     return 5;
  if (/\$500,001/i.test(lbl))                                       return 5;
  if (/\$250,001/i.test(lbl))                                       return 4;
  if (/\$100,001/i.test(lbl))                                       return 3;
  if (/\$50,001/i.test(lbl))                                        return 3;
  if (/\$15,001/i.test(lbl))                                        return 2;
  return 1;
}

/**
 * Parse a date string in MM/DD/YYYY or YYYY-MM-DD format.
 * Returns an ISO string, or null.
 */
function parseDate(str) {
  if (!str) return null;
  if (/^\d{2}\/\d{2}\/\d{4}$/.test(str)) {
    const [m, d, y] = str.split('/');
    const dt = new Date(`${y}-${m.padStart(2,'0')}-${d.padStart(2,'0')}`);
    return isNaN(dt) ? null : dt.toISOString();
  }
  const dt = new Date(str);
  return isNaN(dt) ? null : dt.toISOString();
}

/** Build a deterministic MD5-based ID for deduplication. */
function makeId(source, datePart, namePart, ticker) {
  const raw = `${source}|${datePart}|${namePart}|${ticker}`;
  return crypto.createHash('md5').update(raw).digest('hex');
}

/** Convert a US state full name to its 2-letter abbreviation. */
function stateAbbr(name) {
  if (!name) return 'US';
  if (/^[A-Z]{2}$/.test(name)) return name;
  const MAP = {
    'Alabama':'AL','Alaska':'AK','Arizona':'AZ','Arkansas':'AR','California':'CA',
    'Colorado':'CO','Connecticut':'CT','Delaware':'DE','Florida':'FL','Georgia':'GA',
    'Hawaii':'HI','Idaho':'ID','Illinois':'IL','Indiana':'IN','Iowa':'IA',
    'Kansas':'KS','Kentucky':'KY','Louisiana':'LA','Maine':'ME','Maryland':'MD',
    'Massachusetts':'MA','Michigan':'MI','Minnesota':'MN','Mississippi':'MS',
    'Missouri':'MO','Montana':'MT','Nebraska':'NE','Nevada':'NV',
    'New Hampshire':'NH','New Jersey':'NJ','New Mexico':'NM','New York':'NY',
    'North Carolina':'NC','North Dakota':'ND','Ohio':'OH','Oklahoma':'OK',
    'Oregon':'OR','Pennsylvania':'PA','Rhode Island':'RI','South Carolina':'SC',
    'South Dakota':'SD','Tennessee':'TN','Texas':'TX','Utah':'UT',
    'Vermont':'VT','Virginia':'VA','Washington':'WA','West Virginia':'WV',
    'Wisconsin':'WI','Wyoming':'WY',
  };
  return MAP[name] || name.toUpperCase().slice(0, 2);
}

/** Extract first occurrence of a simple XML tag value using regex. */
function xmlTag(xml, ...tags) {
  for (const tag of tags) {
    const m = xml.match(new RegExp(`<${tag}[^>]*>([^<]*)<\\/${tag}>`, 'i'));
    if (m) return m[1].trim();
  }
  return null;
}

/** Extract all inner-XML blocks matching a tag name. */
function xmlBlocks(xml, tag) {
  const re  = new RegExp(`<${tag}[^>]*>([\\s\\S]*?)<\\/${tag}>`, 'gi');
  const out = [];
  let m;
  while ((m = re.exec(xml)) !== null) out.push(m[1]);
  return out;
}

/** Cutoff date string (YYYY-MM-DD) for the configured lookback window. */
function fromDateStr(days = LOOKBACK_DAYS) {
  const d = new Date();
  d.setDate(d.getDate() - days);
  return d.toISOString().split('T')[0];
}

// ─── SOURCE 1: SENATE EFTS (official government API) ─────────────────────────
//
// Senate Electronic Filing Tracking System
// Official public API: https://efts.senate.gov/
//
// Step 1 – JSON search for recent PTR (Periodic Transaction Report) filings.
// Step 2 – For each filing, fetch its XML and parse individual trades.

async function fetchSenateEFTS() {
  // ── 1a: Search for recent PTR filings ──────────────────────────────────────
  let hits = [];
  try {
    const { data } = await axios.get('https://efts.senate.gov/LATEST/search-index', {
      params: {
        q:            '',
        dateRange:    'custom',
        fromDate:     fromDateStr(),
        results_count: 100,
        filing_type:  'PTR',
      },
      timeout: 20_000,
      headers: {
        'User-Agent': 'Mozilla/5.0 (compatible; PublicDisclosureBot/1.0)',
        'Accept':     'application/json',
      },
    });
    hits = data?.hits?.hits ?? [];
  } catch (err) {
    throw new Error(`EFTS search: ${err.message}`);
  }

  if (!hits.length) return [];

  // ── 1b: Fetch & parse XML for each filing ──────────────────────────────────
  const trades = [];

  await Promise.allSettled(
    hits.slice(0, MAX_FILINGS).map(async (hit) => {
      const src      = hit._source ?? {};
      const reportId = src.report_id || hit._id;
      if (!reportId) return;

      const lastName  = (src.last_name  || '').trim();
      const firstName = (src.first_name || '').trim();
      const name      = [firstName, lastName].filter(Boolean).join(' ') || 'Unknown Senator';
      const state     = stateAbbr(src.state || src.senator_state || '');
      const party     = normalizeParty(src.party);
      const filedDate = src.date_filed || '';

      let xml = '';
      try {
        const { data } = await axios.get(
          `https://efts.senate.gov/LATEST/disclosure-xml/${reportId}.xml`,
          {
            timeout: 12_000,
            headers: { 'User-Agent': 'Mozilla/5.0 (compatible; PublicDisclosureBot/1.0)' },
          }
        );
        xml = typeof data === 'string' ? data : '';
      } catch {
        return; // filing XML unavailable — skip silently
      }

      if (!xml) return;

      // Parse transaction blocks (Senate EFTS XML uses <Transaction> tags)
      const txBlocks = xmlBlocks(xml, 'Transaction');

      for (const txXml of txBlocks) {
        // Try multiple possible field names for robustness
        const ticker = cleanTicker(
          xmlTag(txXml, 'Ticker') ||
          xmlTag(txXml, 'CUSIP')  ||
          xmlTag(txXml, 'Symbol')
        );
        if (!ticker) continue;

        const typeRaw = xmlTag(txXml, 'TransactionType', 'Type', 'TranType') || '';
        const type    = normalizeType(typeRaw);
        if (!type) continue;

        const dateRaw = xmlTag(txXml, 'TransactionDate', 'Date', 'TranDate') || filedDate;
        const txDate  = parseDate(dateRaw);
        if (!txDate) continue;

        // Cutoff check
        if (new Date(txDate) < new Date(fromDateStr())) continue;

        const amount    = xmlTag(txXml, 'Amount', 'AmountRange') || 'Unknown';
        const assetName =
          xmlTag(txXml, 'AssetName', 'Name', 'Asset', 'Description') ||
          ticker;
        const discDate  = parseDate(filedDate) || txDate;

        trades.push({
          id:          makeId('senate', dateRaw, lastName, ticker),
          name,
          ticker,
          company:     assetName.trim(),
          type,
          sizeLabel:   amount.trim(),
          timestamp:   txDate,
          disclosedAt: discDate,
          chamber:     'SEN',
          party,
          state,
          score:       scoreFromSizeLabel(amount),
          source:      'senate',
        });
      }
    })
  );

  return trades;
}

// ─── SOURCE 2: HOUSE CLERK (official government site) ────────────────────────
//
// House Financial Disclosure System
// Official site: https://disclosures-clerk.house.gov/
//
// Step 1 – POST to the PTR search to get a list of recent filings.
// Step 2 – Extract filing IDs from the HTML response.
// Step 3 – For each filing, try to fetch its XML (electronic / eFD filings).
//          Paper filers only have PDFs — those are skipped for this MVP.

async function fetchHouseClerk() {
  const year = new Date().getFullYear();

  // ── 2a: Search for PTR filings ─────────────────────────────────────────────
  let html = '';
  try {
    const { data } = await axios.post(
      'https://disclosures-clerk.house.gov/FinancialDisclosure/search',
      `transactTypeCd=P&reportYear=${year}&submit=search`,
      {
        timeout: 20_000,
        headers: {
          'Content-Type': 'application/x-www-form-urlencoded',
          'User-Agent':   'Mozilla/5.0 (compatible; PublicDisclosureBot/1.0)',
          'Accept':       'text/html,application/xhtml+xml',
        },
      }
    );
    html = typeof data === 'string' ? data : '';
  } catch (err) {
    throw new Error(`House Clerk search: ${err.message}`);
  }

  // ── 2b: Extract filing IDs from search results HTML ────────────────────────
  // Pattern: /public_disc/ptr-pdfs/YEAR/FILEID.pdf
  const filingRe  = /\/public_disc\/ptr-pdfs\/\d{4}\/(\d+)\.pdf/g;
  const seen      = new Set();
  const filingIds = [];
  let m;
  while ((m = filingRe.exec(html)) !== null) {
    if (!seen.has(m[1])) {
      seen.add(m[1]);
      filingIds.push(m[1]);
    }
  }

  if (!filingIds.length) return [];

  // ── 2c: Fetch XML for each electronic (eFD) filing ─────────────────────────
  const trades = [];

  await Promise.allSettled(
    filingIds.slice(0, MAX_FILINGS).map(async (fileId) => {
      // Electronic filings have an XML counterpart at the same base path
      let xml = '';
      try {
        const { data } = await axios.get(
          `https://disclosures-clerk.house.gov/public_disc/ptr-pdfs/${year}/${fileId}.xml`,
          {
            timeout: 10_000,
            headers: { 'User-Agent': 'Mozilla/5.0 (compatible; PublicDisclosureBot/1.0)' },
          }
        );
        xml = typeof data === 'string' ? data : '';
      } catch {
        return; // paper filer (PDF only) — skip
      }

      if (!xml || !xml.includes('<')) return;

      // Extract member info
      const lastName  = xmlTag(xml, 'Last', 'LastName', 'MemberLast')  || '';
      const firstName = xmlTag(xml, 'First', 'FirstName', 'MemberFirst') || '';
      const name      = [firstName, lastName].filter(Boolean).join(' ') || 'Unknown Member';
      const stateRaw  = xmlTag(xml, 'StateDst', 'State', 'MemberState') || 'US';
      const state     = stateAbbr(stateRaw.split('-')[0]); // "CA-01" → "CA"
      const party     = normalizeParty(xmlTag(xml, 'Party', 'MemberParty') || '');

      // Parse transactions
      const txBlocks = xmlBlocks(xml, 'Transaction');

      for (const txXml of txBlocks) {
        const ticker = cleanTicker(
          xmlTag(txXml, 'Ticker', 'ticker') ||
          xmlTag(txXml, 'CUSIP')
        );
        if (!ticker) continue;

        const typeRaw = xmlTag(txXml, 'TranType', 'TransactionType', 'Type') || '';
        const type    = normalizeType(typeRaw);
        if (!type) continue;

        const dateRaw = xmlTag(txXml, 'TranDate', 'TransactionDate', 'Date') || '';
        const txDate  = parseDate(dateRaw);
        if (!txDate) continue;

        if (new Date(txDate) < new Date(fromDateStr())) continue;

        const amount    = xmlTag(txXml, 'Amount', 'AmountRange') || 'Unknown';
        const assetName = xmlTag(txXml, 'AssetName', 'Asset', 'Name') || ticker;

        trades.push({
          id:          makeId('house', dateRaw, lastName, ticker),
          name,
          ticker,
          company:     assetName.trim(),
          type,
          sizeLabel:   amount.trim(),
          timestamp:   txDate,
          disclosedAt: txDate,
          chamber:     'REP',
          party,
          state,
          score:       scoreFromSizeLabel(amount),
          source:      'house',
        });
      }
    })
  );

  return trades;
}

// ─── LEGACY FALLBACK: Community-aggregated S3 datasets ───────────────────────
// These datasets were processed from official STOCK Act disclosures and hosted
// publicly, but the S3 buckets have since been taken offline (HTTP 403).
// Kept here as a fallback in case hosting is restored.

const LEGACY_HOUSE_URL   = 'https://house-stock-watcher-data.s3-us-west-2.amazonaws.com/data/all_transactions.json';
const LEGACY_SENATE_URL  = 'https://senate-stock-watcher-data.s3-us-west-2.amazonaws.com/aggregate/all_transactions.json';

async function fetchLegacyHouse() {
  const { data } = await axios.get(LEGACY_HOUSE_URL, {
    timeout: 30_000,
    headers: { 'Accept-Encoding': 'gzip' },
  });
  if (!Array.isArray(data)) throw new Error('unexpected format');

  const cutoff = new Date(fromDateStr());
  const trades = [];

  for (const row of data) {
    const txDate = parseDate(row.transaction_date);
    if (!txDate || new Date(txDate) < cutoff) continue;

    const ticker = cleanTicker(row.ticker);
    if (!ticker) continue;

    const type = normalizeType(row.type);
    if (!type) continue;

    const discDate = parseDate(row.disclosure_date) || txDate;
    const name     = (row.representative || '').trim() || 'Unknown Member';

    trades.push({
      id:          makeId('house', row.disclosure_date, name, ticker),
      name,
      ticker,
      company:     (row.asset_description || ticker).trim(),
      type,
      sizeLabel:   (row.amount || 'Unknown').trim(),
      timestamp:   txDate,
      disclosedAt: discDate,
      chamber:     'REP',
      party:       normalizeParty(row.party),
      state:       (row.state || 'US').trim().toUpperCase().slice(0, 2),
      score:       scoreFromSizeLabel(row.amount),
      source:      'house',
    });
  }

  return trades;
}

async function fetchLegacySenate() {
  const { data } = await axios.get(LEGACY_SENATE_URL, {
    timeout: 30_000,
    headers: { 'Accept-Encoding': 'gzip' },
  });
  if (!Array.isArray(data)) throw new Error('unexpected format');

  const cutoff = new Date(fromDateStr());
  const trades = [];

  for (const senator of data) {
    const firstName = (senator.first_name || '').trim();
    const lastName  = (senator.last_name  || '').trim();
    const name      = [firstName, lastName].filter(Boolean).join(' ') || 'Unknown Senator';
    const party     = normalizeParty(senator.party);
    const state     = stateAbbr(senator.state || 'US');

    for (const tx of (senator.transactions || [])) {
      const txDate = parseDate(tx.transaction_date);
      if (!txDate || new Date(txDate) < cutoff) continue;

      const ticker = cleanTicker(tx.ticker);
      if (!ticker) continue;

      const type = normalizeType(tx.type);
      if (!type) continue;

      const discDate = parseDate(tx.disclosure_date) || txDate;

      trades.push({
        id:          makeId('senate', tx.transaction_date, lastName, ticker),
        name,
        ticker,
        company:     (tx.asset_name || ticker).trim(),
        type,
        sizeLabel:   (tx.amount || 'Unknown').trim(),
        timestamp:   txDate,
        disclosedAt: discDate,
        chamber:     'SEN',
        party,
        state,
        score:       scoreFromSizeLabel(tx.amount),
        source:      'senate',
      });
    }
  }

  return trades;
}

// ─── PRIMARY FETCHERS (with legacy fallback) ──────────────────────────────────

async function fetchHouseTrades() {
  // Try official House Clerk first, then legacy S3 as fallback
  try {
    const trades = await fetchHouseClerk();
    if (trades.length) return trades;
    console.warn('[QUORUM] House Clerk returned 0 trades, trying legacy S3…');
  } catch (err) {
    console.warn('[QUORUM] House Clerk unavailable:', err.message);
  }
  try {
    return await fetchLegacyHouse();
  } catch (err) {
    console.warn('[QUORUM] Legacy House S3 also unavailable:', err.message);
    return [];
  }
}

async function fetchSenateTrades() {
  // Try official EFTS first, then legacy S3 as fallback
  try {
    const trades = await fetchSenateEFTS();
    if (trades.length) return trades;
    console.warn('[QUORUM] Senate EFTS returned 0 trades, trying legacy S3…');
  } catch (err) {
    console.warn('[QUORUM] Senate EFTS unavailable:', err.message);
  }
  try {
    return await fetchLegacySenate();
  } catch (err) {
    console.warn('[QUORUM] Legacy Senate S3 also unavailable:', err.message);
    return [];
  }
}

// ─── CACHE REFRESH ────────────────────────────────────────────────────────────

async function refreshCache() {
  if (refreshing) return;
  refreshing = true;

  console.log('[QUORUM] Refreshing trade data…');
  const t0 = Date.now();

  const [houseResult, senateResult] = await Promise.allSettled([
    fetchHouseTrades(),
    fetchSenateTrades(),
  ]);

  const houseTrades  = houseResult.status  === 'fulfilled' ? houseResult.value  : [];
  const senateTrades = senateResult.status === 'fulfilled' ? senateResult.value : [];

  // Deduplicate by ID across both sources
  const seen = new Set();
  const all  = [...houseTrades, ...senateTrades].filter(t => {
    if (!t?.id || !t.ticker || !t.name) return false;
    if (seen.has(t.id)) return false;
    seen.add(t.id);
    return true;
  });

  // Sort: most recently disclosed first
  all.sort((a, b) => new Date(b.disclosedAt) - new Date(a.disclosedAt));

  cache.trades    = all.slice(0, 500);
  cache.timestamp = Date.now();
  cache.sources   = {
    house:  houseTrades.length,
    senate: senateTrades.length,
  };

  const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
  console.log(
    `[QUORUM] Cache ready: ${cache.trades.length} trades ` +
    `(house:${cache.sources.house} senate:${cache.sources.senate}) in ${elapsed}s`
  );

  refreshing = false;
}

// ─── ROUTES ───────────────────────────────────────────────────────────────────

/**
 * GET /api/trades
 * Returns normalised trade feed. Refreshes cache if stale.
 */
app.get('/api/trades', async (req, res) => {
  try {
    const isStale = !cache.timestamp || (Date.now() - cache.timestamp > CACHE_TTL_MS);
    if (isStale) await refreshCache();

    let trades = cache.trades;
    const { type, ticker, limit = 150 } = req.query;

    if (type   && ['buy','sell'].includes(type)) trades = trades.filter(t => t.type   === type);
    if (ticker)                                  trades = trades.filter(t => t.ticker === ticker.toUpperCase());

    res.json({
      trades:    trades.slice(0, Number(limit)),
      total:     cache.trades.length,
      fetchedAt: cache.timestamp,
      sources:   cache.sources,
    });
  } catch (err) {
    console.error('[QUORUM] /api/trades error:', err.message);
    // Always return valid shape so the frontend doesn't crash
    res.status(500).json({
      trades: [], total: 0, fetchedAt: null, sources: cache.sources,
      error: err.message,
    });
  }
});

/**
 * GET /api/health
 * Returns cache status, uptime, trade count.
 */
app.get('/api/health', (req, res) => {
  res.json({
    status:     'ok',
    uptime:     process.uptime().toFixed(0) + 's',
    tradeCount: cache.trades.length,
    sources:    cache.sources,
    cacheAge:   cache.timestamp
      ? Math.round((Date.now() - cache.timestamp) / 1000) + 's'
      : 'cold',
  });
});

/**
 * GET /api/refresh
 * Manually trigger a cache refresh.
 */
app.get('/api/refresh', async (req, res) => {
  try {
    await refreshCache();
    res.json({ ok: true, tradeCount: cache.trades.length, sources: cache.sources });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

/** Serve the frontend SPA for any non-API request. */
app.get('*', (req, res, next) => {
  if (req.path.startsWith('/api/')) return next();
  res.sendFile(path.join(__dirname, 'quorum.html'));
});

// ─── START ────────────────────────────────────────────────────────────────────

app.listen(PORT, () => {
  console.log('');
  console.log('  ██████  ██    ██  ██████  ██████  ██    ██ ███    ███');
  console.log(' ██    ██ ██    ██ ██    ██ ██   ██ ██    ██ ████  ████');
  console.log(' ██    ██ ██    ██ ██    ██ ██████  ██    ██ ██ ████ ██');
  console.log(' ██ ▄▄ ██ ██    ██ ██    ██ ██   ██ ██    ██ ██  ██  ██');
  console.log('  ██████   ██████   ██████  ██   ██  ██████  ██      ██');
  console.log('     ▀▀                     Political Trade Intelligence');
  console.log('');
  console.log(`  → http://localhost:${PORT}`);
  console.log(`  → Primary:  Senate EFTS API | House Clerk eFD`);
  console.log(`  → Fallback: Community S3 datasets (legacy)`);
  console.log('');

  // Warm cache on boot (non-blocking)
  refreshCache().catch(err =>
    console.error('[QUORUM] Initial refresh failed:', err.message)
  );
});
