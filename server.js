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

// ─── MIDDLEWARE ───────────────────────────────────────────────────────────────
app.use(cors());
app.use(express.json());
app.use(express.static(path.join(__dirname)));

// ─── IN-MEMORY CACHE ─────────────────────────────────────────────────────────
const cache = {
  trades:    [],
  timestamp: null,
  sources:   { house: 0, senate: 0, aletheia: 0 },
};

// ─── UTILITIES ────────────────────────────────────────────────────────────────

/**
 * Remove leading "$", strip suffix classes (.COMM, etc.), upper-case.
 * Returns null if the result doesn't look like a real ticker.
 */
function cleanTicker(raw) {
  if (!raw || typeof raw !== 'string') return null;
  const t = raw.replace(/^\$/, '').toUpperCase().split(/[.\s,]/)[0].trim();
  const SKIP = new Set(['N/A', 'NA', '--', 'N', 'NONE', '', 'N/A-','CASH']);
  if (SKIP.has(t) || t.length === 0 || t.length > 5) return null;
  if (!/^[A-Z]{1,5}$/.test(t)) return null; // must be letters only
  return t;
}

/**
 * Map raw type string → 'buy' | 'sell' | null (null = skip non-trade events)
 */
function normalizeType(raw) {
  if (!raw) return null;
  const t = raw.toString().toLowerCase();
  if (t.includes('purchase')) return 'buy';
  if (t.includes('sale')  || t.includes('sell'))  return 'sell';
  // SEC Form 4 transaction codes
  if (t === 'p' || t === 'a' || t === 'm') return 'buy';
  if (t === 's' || t === 'd' || t === 'f') return 'sell';
  return null; // skip exchanges, gifts, options exercises, etc.
}

/**
 * Normalize political party abbreviation → 'D' | 'R' | 'I'
 */
function normalizeParty(raw) {
  if (!raw) return 'I';
  const p = raw.toString().toLowerCase().trim();
  if (p === 'd' || p.startsWith('dem')) return 'D';
  if (p === 'r' || p.startsWith('rep')) return 'R';
  return 'I';
}

/**
 * Derive a 1–5 signal score from the trade-size label string.
 */
function scoreFromSizeLabel(lbl) {
  if (!lbl || typeof lbl !== 'string') return 2;
  // Anchored to the high-end boundary of each bracket
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
 * Derive a 1–5 score from a raw dollar value (Aletheia data).
 */
function scoreFromDollarValue(v) {
  if (!v || isNaN(v)) return 2;
  if (v > 1_000_000) return 5;
  if (v >   500_000) return 5;
  if (v >   250_000) return 4;
  if (v >   100_000) return 3;
  if (v >    50_000) return 3;
  if (v >    15_000) return 2;
  return 1;
}

/**
 * Parse a date string that may be MM/DD/YYYY or YYYY-MM-DD.
 * Returns an ISO string, or null on failure.
 */
function parseDate(str) {
  if (!str) return null;
  if (/^\d{2}\/\d{2}\/\d{4}$/.test(str)) {
    const [m, d, y] = str.split('/');
    const iso = `${y}-${m.padStart(2,'0')}-${d.padStart(2,'0')}`;
    const dt  = new Date(iso);
    return isNaN(dt) ? null : dt.toISOString();
  }
  const dt = new Date(str);
  return isNaN(dt) ? null : dt.toISOString();
}

/**
 * Build a deterministic, URL-safe ID for deduplication.
 */
function makeId(source, datePart, namePart, ticker) {
  const raw = `${source}|${datePart}|${namePart}|${ticker}`;
  return crypto.createHash('md5').update(raw).digest('hex');
}

/**
 * Format a raw dollar amount into a compact string.
 */
function formatDollar(val) {
  if (!val || isNaN(val)) return 'Unknown';
  const n = Number(val);
  if (n >= 1_000_000) return `$${(n / 1_000_000).toFixed(1)}M`;
  if (n >=     1_000) return `$${Math.round(n / 1_000)}K`;
  return `$${n}`;
}

// ─── DATA FETCHERS ────────────────────────────────────────────────────────────

/**
 * House of Representatives — STOCK Act disclosures
 * Public dataset maintained at house-stock-watcher-data.s3-us-west-2.amazonaws.com
 */
async function fetchHouseTrades() {
  const URL = 'https://house-stock-watcher-data.s3-us-west-2.amazonaws.com/data/all_transactions.json';

  const { data } = await axios.get(URL, {
    timeout: 45_000,
    headers: { 'Accept-Encoding': 'gzip' },
  });

  if (!Array.isArray(data)) throw new Error('House data: unexpected format');

  const cutoff = new Date();
  cutoff.setDate(cutoff.getDate() - LOOKBACK_DAYS);

  const trades = [];

  for (const row of data) {
    // Filter to lookback window
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

/**
 * U.S. Senate — STOCK Act disclosures
 * Public dataset maintained at senate-stock-watcher-data.s3-us-west-2.amazonaws.com
 */
async function fetchSenateTrades() {
  const URL = 'https://senate-stock-watcher-data.s3-us-west-2.amazonaws.com/aggregate/all_transactions.json';

  const { data } = await axios.get(URL, {
    timeout: 45_000,
    headers: { 'Accept-Encoding': 'gzip' },
  });

  if (!Array.isArray(data)) throw new Error('Senate data: unexpected format');

  const cutoff = new Date();
  cutoff.setDate(cutoff.getDate() - LOOKBACK_DAYS);

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

      // Senate data sometimes includes disclosure_date inside the transaction
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

/**
 * Aletheia API — SEC Form 4 corporate insider trades (optional).
 * Activated only when ALETHEIA_API_KEY is set in .env.
 * Note: this source tracks corporate executives/directors, NOT politicians.
 */
async function fetchAletheiaTrades() {
  const apiKey = process.env.ALETHEIA_API_KEY;
  if (!apiKey) return [];

  let data;
  try {
    const res = await axios.get('https://api.aletheiaapi.com/LatestTransactions', {
      headers: { key: apiKey },
      params:  { top: 50 },
      timeout: 10_000,
    });
    data = res.data;
  } catch (err) {
    // Endpoint may be deprecated — fail silently
    console.warn('[QUORUM] Aletheia LatestTransactions unavailable:', err.message);
    return [];
  }

  if (!Array.isArray(data)) return [];

  const trades = [];

  for (const t of data) {
    const ticker = cleanTicker(t.Symbol || t.Ticker || t.SecuritySymbol);
    if (!ticker) continue;

    const type = normalizeType(
      t.TransactionCode || t.AcquiredOrDisposed || t.TransactionType
    );
    if (!type) continue;

    const sharesRaw = parseFloat(t.SharesTraded || t.Shares || 0);
    const priceRaw  = parseFloat(t.PricePerShare || t.Price || 0);
    const totalVal  = sharesRaw * priceRaw;

    const txDate   = parseDate(t.TransactionDate) || new Date().toISOString();
    const discDate = parseDate(t.FilingDate || t.ReportDate) || txDate;
    const name     = (t.Owner || t.OwnerName || 'Corporate Insider').trim();

    trades.push({
      id:          makeId('aletheia', t.FilingDate || t.TransactionDate, name, ticker),
      name,
      ticker,
      company:     (t.Issuer || t.IssuerName || ticker).trim(),
      type,
      sizeLabel:   totalVal > 0 ? formatDollar(totalVal) : 'See filing',
      timestamp:   txDate,
      disclosedAt: discDate,
      chamber:     'INS',   // Corporate Insider — not a politician
      party:       'C',
      state:       'US',
      score:       scoreFromDollarValue(totalVal),
      source:      'aletheia',
    });
  }

  return trades;
}

/**
 * Convert a US state full name to its 2-letter abbreviation.
 */
function stateAbbr(name) {
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
  if (!name) return 'US';
  if (name.length === 2) return name.toUpperCase();
  return MAP[name] || name.toUpperCase().slice(0, 2);
}

// ─── CACHE REFRESH ────────────────────────────────────────────────────────────

async function refreshCache() {
  console.log('[QUORUM] Refreshing trade data…');
  const t0 = Date.now();

  const [houseResult, senateResult, aletheiaResult] = await Promise.allSettled([
    fetchHouseTrades(),
    fetchSenateTrades(),
    fetchAletheiaTrades(),
  ]);

  const houseTrades    = houseResult.status    === 'fulfilled' ? houseResult.value    : [];
  const senateTrades   = senateResult.status   === 'fulfilled' ? senateResult.value   : [];
  const aletheiaTrades = aletheiaResult.status === 'fulfilled' ? aletheiaResult.value : [];

  if (houseResult.status    === 'rejected') console.warn('[QUORUM] House fetch failed:',    houseResult.reason?.message);
  if (senateResult.status   === 'rejected') console.warn('[QUORUM] Senate fetch failed:',   senateResult.reason?.message);
  if (aletheiaResult.status === 'rejected') console.warn('[QUORUM] Aletheia fetch failed:', aletheiaResult.reason?.message);

  // Merge and deduplicate by ID
  const seen  = new Set();
  const all   = [...houseTrades, ...senateTrades, ...aletheiaTrades].filter(t => {
    if (!t || !t.id || !t.ticker || !t.name) return false;
    if (seen.has(t.id)) return false;
    seen.add(t.id);
    return true;
  });

  // Sort: most recently DISCLOSED first
  all.sort((a, b) => new Date(b.disclosedAt) - new Date(a.disclosedAt));

  // Keep the freshest 300 for the feed
  cache.trades    = all.slice(0, 300);
  cache.timestamp = Date.now();
  cache.sources   = {
    house:    houseTrades.length,
    senate:   senateTrades.length,
    aletheia: aletheiaTrades.length,
  };

  const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
  console.log(
    `[QUORUM] Cache ready: ${cache.trades.length} trades ` +
    `(house:${cache.sources.house} senate:${cache.sources.senate} aletheia:${cache.sources.aletheia}) ` +
    `in ${elapsed}s`
  );
}

// ─── ROUTES ───────────────────────────────────────────────────────────────────

/**
 * GET /api/trades
 * Returns the normalized trade feed.
 * Respects cache; triggers refresh if stale.
 */
app.get('/api/trades', async (req, res) => {
  try {
    const isStale = !cache.timestamp || (Date.now() - cache.timestamp > CACHE_TTL_MS);
    if (isStale) {
      await refreshCache();
    }

    // Optional server-side filter params (frontend may also filter)
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
    res.status(500).json({ error: 'Failed to fetch trades', message: err.message });
  }
});

/**
 * GET /api/health
 * Quick health check — useful for debugging.
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
    aletheiaEnabled: !!process.env.ALETHEIA_API_KEY,
  });
});

/**
 * GET /api/refresh
 * Force a manual cache refresh (dev only).
 */
app.get('/api/refresh', async (req, res) => {
  try {
    await refreshCache();
    res.json({ ok: true, tradeCount: cache.trades.length, sources: cache.sources });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

/**
 * Serve the frontend.
 */
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'quorum.html'));
});

// ─── START ────────────────────────────────────────────────────────────────────

app.listen(PORT, async () => {
  console.log('');
  console.log('  ██████  ██    ██  ██████  ██████  ██    ██ ███    ███');
  console.log(' ██    ██ ██    ██ ██    ██ ██   ██ ██    ██ ████  ████');
  console.log(' ██    ██ ██    ██ ██    ██ ██████  ██    ██ ██ ████ ██');
  console.log(' ██ ▄▄ ██ ██    ██ ██    ██ ██   ██ ██    ██ ██  ██  ██');
  console.log('  ██████   ██████   ██████  ██   ██  ██████  ██      ██');
  console.log('     ▀▀                     Political Trade Intelligence');
  console.log('');
  console.log(`  → http://localhost:${PORT}`);
  console.log(`  → Aletheia key: ${process.env.ALETHEIA_API_KEY ? '✓ configured' : '✗ not set (optional)'}`);
  console.log('');

  // Warm the cache on boot (non-blocking — the first /api/trades will also trigger this)
  refreshCache().catch(err => console.error('[QUORUM] Initial refresh failed:', err.message));
});
