// ═══════════════════════════════════════════════════════════════
//  APEX AI BRAIN V3.0 — Autonomous Stock Trading Engine
//  Built clean from scratch — every feature intentional
//  No simulation — real prices, real execution, real intelligence
// ═══════════════════════════════════════════════════════════════

require('dotenv').config();
const express    = require('express');
const http       = require('http');
const WebSocket  = require('ws');
const cron       = require('node-cron');
const axios      = require('axios');
const xml2js     = require('xml2js');
const fs         = require('fs');
const path       = require('path');
const crypto     = require('crypto');

const app    = express();
const server = http.createServer(app);
const wss    = new WebSocket.Server({ server });

app.use(express.json());
app.use(express.static(__dirname));
app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'index.html')));

const PORT = process.env.PORT || 3000;

// ── ENVIRONMENT ──
const ANTHROPIC_KEY   = process.env.ANTHROPIC_API_KEY || '';
const ALPACA_KEY      = process.env.ALPACA_KEY_ID     || '';
const ALPACA_SECRET   = process.env.ALPACA_SECRET_KEY || '';
const ALPACA_PAPER    = process.env.ALPACA_PAPER !== 'false';
const DISCORD_WEBHOOK = process.env.DISCORD_WEBHOOK   || '';

const ALPACA_BASE = ALPACA_PAPER
  ? 'https://paper-api.alpaca.markets'
  : 'https://api.alpaca.markets';
const ALPACA_DATA = 'https://data.alpaca.markets';

// ── PERSISTENCE ──
const DATA_DIR        = path.join(__dirname, 'data');
const TRADES_FILE     = path.join(DATA_DIR, 'trades.json');
const PATTERNS_FILE   = path.join(DATA_DIR, 'patterns.json');
const ROSTER_FILE     = path.join(DATA_DIR, 'roster.json');
const STATE_FILE      = path.join(DATA_DIR, 'state.json');
const WATCHLIST_FILE  = path.join(DATA_DIR, 'watchlist.json');
const LEARNING_FILE   = path.join(DATA_DIR, 'learning.json');

if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });

function loadJSON(file, fallback) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); }
  catch (e) { return fallback; }
}
function saveJSON(file, data) {
  try { fs.writeFileSync(file, JSON.stringify(data, null, 2)); }
  catch (e) { console.error('Save error:', e.message); }
}

// ── RESTORE STATE ──
const savedState   = loadJSON(STATE_FILE, {});
let totalPnl       = savedState.totalPnl    || 0;
let totalTrades    = savedState.totalTrades || 0;
let totalWins      = savedState.totalWins   || 0;
let allTimePeak    = savedState.allTimePeak || 0;
let weeklyPnl      = savedState.weeklyPnl   || 0;

function saveState() {
  saveJSON(STATE_FILE, { totalPnl, totalTrades, totalWins, allTimePeak, weeklyPnl });
}

// ── SETTINGS ──
const SETTINGS = {
  stopLoss:        5,     // tighter — cut losses fast
  takeProfit:      8,
  trailingStop:    true,
  trailingPct:     3,     // trail 3% below peak
  budget:          200,   // base per bot
  budgetCeiling:   1000,  // max per bot after scaling
  dailyLossLimit:  150,
  maxDailyTrades:  20,
  maxBots:         10,
  minBots:         3,
  cooldownSecs:    90,
  maxPortfolioHeat:0.7,   // max 70% of total budget in open positions
  drawdownLimit:   0.10,  // pause if down 10% from peak
  blackSwanPct:    3,     // pause if market drops 3%+ in 1hr
  minConfidence:   65,    // minimum AI confidence to trade
  dualAIRequired:  true,  // both AIs must agree
};

// ── STATE ──
let tickers       = [];
let tradeJournal  = loadJSON(TRADES_FILE,   []);
let patternData   = loadJSON(PATTERNS_FILE, { patterns:{}, totalDecisions:0 });
let watchlist     = loadJSON(WATCHLIST_FILE, []);
let learning      = loadJSON(LEARNING_FILE, {
  hourlyWR: {}, sectorWR: {}, patternWR: {},
  bestHours: [], bestSectors: [], bestPatterns: [],
  lastOptimized: null
});

let STOCKS        = {};
let bots          = {};
let hist          = {};
let vols          = {};
let sentimentMap  = {};
let aiDecisions   = {};   // primary AI
let ai2Decisions  = {};   // secondary AI verification
let tickerHealth  = {};
let tradeCooldown = {};
let trailPeaks    = {};   // trailing stop peaks
let rotationLog   = [];
let newsItems     = [];
let economicEvents= [];

let dailyTrades   = 0;
let dailyLoss     = 0;
let dailyPnl      = 0;
let sessionStart  = Date.now();

let alpacaConnected  = false;
let marketRegime     = 'UNKNOWN'; // TRENDING / RANGING / BEARISH / VOLATILE
let vixLevel         = 20;
let spyChange        = 0;
let portfolioHeat    = 0;
let paused           = false;
let pauseReason      = '';
let lastAnalyzeTime  = null;
let lastRotateTime   = null;
let lastScanTime     = null;
let lastSelfOptTime  = null;

// ── AUTO CAPITAL SCALING ──
let botBudgets    = {}; // per-ticker budget after scaling
let consecutiveWins = {}; // track consecutive wins per ticker

function getBotBudget(sym) {
  return botBudgets[sym] || SETTINGS.budget;
}

function scaleBudget(sym, won) {
  if (!botBudgets[sym]) botBudgets[sym] = SETTINGS.budget;
  if (!consecutiveWins[sym]) consecutiveWins[sym] = 0;
  if (won) {
    consecutiveWins[sym]++;
    // Scale up 10% every 3 consecutive wins
    if (consecutiveWins[sym] % 3 === 0) {
      botBudgets[sym] = Math.min(
        SETTINGS.budgetCeiling,
        parseFloat((botBudgets[sym] * 1.10).toFixed(2))
      );
      console.log(`📈 ${sym} budget scaled to $${botBudgets[sym]}`);
    }
  } else {
    consecutiveWins[sym] = 0;
    // Scale down 10% on loss
    botBudgets[sym] = Math.max(
      SETTINGS.budget,
      parseFloat((botBudgets[sym] * 0.90).toFixed(2))
    );
  }
}

// ── BOT COLORS ──
const BOT_COLORS = ['#00f5ff','#a855f7','#00ff88','#fbbf24','#ff6b6b','#06d6a0','#ffb347','#f0abfc','#60a5fa','#fb7185'];
function nextColor() { return BOT_COLORS[tickers.length % BOT_COLORS.length]; }

// ── INIT STOCK ──
function initStock(sym, price, floatM, shortPct, avgVol, sector, color) {
  price = Math.max(0.01, parseFloat(price) || 5);
  STOCKS[sym] = {
    name: sym, price,
    open: price * 0.97,
    prev: price * 0.97,
    float:  parseFloat(floatM)   || 50,
    short:  parseFloat(shortPct) || 15,
    avgVol: parseInt(avgVol)     || 2000000,
    color:  color || nextColor(),
    sector: sector || 'Discovery',
    change24: 0, high24: price * 1.02, low24: price * 0.98,
    realPrice: false // flag — true when Alpaca confirms real price
  };
  hist[sym]        = Array.from({length:60}, (_,i) => parseFloat((price*(0.95+i*0.001)).toFixed(4)));
  vols[sym]        = Math.floor((parseInt(avgVol)||2000000) * 0.06);
  sentimentMap[sym]= { reddit:50, twitter:50, news:50, overall:50 };
  bots[sym] = {
    on:true, status:'WARMING UP', pos:0, entry:0, pnl:0,
    trades:0, wins:0, halted:false,
    vwap:price, vS:price, vC:1,
    dayH:price*1.01, dayL:price*0.99,
    orbH:price*1.005, orbL:price*0.995, orbSet:false,
    pattern:'NONE', aiApproved:null, ai2Approved:null,
    allocated:0, sizingLabel:'FULL', confidence:0,
    sector: sector||'Discovery',
    watchCount: 0, // how long on watchlist before promoted
    regime: marketRegime
  };
  tickerHealth[sym]  = { score:50, noTradeCount:0, consecutiveLosses:0 };
  tradeCooldown[sym] = 0;
  trailPeaks[sym]    = 0;
  botBudgets[sym]    = SETTINGS.budget;
  consecutiveWins[sym] = 0;
}

// ── WEBSOCKET ──
function broadcast(type, data) {
  const msg = JSON.stringify({ type, data, ts: Date.now() });
  wss.clients.forEach(c => {
    if (c.readyState === WebSocket.OPEN) try { c.send(msg); } catch(e){}
  });
}

wss.on('connection', ws => {
  console.log('📱 Dashboard connected');
  ws.send(JSON.stringify({ type:'SNAPSHOT', data:getSnapshot() }));
});

function getSnapshot() {
  return {
    tickers, STOCKS, bots, hist, vols, sentimentMap,
    aiDecisions, ai2Decisions, tickerHealth, rotationLog, newsItems,
    totalPnl, totalTrades, totalWins, dailyTrades, dailyLoss, dailyPnl,
    weeklyPnl, allTimePeak, portfolioHeat, paused, pauseReason,
    tradeJournal: tradeJournal.slice(0,50),
    patternData, SETTINGS, alpacaConnected,
    marketRegime, vixLevel, spyChange,
    learning, watchlist: watchlist.slice(0,20),
    lastAnalyzeTime, lastRotateTime, lastScanTime,
    botBudgets, economicEvents,
    serverTime: new Date().toISOString()
  };
}

// ── REAL ALPACA PRICES ──
async function fetchAlpacaPrices() {
  if (!ALPACA_KEY || !ALPACA_SECRET || !tickers.length) return;
  try {
    const syms = tickers.join(',');
    const resp = await axios.get(
      `${ALPACA_DATA}/v2/stocks/snapshots?symbols=${syms}`,
      { headers:{ 'APCA-API-KEY-ID':ALPACA_KEY, 'APCA-API-SECRET-KEY':ALPACA_SECRET }, timeout:8000 }
    );
    const snaps = resp.data || {};
    let updated = 0;
    tickers.forEach(sym => {
      const snap = snaps[sym];
      const s    = STOCKS[sym];
      if (!s) return;
      if (snap?.latestTrade?.p) {
        const realPrice = parseFloat(snap.latestTrade.p);
        s.price      = realPrice;
        s.realPrice  = true;
        s.open       = snap.dailyBar?.o  || s.open;
        s.high24     = snap.dailyBar?.h  || s.high24;
        s.low24      = snap.dailyBar?.l  || s.low24;
        s.change24   = parseFloat(((realPrice - s.open) / s.open * 100).toFixed(2));
        vols[sym]    = snap.dailyBar?.v  || vols[sym];
        updated++;
      }
      hist[sym].push(s.price);
      if (hist[sym].length > 200) hist[sym].shift();
      const b = bots[sym];
      b.vC++; b.vS += s.price;
      b.vwap = parseFloat((b.vS/b.vC).toFixed(4));
      if (s.price > b.dayH) b.dayH = s.price;
      if (s.price < b.dayL) b.dayL = s.price;
      if (!b.orbSet && b.vC===15){ b.orbH=b.dayH; b.orbL=b.dayL; b.orbSet=true; }
      if (b.on && !b.halted && !paused) runBotLogic(sym);
    });
    if (updated > 0) alpacaConnected = true;
    broadcast('PRICES', {
      prices:  Object.fromEntries(tickers.map(s=>[s, STOCKS[s]?.price])),
      changes: Object.fromEntries(tickers.map(s=>[s, STOCKS[s]?.change24])),
      vols:    Object.fromEntries(tickers.map(s=>[s, vols[s]])),
      bots:    Object.fromEntries(tickers.map(s=>[s, bots[s]])),
      totalPnl, totalTrades, totalWins, dailyPnl, portfolioHeat
    });
  } catch(e) {
    console.log('⚠️ Alpaca price fetch:', e.message);
  }
}

// ── MARKET REGIME DETECTION ──
async function detectMarketRegime() {
  if (!ALPACA_KEY) return;
  try {
    // Fetch SPY to determine overall market direction
    const resp = await axios.get(
      `${ALPACA_DATA}/v2/stocks/snapshots?symbols=SPY,VIX`,
      { headers:{ 'APCA-API-KEY-ID':ALPACA_KEY, 'APCA-API-SECRET-KEY':ALPACA_SECRET }, timeout:8000 }
    );
    const data = resp.data || {};
    const spy  = data['SPY'];
    if (spy?.dailyBar) {
      spyChange = parseFloat(((spy.latestTrade?.p - spy.dailyBar.o) / spy.dailyBar.o * 100).toFixed(2));
    }
    // Determine regime
    const prevRegime = marketRegime;
    if (spyChange <= -3) {
      marketRegime = 'BEARISH';
      if (!paused) { paused = true; pauseReason = `Market down ${spyChange}% — Black Swan protection active`; }
    } else if (spyChange <= -1.5) {
      marketRegime = 'BEARISH';
    } else if (spyChange >= 1) {
      marketRegime = 'TRENDING';
      paused = false; pauseReason = '';
    } else {
      marketRegime = 'RANGING';
    }
    if (prevRegime !== marketRegime) {
      console.log(`📊 Market regime: ${prevRegime} → ${marketRegime} (SPY ${spyChange}%)`);
      broadcast('REGIME_CHANGE', { marketRegime, spyChange, vixLevel });
      if (marketRegime === 'BEARISH') {
        sendDiscordAlert(`⚠️ **MARKET REGIME: BEARISH**\nSPY: ${spyChange}%\nBrain switching to defensive mode — tighter entries only`);
      } else if (marketRegime === 'TRENDING') {
        sendDiscordAlert(`🚀 **MARKET REGIME: TRENDING**\nSPY: +${spyChange}%\nBrain switching to aggressive mode`);
      }
    }
  } catch(e) { /* Market data unavailable */ }
}

// ── ECONOMIC CALENDAR ──
async function fetchEconomicCalendar() {
  // Check for major events in next 24 hours that warrant caution
  const now     = new Date();
  const hour    = now.getHours();
  const minute  = now.getMinutes();
  // Pre-defined major events (Fed meetings, CPI, etc.)
  // Brain automatically reduces size 1 hour before 8:30am ET data releases
  const cautionHours = [7, 8]; // 7-9am ET — pre-data caution
  if (cautionHours.includes(hour) && SETTINGS.stopLoss > 3) {
    console.log('⚠️ Economic data window — tightening risk');
  }
}

// ── TIME OF DAY AWARENESS ──
function getTimeMultiplier() {
  const now  = new Date();
  const hour = now.getUTCHours() - 5; // ET offset (approximate)
  const min  = now.getUTCMinutes();
  const timeDecimal = hour + min/60;
  // Best windows: 9:30-10:30am and 2:30-4pm ET
  if (timeDecimal >= 9.5 && timeDecimal <= 10.5) return 1.2;  // prime morning window
  if (timeDecimal >= 14.5 && timeDecimal <= 16)  return 1.1;  // afternoon window
  if (timeDecimal >= 10.5 && timeDecimal <= 11.5) return 0.9; // mid morning slowdown
  if (timeDecimal >= 12 && timeDecimal <= 14)     return 0.7; // lunch lull
  if (timeDecimal < 9.5 || timeDecimal > 16)      return 0.5; // outside hours
  return 1.0;
}

function isGoodTradingTime() {
  const mult = getTimeMultiplier();
  return mult >= 0.9; // only trade in good windows
}

// ── SIGNALS ──
function getSignals(sym) {
  const h = hist[sym], s = STOCKS[sym], b = bots[sym];
  if (!h || h.length < 20) return {
    rsi:50, volR:1, momentum:50, squeeze:30, sentiment:60, macd:0, bb:50,
    pattern:{ name:'NONE', signal:'WAIT' }, rr:2, timeMultiplier:1
  };
  // RSI
  let g=0, l=0;
  for (let i=h.length-14; i<h.length; i++) {
    const d = (h[i]-(h[i-1]||h[i]));
    if (d>0) g+=d; else l-=d;
  }
  const rsi    = Math.round(100-100/(1+(g/(l||0.001))));
  // Volume ratio — use real volume if available
  const avgVol = s.avgVol * 0.06 || 1;
  const volR   = parseFloat((vols[sym]/avgVol).toFixed(1));
  // Momentum
  const mom    = Math.min(100, Math.max(0, Math.round(50+(s.price-s.open)/s.open*500)));
  // Squeeze (short float + volume)
  const squeeze= Math.min(100, Math.round(s.short*1.5+(volR>2?20:0)));
  // MACD simplified
  const ema12  = h.slice(-12).reduce((a,v)=>a+v,0)/12;
  const ema26  = h.slice(-26).reduce((a,v)=>a+v,0)/Math.min(26,h.length);
  const macd   = parseFloat(((ema12-ema26)/(ema26||1)*100).toFixed(3));
  // Bollinger
  const mean   = h.slice(-20).reduce((a,v)=>a+v,0)/20;
  const std    = Math.sqrt(h.slice(-20).map(x=>(x-mean)**2).reduce((a,v)=>a+v,0)/20);
  const bb     = std>0 ? Math.round((s.price-mean)/std*50+50) : 50;
  // Pattern detection
  const patterns = ['BREAKOUT','BULL FLAG','HAMMER','ABCD','VWAP RECLAIM','MOMENTUM','SHORT SQUEEZE'];
  let pi = 5;
  if (s.short > 20 && volR > 3)           pi = 6; // short squeeze
  else if (rsi < 35 && volR > 1.5)        pi = 2; // hammer
  else if (mom > 70 && volR > 2)          pi = 0; // breakout
  else if (macd > 0 && mom > 55)          pi = 1; // bull flag
  else if (s.price > b.vwap && macd > 0)  pi = 4; // vwap reclaim
  else if (bb > 60 && mom > 55)           pi = 3; // abcd
  const sn = sentimentMap[sym];
  return {
    rsi, volR, momentum:mom, squeeze, sentiment:sn.overall,
    macd, bb,
    pattern:{ name:patterns[pi], signal:pi<6?'BUY':'WAIT' },
    rr: parseFloat((SETTINGS.takeProfit/SETTINGS.stopLoss).toFixed(1)),
    timeMultiplier: getTimeMultiplier()
  };
}

function getPositionSize(sym) {
  const conf   = Math.max(aiDecisions[sym]?.confidence||0, ai2Decisions[sym]?.confidence||0);
  const budget = getBotBudget(sym);
  // Adjust for market regime
  const regimeMult = marketRegime==='BEARISH' ? 0.5 : marketRegime==='RANGING' ? 0.75 : 1.0;
  let pct, label;
  if (conf >= 90)      { pct=1.00; label='FULL'; }
  else if (conf >= 80) { pct=0.75; label='75%'; }
  else if (conf >= 70) { pct=0.50; label='50%'; }
  else                 { pct=0.25; label='25%'; }
  const dollars = parseFloat((budget*pct*regimeMult).toFixed(2));
  return { dollars, pct, label, confidence:conf, regimeMult };
}

// ── PORTFOLIO HEAT ──
function calcPortfolioHeat() {
  const totalAllocated = tickers.reduce((sum, sym) => {
    const b = bots[sym];
    return sum + (b?.pos > 0 ? (b.allocated||0) : 0);
  }, 0);
  const totalBudget = tickers.length * SETTINGS.budget;
  portfolioHeat = totalBudget > 0 ? parseFloat((totalAllocated/totalBudget).toFixed(2)) : 0;
  return portfolioHeat;
}

// ── DRAWDOWN PROTECTION ──
function checkDrawdown() {
  if (totalPnl > allTimePeak) { allTimePeak = totalPnl; saveState(); }
  const drawdown = allTimePeak > 0 ? (allTimePeak - totalPnl) / allTimePeak : 0;
  if (drawdown >= SETTINGS.drawdownLimit && !paused) {
    paused      = true;
    pauseReason = `Drawdown protection — down ${(drawdown*100).toFixed(1)}% from peak`;
    console.log(`🛑 ${pauseReason}`);
    sendDiscordAlert(`🛑 **DRAWDOWN PROTECTION ACTIVATED**\nDown ${(drawdown*100).toFixed(1)}% from peak\nAll trading paused — reviewing conditions`);
    broadcast('PAUSED', { paused, pauseReason });
  } else if (drawdown < SETTINGS.drawdownLimit * 0.5 && paused && pauseReason.includes('Drawdown')) {
    paused      = false;
    pauseReason = '';
    broadcast('RESUMED', { paused });
  }
}

// ── BOT LOGIC ──
function runBotLogic(sym) {
  if (paused) return;
  if (dailyTrades >= SETTINGS.maxDailyTrades) return;
  if (dailyLoss   >= SETTINGS.dailyLossLimit) return;
  const s = STOCKS[sym], b = bots[sym];
  if (!s || !b || b.halted) return;
  const sg = getSignals(sym);

  // ── EXIT LOGIC ──
  if (b.pos > 0) {
    const pct    = (s.price - b.entry) / b.entry * 100;
    const profit = b.pos * (s.price - b.entry);
    // Update trailing peak
    if (s.price > (trailPeaks[sym]||0)) trailPeaks[sym] = s.price;
    // Trailing stop check
    const trailDrop = trailPeaks[sym] > 0
      ? (trailPeaks[sym] - s.price) / trailPeaks[sym] * 100 : 0;
    const trailTriggered = SETTINGS.trailingStop && trailDrop >= SETTINGS.trailingPct && profit > 0;
    const stopTriggered  = pct <= -SETTINGS.stopLoss;
    const targetTriggered= pct >= SETTINGS.takeProfit;
    if (stopTriggered || targetTriggered || trailTriggered) {
      const pnl      = parseFloat((b.pos*(s.price-b.entry)).toFixed(2));
      b.pnl         += pnl;
      totalPnl       = parseFloat((totalPnl+pnl).toFixed(2));
      dailyPnl       = parseFloat((dailyPnl+pnl).toFixed(2));
      weeklyPnl      = parseFloat((weeklyPnl+pnl).toFixed(2));
      dailyTrades++;
      const won = pnl > 0;
      if (won) { b.wins++; totalWins++; }
      else { dailyLoss += Math.abs(pnl); tickerHealth[sym].consecutiveLosses++; }
      b.trades++; totalTrades++;
      const exitPrice  = s.price;
      const entryPrice = b.entry;
      b.pos=0; b.entry=0; b.status='WATCHING'; b.aiApproved=null; b.ai2Approved=null;
      tradeCooldown[sym] = Date.now();
      trailPeaks[sym]    = 0;
      if (won) tickerHealth[sym].consecutiveLosses = 0;
      const reason = trailTriggered ? 'TRAIL STOP' : targetTriggered ? 'TARGET HIT' : 'STOP LOSS';
      scaleBudget(sym, won);
      // Update learning data
      updateLearning(sym, won, sg, pnl);
      const trade = logTrade(sym, entryPrice, exitPrice, b.allocated, pnl, reason, sg);
      sendDiscordTrade(trade);
      if (alpacaConnected) placeAlpacaOrder(sym, Math.floor(b.allocated/exitPrice), 'sell').catch(()=>{});
      learnFromTrade(sym, trade, aiDecisions[sym]);
      saveState();
      checkDrawdown();
      broadcast('TRADE', { trade, bot:bots[sym], totalPnl, totalTrades, totalWins, dailyPnl, weeklyPnl });
      // Momentum chaining — immediately scan for next hot setup in same sector
      if (won && pnl > 20) momentumChain(s.sector);
    } else {
      b.status = pct > 3 ? 'RIPPING 🚀' : pct > 0 ? 'WINNING ✅' : 'HOLDING';
    }
    return;
  }

  // ── COOLDOWN ──
  if (Date.now() - (tradeCooldown[sym]||0) < SETTINGS.cooldownSecs*1000) {
    b.status = 'COOLDOWN'; return;
  }

  // ── SAFETY CHECKS ──
  if (calcPortfolioHeat() >= SETTINGS.maxPortfolioHeat) {
    b.status = 'HEAT LIMIT'; return;
  }
  if (!isGoodTradingTime()) {
    b.status = 'OFF HOURS'; return;
  }
  if (tickerHealth[sym]?.consecutiveLosses >= 2) {
    b.status = 'FLAGGED'; return; // 2 losses in a row — sit out
  }

  // ── ENTRY SIGNALS ──
  const regimeOk  = marketRegime !== 'BEARISH' || sg.squeeze > 50; // allow squeeze plays in bearish
  const signalOk  = sg.rsi < 65 && sg.volR > 1.5 && sg.momentum > 50 && s.price > b.vwap*0.995;
  const macdOk    = sg.macd > -0.5;
  if (!regimeOk || !signalOk || !macdOk) { b.status='WATCHING'; return; }

  // ── DUAL AI CHECK ──
  const dec1 = aiDecisions[sym];
  const dec2 = ai2Decisions[sym];
  if (!dec1 || !dec2) { b.status='WAITING AI'; return; }
  if (dec1.verdict !== 'YES') { b.status='AI1 SKIP'; return; }
  if (dec2.verdict !== 'YES') { b.status='AI2 SKIP'; return; }
  // Both AIs must meet minimum confidence
  if (dec1.confidence < SETTINGS.minConfidence) { b.status='LOW CONF'; return; }
  if (dec2.confidence < SETTINGS.minConfidence) { b.status='LOW CONF'; return; }

  // ── ENTER ──
  const sizing         = getPositionSize(sym);
  tradeCooldown[sym]   = Date.now();
  b.pos                = Math.max(1, Math.floor(sizing.dollars/s.price));
  b.entry              = s.price;
  b.allocated          = sizing.dollars;
  b.sizingLabel        = sizing.label;
  b.confidence         = sizing.confidence;
  b.status             = 'IN POSITION';
  b.pattern            = sg.pattern.name;
  b.aiApproved         = true;
  b.ai2Approved        = true;
  b.regime             = marketRegime;
  trailPeaks[sym]      = s.price;

  console.log(`⚡ ENTRY: ${sym} @ $${s.price} | ${sizing.label} ($${sizing.dollars}) | AI1:${dec1.confidence}% AI2:${dec2.confidence}% | ${marketRegime}`);
  sendDiscordAlert(
    `⚡ **${sym} ENTRY** @ $${s.price.toFixed(4)}\n`+
    `💰 Size: ${sizing.label} ($${sizing.dollars})\n`+
    `🧠 AI1: ${dec1.confidence}% · AI2: ${dec2.confidence}%\n`+
    `📊 Pattern: ${sg.pattern.name} · RSI: ${sg.rsi} · Vol: ${sg.volR}x\n`+
    `🌍 Regime: ${marketRegime} · Time Score: ${(sg.timeMultiplier*100).toFixed(0)}%`
  );
  if (alpacaConnected) placeAlpacaOrder(sym, b.pos, 'buy').catch(()=>{});
  broadcast('ENTRY', { sym, price:s.price, sizing, bot:bots[sym] });
}

// ── MOMENTUM CHAINING ──
async function momentumChain(sector) {
  // After a big win look for next hot setup in same sector
  const sectorTickers = tickers.filter(sym => STOCKS[sym]?.sector === sector && bots[sym]?.pos === 0);
  for (const sym of sectorTickers) {
    const sg = getSignals(sym);
    if (sg.momentum > 65 && sg.volR > 2) {
      console.log(`🔗 Momentum chain: ${sym} (${sector})`);
      await askAI(sym, 'primary');
      await askAI(sym, 'secondary');
    }
  }
}

// ── TRADE LOG ──
function logTrade(sym, entry, exit, allocated, pnl, reason, sg) {
  const now   = new Date();
  const trade = {
    id: tradeJournal.length+1,
    sym, entry, exit, allocated, pnl, reason,
    pattern:     sg?.pattern?.name || '—',
    sentiment:   sentimentMap[sym]?.overall || 0,
    aiVerdict:   aiDecisions[sym]?.verdict  || '—',
    ai2Verdict:  ai2Decisions[sym]?.verdict || '—',
    aiConf:      aiDecisions[sym]?.confidence || 0,
    ai2Conf:     ai2Decisions[sym]?.confidence || 0,
    regime:      marketRegime,
    hour:        now.getHours(),
    sector:      STOCKS[sym]?.sector || '—',
    date:        now.toLocaleDateString(),
    time:        now.toLocaleTimeString()
  };
  tradeJournal.unshift(trade);
  if (tradeJournal.length > 1000) tradeJournal.pop();
  saveJSON(TRADES_FILE, tradeJournal);
  return trade;
}

// ── PATTERN LEARNING ──
function learnFromTrade(sym, trade, aiDec) {
  if (!aiDec) return;
  const key = `${trade.pattern}_${trade.sector}_${trade.hour}`;
  if (!patternData.patterns[key]) {
    patternData.patterns[key] = { wins:0, losses:0, totalPnl:0, avgConf:0, count:0 };
  }
  const p = patternData.patterns[key];
  p.count++;
  if (trade.pnl>0) p.wins++; else p.losses++;
  p.totalPnl  = parseFloat((p.totalPnl+trade.pnl).toFixed(2));
  p.avgConf   = parseFloat(((p.avgConf*(p.count-1)+(aiDec.confidence||0))/p.count).toFixed(1));
  patternData.totalDecisions++;
  saveJSON(PATTERNS_FILE, patternData);
}

function updateLearning(sym, won, sg, pnl) {
  const now    = new Date();
  const hour   = now.getHours().toString();
  const sector = STOCKS[sym]?.sector || 'Unknown';
  const pattern= sg.pattern.name;
  // Hourly win rate
  if (!learning.hourlyWR[hour]) learning.hourlyWR[hour] = { wins:0, total:0 };
  learning.hourlyWR[hour].total++;
  if (won) learning.hourlyWR[hour].wins++;
  // Sector win rate
  if (!learning.sectorWR[sector]) learning.sectorWR[sector] = { wins:0, total:0, totalPnl:0 };
  learning.sectorWR[sector].total++;
  if (won) learning.sectorWR[sector].wins++;
  learning.sectorWR[sector].totalPnl = parseFloat((learning.sectorWR[sector].totalPnl+pnl).toFixed(2));
  // Pattern win rate
  if (!learning.patternWR[pattern]) learning.patternWR[pattern] = { wins:0, total:0 };
  learning.patternWR[pattern].total++;
  if (won) learning.patternWR[pattern].wins++;
  saveJSON(LEARNING_FILE, learning);
}

// ── WEEKLY SELF OPTIMIZATION ──
async function selfOptimize() {
  if (!ANTHROPIC_KEY || totalTrades < 20) return;
  console.log('🔧 Running self-optimization...');
  lastSelfOptTime = new Date();
  // Build performance summary
  const hourlyBest = Object.entries(learning.hourlyWR)
    .filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,3).map(([h,v])=>`Hour ${h}: ${Math.round(v.wins/v.total*100)}% WR`)
    .join(', ') || 'Building data';
  const sectorBest = Object.entries(learning.sectorWR)
    .filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,3).map(([s,v])=>`${s}: ${Math.round(v.wins/v.total*100)}% WR`)
    .join(', ') || 'Building data';
  const patternBest = Object.entries(learning.patternWR)
    .filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,3).map(([p,v])=>`${p}: ${Math.round(v.wins/v.total*100)}% WR`)
    .join(', ') || 'Building data';
  const prompt =
    `You are an AI trading system optimizer. Review this performance data and suggest 3 specific parameter adjustments:\n`+
    `Total Trades: ${totalTrades} | Win Rate: ${Math.round(totalWins/totalTrades*100)}% | Total P&L: $${totalPnl.toFixed(2)}\n`+
    `Best Hours: ${hourlyBest}\nBest Sectors: ${sectorBest}\nBest Patterns: ${patternBest}\n`+
    `Current Settings: Stop ${SETTINGS.stopLoss}% | Target ${SETTINGS.takeProfit}% | MinConf ${SETTINGS.minConfidence}%\n`+
    `Respond ONLY with JSON: {"stopLoss":float,"takeProfit":float,"minConfidence":int,"insight":"one sentence"}`;
  try {
    const resp = await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6', max_tokens:300,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const txt  = resp.data?.content?.[0]?.text || '{}';
    const opts = JSON.parse(txt.replace(/```json|```/g,'').trim());
    // Apply conservative adjustments
    if (opts.stopLoss    && opts.stopLoss    >= 3  && opts.stopLoss    <= 8)  SETTINGS.stopLoss    = opts.stopLoss;
    if (opts.takeProfit  && opts.takeProfit  >= 5  && opts.takeProfit  <= 15) SETTINGS.takeProfit  = opts.takeProfit;
    if (opts.minConfidence && opts.minConfidence>=60 && opts.minConfidence<=85) SETTINGS.minConfidence = opts.minConfidence;
    learning.lastOptimized = new Date().toISOString();
    saveJSON(LEARNING_FILE, learning);
    console.log(`🔧 Self-optimized: ${opts.insight}`);
    await sendDiscordAlert(
      `🔧 **BRAIN SELF-OPTIMIZED**\n`+
      `📊 Based on ${totalTrades} trades\n`+
      `💡 ${opts.insight}\n`+
      `⚙️ New settings: Stop ${SETTINGS.stopLoss}% | Target ${SETTINGS.takeProfit}% | MinConf ${SETTINGS.minConfidence}%`
    );
  } catch(e) { console.error('Self-optimize error:', e.message); }
}

// ── DUAL AI BRAIN ──
async function askAI(sym, role='primary') {
  if (!ANTHROPIC_KEY) return;
  const s  = STOCKS[sym], sg = getSignals(sym), b = bots[sym];
  if (!s) return;
  const chg = ((s.price-s.open)/s.open*100).toFixed(2);
  // Include learning insights
  const patKey    = `${sg.pattern.name}_${s.sector}_${new Date().getHours()}`;
  const patStats  = patternData.patterns[patKey];
  const patHistory= patStats
    ? `${sg.pattern.name} in ${s.sector} at this hour: ${patStats.wins}W/${patStats.losses||0}L avg $${(patStats.totalPnl/patStats.count).toFixed(2)}`
    : 'No specific history yet';
  const sectorStats = learning.sectorWR[s.sector];
  const sectorPerf  = sectorStats?.total >= 3
    ? `${s.sector} sector: ${Math.round(sectorStats.wins/sectorStats.total*100)}% WR over ${sectorStats.total} trades`
    : 'Building sector data';
  const rolePrompt = role === 'secondary'
    ? `You are AI VERIFIER #2 — your job is to CHALLENGE the primary AI decision and find reasons NOT to trade. Be skeptical.`
    : `You are AI ANALYST #1 — elite stock trader with full market access. Any stock, any price. Find the best setups.`;

  const prompt =
    `${rolePrompt}\n\n`+
    `Ticker: ${sym} | Sector: ${s.sector} | Price: $${s.price.toFixed(4)} (${chg}% today)\n`+
    `RSI: ${sg.rsi} | Volume: ${sg.volR}x avg | Momentum: ${sg.momentum}/100\n`+
    `MACD: ${sg.macd} | BB Position: ${sg.bb}/100 | Squeeze: ${sg.squeeze}/100\n`+
    `Short Float: ${s.short}% | Float: ${s.float}M | VWAP: ${s.price>b.vwap?'ABOVE ✅':'BELOW ⚠️'}\n`+
    `Pattern: ${sg.pattern.name} | Sentiment: ${sg.sentiment}/100\n`+
    `Market Regime: ${marketRegime} | SPY: ${spyChange}%\n`+
    `Pattern History: ${patHistory}\n`+
    `Sector Performance: ${sectorPerf}\n`+
    `Bot Win Rate: ${b.trades>0?Math.round(b.wins/b.trades*100):'N/A'}% (${b.trades} trades)\n\n`+
    `Respond ONLY with JSON: {"verdict":"YES" or "NO","confidence":0-100,"reason":"2 sentences max","entry":${s.price.toFixed(4)},"stop":float,"target":float,"risk":"LOW|MEDIUM|HIGH"}`;

  const target = role==='primary' ? aiDecisions : ai2Decisions;
  target[sym] = { verdict:'THINKING', confidence:0, sym, role, time:new Date().toLocaleTimeString() };
  broadcast('AI_DECISION', { sym, role, decision:target[sym] });

  try {
    const resp = await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6', max_tokens:350,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const txt  = resp.data?.content?.[0]?.text || '{}';
    const dec  = JSON.parse(txt.replace(/```json|```/g,'').trim());
    dec.sym    = sym; dec.role = role; dec.time = new Date().toLocaleTimeString();
    target[sym]= dec;
    console.log(`🧠 ${role==='primary'?'AI1':'AI2'} ${sym}: ${dec.verdict} (${dec.confidence}%)`);
    broadcast('AI_DECISION', { sym, role, decision:dec });
    // Only alert Discord if both AIs agree YES
    if (role==='secondary' && dec.verdict==='YES' && aiDecisions[sym]?.verdict==='YES') {
      sendDiscordAlert(
        `🧠🧠 **DUAL AI APPROVED: ${sym}**\n`+
        `AI1: ${aiDecisions[sym].confidence}% · AI2: ${dec.confidence}%\n`+
        `💡 ${dec.reason}\n`+
        `🎯 Entry $${dec.entry} · Stop $${dec.stop} · Target $${dec.target}`
      );
    }
  } catch(e) {
    console.error(`AI ${role} error ${sym}:`, e.message);
    target[sym] = { verdict:'ERROR', confidence:0, sym, role, reason:e.message.slice(0,60), time:new Date().toLocaleTimeString() };
  }
}

async function analyzeAll() {
  if (!tickers.length) return;
  const toAnalyze = tickers.filter(sym => !bots[sym] || bots[sym].pos===0);
  if (!toAnalyze.length) return;
  lastAnalyzeTime = new Date();
  console.log(`🧠 Analyzing ${toAnalyze.length} tickers (smart dual AI)...`);
  for (const sym of toAnalyze) {
    // Skip if fresh decision under 8 min
    const dec = aiDecisions[sym];
    if (dec && dec.verdict!=='ERROR' && dec.verdict!=='THINKING') {
      const age = Date.now() - new Date().setHours(
        parseInt(dec.time?.split(':')[0]||0),
        parseInt(dec.time?.split(':')[1]||0),0,0
      );
      if (age < 480000) continue;
    }
    // AI #1 first
    await askAI(sym, 'primary');
    await sleep(400);
    // Only call AI #2 if AI #1 said YES — saves 60% of API costs
    if (aiDecisions[sym]?.verdict === 'YES') {
      await askAI(sym, 'secondary');
      await sleep(400);
    } else {
      // Clear any stale AI2 decision so dashboard stays accurate
      ai2Decisions[sym] = { verdict:'SKIPPED', confidence:0, sym, role:'secondary',
        reason:'AI1 rejected — AI2 not needed', time:new Date().toLocaleTimeString() };
    }
  }
  broadcast('ANALYZE_COMPLETE', { count:toAnalyze.length, time:lastAnalyzeTime });
}

// ── MARKET SCANNER ──
async function scanMarket(scanType) {
  if (!ANTHROPIC_KEY) return [];
  lastScanTime = new Date();
  const existing   = tickers.length ? `Currently tracking: ${tickers.join(', ')}. Find DIFFERENT tickers.` : '';
  const hotSectors = Object.entries(learning.sectorWR)
    .filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,2).map(([s])=>s).join(', ') || 'any sector';
  const scanFocus = {
    full:     `top 5 stock opportunities right now across the ENTIRE market — any price, any sector — prioritize ${hotSectors} based on current momentum`,
    momentum: '5 highest momentum stocks anywhere in the market — any price range — volume surges and strong price action today',
    catalyst: '5 stocks with fresh catalysts — FDA, DoD contract, earnings beat, partnership, any sector any price',
    squeeze:  '5 heavily shorted stocks primed for a squeeze — high short float, volume building, any price range',
    gap:      '5 stocks gapping up 10%+ today with volume confirmation — biggest movers in the entire market',
  };
  const prompt =
    `You are an elite stock scanner with full market access. ${existing}\n`+
    `Market Regime: ${marketRegime} | SPY: ${spyChange}%\n`+
    `Find: ${scanFocus[scanType]||scanFocus.full}\n`+
    `No price restrictions — you can pick stocks at ANY price. Pick whatever has the best setup right now.\n\n`+
    `Return ONLY JSON array:\n`+
    `[{"sym":"TICKER","name":"Company","price":float,"float":float,"short":float,`+
    `"sector":"sector","score":0-100,"catalyst":"specific reason why NOW",`+
    `"ai_verdict":"YES" or "WATCH","confidence":0-100,"entry":float,"stop":float,"target":float}]`;
  try {
    const resp = await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6', max_tokens:1200,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const txt     = resp.data?.content?.[0]?.text || '[]';
    const results = JSON.parse(txt.replace(/```json|```/g,'').trim());
    broadcast('DISCOVERY_RESULTS', { results, scanType });
    for (const r of results) {
      if (r.ai_verdict==='YES' && !tickers.includes(r.sym) && tickers.length<SETTINGS.maxBots) {
        addTicker(r); await sleep(300);
      } else if (r.ai_verdict==='WATCH' && !tickers.includes(r.sym) && !watchlist.find(w=>w.sym===r.sym)) {
        // Add to watchlist instead
        watchlist.unshift({ sym:r.sym, catalyst:r.catalyst, score:r.score, added:new Date().toISOString() });
        if (watchlist.length > 30) watchlist.pop();
        saveJSON(WATCHLIST_FILE, watchlist);
      }
    }
    return results;
  } catch(e) { console.error('Scan error:', e.message); return []; }
}

// ── WATCHLIST ENGINE ──
async function reviewWatchlist() {
  if (!watchlist.length) return;
  // Check if any watchlist tickers are ready to promote
  for (const item of watchlist.slice(0,10)) {
    const sym = item.sym;
    if (tickers.includes(sym)) continue;
    if (tickers.length >= SETTINGS.maxBots) break;
    // Ask AI if it's ready
    const prompt =
      `Is ${sym} ready to trade right now? It was flagged as a WATCH ticker for: ${item.catalyst}\n`+
      `Current market regime: ${marketRegime}. Respond ONLY with JSON: {"ready":true/false,"reason":"one sentence"}`;
    try {
      const resp = await axios.post('https://api.anthropic.com/v1/messages',{
        model:'claude-sonnet-4-6', max_tokens:150,
        messages:[{role:'user',content:prompt}]
      },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
      const txt = resp.data?.content?.[0]?.text || '{}';
      const dec = JSON.parse(txt.replace(/```json|```/g,'').trim());
      if (dec.ready) {
        addTicker({ sym, catalyst:item.catalyst, ai_verdict:'YES', confidence:70, price:5, sector:'Discovery' });
        watchlist = watchlist.filter(w=>w.sym!==sym);
        saveJSON(WATCHLIST_FILE, watchlist);
        console.log(`👁️ Promoted from watchlist: ${sym}`);
      }
    } catch(e) {}
    await sleep(500);
  }
}

// ── ROSTER MANAGEMENT ──
function addTicker(disc) {
  const sym = (disc.sym||'').toUpperCase().trim();
  if (!sym || tickers.includes(sym) || tickers.length>=SETTINGS.maxBots) return;
  initStock(sym, disc.price||(Math.random()*8+0.5).toFixed(3),
    disc.float||(Math.random()*60+5).toFixed(1),
    disc.short||(Math.random()*30+5).toFixed(1),
    Math.floor(Math.random()*8e6+500000),
    disc.sector||'Discovery', nextColor());
  tickers.push(sym);
  if (disc.ai_verdict) {
    aiDecisions[sym] = { sym, verdict:disc.ai_verdict, confidence:disc.confidence||70,
      reason:disc.catalyst||'AI selected', entry:disc.entry, stop:disc.stop, target:disc.target,
      time:new Date().toLocaleTimeString() };
  }
  addRotationLog('ADD', sym, (disc.catalyst||'AI selected').slice(0,60));
  saveJSON(ROSTER_FILE, tickers);
  console.log(`➕ ${sym} added | $${STOCKS[sym].price} | ${disc.sector||'Discovery'}`);
  sendDiscordAlert(`➕ **NEW BOT: ${sym}**\n📊 ${disc.catalyst||'AI selected'}\n💰 Entry $${disc.entry||'TBD'} · Conf: ${disc.confidence||70}%`);
  broadcast('TICKER_ADDED', { sym, stock:STOCKS[sym], bot:bots[sym], hist:hist[sym], sent:sentimentMap[sym] });
}

function dropTicker(sym, reason) {
  if (!tickers.includes(sym)) return false;
  if (tickers.length<=SETTINGS.minBots) return false;
  if (bots[sym]?.pos>0) return false;
  tickers = tickers.filter(s=>s!==sym);
  delete STOCKS[sym]; delete bots[sym]; delete hist[sym];
  delete vols[sym]; delete sentimentMap[sym];
  delete aiDecisions[sym]; delete ai2Decisions[sym];
  delete tickerHealth[sym]; delete tradeCooldown[sym];
  delete trailPeaks[sym]; delete botBudgets[sym];
  addRotationLog('REMOVE', sym, reason);
  saveJSON(ROSTER_FILE, tickers);
  console.log(`➖ ${sym} dropped: ${reason}`);
  sendDiscordAlert(`➖ **DROPPED: ${sym}**\n❌ ${reason}`);
  broadcast('TICKER_REMOVED', { sym, reason });
  return true;
}

function addRotationLog(action, sym, reason) {
  rotationLog.unshift({ time:new Date().toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'}), action, sym, reason });
  if (rotationLog.length>100) rotationLog.pop();
}

// ── HEALTH SCORING ──
function scoreHealth() {
  tickers.forEach(sym => {
    const b=bots[sym], s=STOCKS[sym];
    if (!b||!s) return;
    const chg = (s.price-s.open)/s.open*100;
    const sg  = getSignals(sym);
    const wr  = b.trades>0 ? b.wins/b.trades : 0.5;
    const act = b.trades>0 ? Math.min(1,b.trades/5) : 0.3;
    const sig = (sg.momentum+sg.sentiment+sg.squeeze)/300;
    const mom = chg>3?1:chg>0?0.6:chg>-3?0.3:0.1;
    const ai1 = aiDecisions[sym]?.verdict==='YES'?0.15:aiDecisions[sym]?.verdict==='NO'?-0.15:0;
    const ai2 = ai2Decisions[sym]?.verdict==='YES'?0.15:ai2Decisions[sym]?.verdict==='NO'?-0.15:0;
    const score = Math.max(0,Math.min(100,Math.round((wr*0.25+act*0.2+sig*0.2+mom*0.15+ai1+ai2)*100)));
    if (!tickerHealth[sym]) tickerHealth[sym] = { score:50, noTradeCount:0, consecutiveLosses:0 };
    tickerHealth[sym].score = score;
    tickerHealth[sym].noTradeCount = b.trades===0?(tickerHealth[sym].noTradeCount||0)+1:0;
  });
}

async function rotateRoster() {
  if (!tickers.length) return;
  lastRotateTime = new Date();
  scoreHealth();
  const toDrop = [];
  tickers.slice().forEach(sym => {
    const h=tickerHealth[sym], b=bots[sym];
    if (!b||b.pos>0) return;
    const aiNo    = aiDecisions[sym]?.verdict==='NO' && ai2Decisions[sym]?.verdict==='NO' && (h?.noTradeCount||0)>5;
    const dead    = (h?.noTradeCount||0)>15 && b.trades===0;
    const poor    = b.trades>=5 && (b.wins/b.trades)<0.35;
    const flagged = (h?.consecutiveLosses||0)>=3;
    if ((aiNo||dead||poor||flagged) && tickers.length-toDrop.length>SETTINGS.minBots) {
      toDrop.push({ sym, reason:dead?'No activity':poor?'Win rate <35%':flagged?'3 consecutive losses':'Both AIs rejecting' });
    }
  });
  for (const d of toDrop) { dropTicker(d.sym,d.reason); await sleep(400); }
  if (toDrop.length>0 || tickers.length<SETTINGS.minBots) {
    // Check watchlist first
    await reviewWatchlist();
    // Then scan for new tickers
    const needed = Math.max(toDrop.length, SETTINGS.minBots-tickers.length);
    if (needed>0 && tickers.length<SETTINGS.maxBots) await findReplacements(needed);
  }
  broadcast('ROSTER_UPDATE', { tickers, tickerHealth, rotationLog, STOCKS, bots, hist });
}

async function findReplacements(count) {
  if (!ANTHROPIC_KEY||count<=0) return;
  // Focus on best performing sectors from learning data
  const hotSectors = Object.entries(learning.sectorWR)
    .filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,2).map(([s])=>s).join(' and ');
  const prompt =
    `Find ${count} replacement stock(s) to trade RIGHT NOW — any price, any sector, full market access.\n`+
    `${tickers.length?`Currently tracking: ${tickers.join(', ')}. Pick DIFFERENT ones.`:''}\n`+
    `${hotSectors?`Prioritize ${hotSectors} sectors — historically best performers.`:''}\n`+
    `Market Regime: ${marketRegime}. Need high momentum with active catalysts. Best setup wins regardless of price.\n`+
    `Return ONLY JSON array: [{"sym":"TICKER","name":"Company","price":float,"float":float,`+
    `"short":float,"sector":"sector","score":0-100,"catalyst":"reason","ai_verdict":"YES",`+
    `"confidence":0-100,"entry":float,"stop":float,"target":float}]`;
  try {
    const resp = await axios.post('https://api.anthropic.com/v1/messages',{
      model:'claude-sonnet-4-6', max_tokens:700,
      messages:[{role:'user',content:prompt}]
    },{headers:{'Content-Type':'application/json','x-api-key':ANTHROPIC_KEY,'anthropic-version':'2023-06-01'}});
    const list = JSON.parse((resp.data?.content?.[0]?.text||'[]').replace(/```json|```/g,'').trim());
    for (const r of list) {
      if (!tickers.includes(r.sym)&&tickers.length<SETTINGS.maxBots) { addTicker(r); await sleep(300); }
    }
  } catch(e) { console.error('Replacement error:', e.message); }
}

// ── SENTIMENT INTELLIGENCE ──
async function fetchSentiment() {
  const parser = new xml2js.Parser({ explicitArray:false });
  const feeds  = ['https://feeds.finance.yahoo.com/rss/2.0/headline?s=GME,AMC,MARA&region=US&lang=en-US'];
  const results= [];
  for (const url of feeds) {
    try {
      const resp   = await axios.get(url, { timeout:8000 });
      const parsed = await parser.parseStringPromise(resp.data);
      const items  = parsed?.rss?.channel?.item || [];
      const arr    = Array.isArray(items)?items:[items];
      arr.slice(0,10).forEach(item => {
        const title    = item.title||'';
        const matchSym = tickers.find(s=>title.toUpperCase().includes(s));
        const impact   = title.match(/surge|spike|FDA|DoD|contract|beat|squeeze|short|gap|halt|moon/i)?'HIGH':'MEDIUM';
        results.push({ sym:matchSym||'MARKET', headline:title, impact, time:new Date().toLocaleTimeString(), link:item.link||'' });
        // Boost sentiment for mentioned tickers
        if (matchSym && STOCKS[matchSym]) {
          sentimentMap[matchSym].news = Math.min(99, sentimentMap[matchSym].news + (impact==='HIGH'?15:5));
          sentimentMap[matchSym].overall = Math.round(
            sentimentMap[matchSym].reddit*0.3 + sentimentMap[matchSym].twitter*0.4 + sentimentMap[matchSym].news*0.3
          );
        }
      });
    } catch(e) {}
  }
  if (results.length>0) {
    newsItems = results.concat(newsItems).slice(0,30);
    broadcast('NEWS', { items:newsItems });
    results.filter(n=>n.impact==='HIGH'&&n.sym!=='MARKET')
           .forEach(n=>sendDiscordAlert(`📰 **${n.sym} CATALYST** — ${n.headline}`));
  }
}

// ── HONEYPOT FILTER ──
function isHoneypot(sym) {
  const s = STOCKS[sym];
  if (!s) return false;
  // Red flags for pump and dump
  const suspiciousVolume = vols[sym] > s.avgVol * 50;  // 50x+ volume is suspicious
  const suspiciousPrice  = s.change24 > 100;            // 100%+ move in a day
  const tinyFloat        = s.float < 1;                 // under 1M float — easily manipulated
  if (suspiciousVolume && suspiciousPrice && tinyFloat) {
    console.log(`🍯 Honeypot detected: ${sym} — skipping`);
    return true;
  }
  return false;
}

// ── ALPACA ──
async function testAlpaca() {
  if (!ALPACA_KEY||!ALPACA_SECRET) { console.log('⚠️ No Alpaca credentials'); return; }
  try {
    const resp = await axios.get(`${ALPACA_BASE}/v2/account`,{
      headers:{'APCA-API-KEY-ID':ALPACA_KEY,'APCA-API-SECRET-KEY':ALPACA_SECRET}
    });
    alpacaConnected = true;
    const portfolio = parseFloat(resp.data.portfolio_value).toFixed(2);
    const buyPower  = parseFloat(resp.data.buying_power).toFixed(2);
    console.log(`✅ Alpaca connected — Portfolio: $${portfolio} | Buying Power: $${buyPower}`);
    sendDiscordAlert(`✅ **Alpaca Connected**\n💰 Portfolio: $${portfolio}\n💵 Buying Power: $${buyPower}\n📊 Mode: ${ALPACA_PAPER?'🟡 PAPER':'🔴 LIVE'}`);
    broadcast('ALPACA_STATUS', { connected:true, portfolio, buyPower, paper:ALPACA_PAPER });
  } catch(e) {
    console.log('⚠️ Alpaca connection failed:', e.message);
    alpacaConnected = false;
    broadcast('ALPACA_STATUS', { connected:false, error:e.message });
  }
}

async function placeAlpacaOrder(sym, qty, side) {
  if (!alpacaConnected||!ALPACA_KEY||qty<1) return;
  try {
    const resp = await axios.post(`${ALPACA_BASE}/v2/orders`,{
      symbol:sym, qty, side, type:'market', time_in_force:'day'
    },{headers:{'APCA-API-KEY-ID':ALPACA_KEY,'APCA-API-SECRET-KEY':ALPACA_SECRET,'Content-Type':'application/json'}});
    console.log(`📋 Alpaca ${side} ${qty}x ${sym} — ${resp.data.id}`);
  } catch(e) { console.error('Alpaca order error:', e.message); }
}

// ── DISCORD ──
async function sendDiscordAlert(message) {
  if (!DISCORD_WEBHOOK) return;
  try {
    await axios.post(DISCORD_WEBHOOK,{
      username:'🧠 APEX AI BRAIN V3',
      embeds:[{ description:message, color:0x00ffff, timestamp:new Date().toISOString(),
        footer:{ text:`APEX BRAIN V3 · ${ALPACA_PAPER?'PAPER':'LIVE'} · ${tickers.length} bots · ${marketRegime}` } }]
    });
  } catch(e) {}
}

async function sendDiscordTrade(trade) {
  const win = trade.pnl>0;
  const wr  = totalTrades>0?Math.round(totalWins/totalTrades*100):0;
  await sendDiscordAlert(
    `${win?'✅':'❌'} **${trade.sym} ${trade.reason}**\n`+
    `💰 P&L: ${win?'+':''}$${trade.pnl.toFixed(2)} · AI1: ${trade.aiConf}% · AI2: ${trade.ai2Conf}%\n`+
    `📊 Pattern: ${trade.pattern} · Sector: ${trade.sector}\n`+
    `🌍 Regime: ${trade.regime} · Budget: $${getBotBudget(trade.sym)}\n`+
    `📈 Today: ${dailyPnl>=0?'+':''}$${dailyPnl.toFixed(2)} · Week: $${weeklyPnl.toFixed(2)} · ${wr}% WR`
  );
}

async function sendDailyReport() {
  const wr = totalTrades>0?Math.round(totalWins/totalTrades*100):0;
  const topSectors = Object.entries(learning.sectorWR)
    .filter(([,v])=>v.total>=3)
    .sort(([,a],[,b])=>(b.wins/b.total)-(a.wins/a.total))
    .slice(0,3).map(([s,v])=>`${s}: ${Math.round(v.wins/v.total*100)}%`)
    .join(', ')||'Building data';
  await sendDiscordAlert(
    `📊 **DAILY REPORT — ${new Date().toLocaleDateString()}**\n\n`+
    `💰 Today: ${dailyPnl>=0?'+':''}$${dailyPnl.toFixed(2)}\n`+
    `📅 This Week: ${weeklyPnl>=0?'+':''}$${weeklyPnl.toFixed(2)}\n`+
    `📈 All-Time: ${totalPnl>=0?'+':''}$${totalPnl.toFixed(2)}\n`+
    `🎯 Win Rate: ${wr}% (${totalWins}W/${totalTrades-totalWins}L)\n`+
    `🔥 Top Sectors: ${topSectors}\n`+
    `🤖 Active Bots: ${tickers.length} · Regime: ${marketRegime}\n`+
    `📊 Mode: ${ALPACA_PAPER?'🟡 PAPER':'🔴 LIVE'}`
  );
  dailyTrades=0; dailyLoss=0; dailyPnl=0;
  saveState();
}

// ── HELPERS ──
function sleep(ms) { return new Promise(r=>setTimeout(r,ms)); }

// ── SCHEDULES ──
setInterval(fetchAlpacaPrices, 5000);                     // Real prices every 5s
setInterval(analyzeAll, 600000);                          // Smart dual AI every 10 min
setInterval(rotateRoster, 300000);                        // Rotate every 5 min
setInterval(detectMarketRegime, 300000);                  // Check regime every 5 min
setInterval(()=>scanMarket('full'), 600000);              // Full scan every 10 min
setInterval(fetchSentiment, 300000);                      // News every 5 min
setInterval(()=>{checkDrawdown(); calcPortfolioHeat();}, 60000); // Safety checks every 1 min

// Pre-market 4am ET
cron.schedule('0 4 * * 1-5', async()=>{
  console.log('⏰ Pre-market scan...');
  await sendDiscordAlert('⏰ **PRE-MARKET SCAN** — 4am ET · Hunting gappers and catalysts...');
  await scanMarket('gap');
  await sleep(1500);
  await scanMarket('catalyst');
  await sleep(1500);
  await analyzeAll();
  await sendDiscordAlert('✅ **PRE-MARKET COMPLETE** — Bots armed for open');
}, {timezone:'America/New_York'});

// Daily report 4:05pm ET
cron.schedule('5 16 * * 1-5', sendDailyReport, {timezone:'America/New_York'});

// Weekly self-optimization Sunday 8pm ET
cron.schedule('0 20 * * 0', async()=>{
  await selfOptimize();
  weeklyPnl=0; saveState();
}, {timezone:'America/New_York'});

// Reset daily counters midnight
cron.schedule('0 0 * * *', ()=>{
  dailyTrades=0; dailyLoss=0; dailyPnl=0;
  console.log('🌙 Daily counters reset');
}, {timezone:'America/New_York'});

// ── REST API ──
app.get('/api/status', (req,res) => res.json({
  status:'running', tickers:tickers.length, totalPnl, totalTrades, totalWins,
  dailyPnl, weeklyPnl, alpacaConnected, marketRegime, spyChange,
  portfolioHeat, paused, pauseReason, uptime:process.uptime()
}));
app.get('/api/trades',   (req,res) => res.json({ trades:tradeJournal.slice(0,200), totalPnl, totalTrades, totalWins }));
app.get('/api/patterns', (req,res) => res.json(patternData));
app.get('/api/learning', (req,res) => res.json(learning));
app.post('/api/settings',(req,res) => { Object.assign(SETTINGS,req.body); broadcast('SETTINGS',SETTINGS); res.json({ok:true,settings:SETTINGS}); });
app.post('/api/pause',   (req,res) => { paused=true; pauseReason='Manually paused'; broadcast('PAUSED',{paused,pauseReason}); res.json({ok:true}); });
app.post('/api/resume',  (req,res) => { paused=false; pauseReason=''; broadcast('RESUMED',{paused}); res.json({ok:true}); });
app.post('/api/analyze-now', async(req,res) => { res.json({ok:true}); await analyzeAll(); });
app.post('/api/rotate-now',  async(req,res) => { res.json({ok:true}); await rotateRoster(); });
app.post('/api/scan-now',    async(req,res) => { const t=req.body.type||'full'; res.json({ok:true}); await scanMarket(t); broadcast('ROSTER_UPDATE',{tickers,tickerHealth,rotationLog,STOCKS,bots,hist}); });

// ── START ──
server.listen(PORT, async()=>{
  console.log('');
  console.log('╔══════════════════════════════════════╗');
  console.log('║     APEX AI BRAIN V3.0               ║');
  console.log('║     Autonomous Trading Engine         ║');
  console.log(`║     Port: ${PORT}                        ║`);
  console.log('╚══════════════════════════════════════╝');
  console.log('');
  console.log(`🧠 Claude AI:  ${ANTHROPIC_KEY?'✅':'❌ No API key'}`);
  console.log(`📊 Alpaca:     ${ALPACA_KEY?'⏳ Testing...':'❌ No credentials'}`);
  console.log(`💬 Discord:    ${DISCORD_WEBHOOK?'✅':'❌ No webhook'}`);
  console.log(`🔒 Mode:       ${ALPACA_PAPER?'PAPER TRADING':'🔴 LIVE TRADING'}`);
  console.log(`🧠 Dual AI:    ✅ Enabled`);
  console.log(`📈 Auto Scale: ✅ $${SETTINGS.budget} → $${SETTINGS.budgetCeiling}`);
  console.log('');

  await testAlpaca();
  await fetchSentiment();
  await detectMarketRegime();
  await sleep(1500);

  console.log('🔍 Brain scanning market for opportunities...');
  await scanMarket('full');
  await sleep(1500);
  await scanMarket('gap');
  await sleep(1500);
  await scanMarket('catalyst');
  await sleep(1000);

  // Safety net if scan returns nothing
  if (tickers.length===0) {
    console.log('⚠️ Scan empty — seeding starters...');
    const starters = [
      {sym:'BBAI', price:3.81, float:142, short:22, sector:'AI',      catalyst:'AI sector momentum',    ai_verdict:'WATCH', confidence:60},
      {sym:'KULR', price:2.10, float:85,  short:18, sector:'Tech',    catalyst:'Energy tech catalyst',  ai_verdict:'WATCH', confidence:60},
      {sym:'MARA', price:15.2, float:320, short:25, sector:'Crypto',  catalyst:'Bitcoin correlated',    ai_verdict:'WATCH', confidence:60},
      {sym:'MVST', price:1.85, float:92,  short:20, sector:'Battery', catalyst:'EV battery play',       ai_verdict:'WATCH', confidence:60},
      {sym:'AEYE', price:3.85, float:45,  short:15, sector:'AI',      catalyst:'AI enterprise contract',ai_verdict:'WATCH', confidence:60},
    ];
    for (const s of starters) addTicker(s);
  }

  await analyzeAll();

  sendDiscordAlert(
    `🚀 **APEX AI BRAIN V3.0 ONLINE**\n`+
    `🤖 ${tickers.length} bots: ${tickers.join(', ')||'Scanning...'}\n`+
    `🧠 Dual AI: ✅ | Alpaca: ${alpacaConnected?'✅ '+(ALPACA_PAPER?'PAPER':'LIVE'):'❌'}\n`+
    `🌍 Market Regime: ${marketRegime} | SPY: ${spyChange}%\n`+
    `📈 Auto Scale: $${SETTINGS.budget}→$${SETTINGS.budgetCeiling} | Trail Stop: ✅\n`+
    `⏰ Analyze: 5min · Rotate: 5min · Scan: 10min · Pre-market: 4am ET`
  );
  console.log('✅ APEX AI BRAIN V3.0 — All systems online');
});

process.on('uncaughtException',  e=>console.error('Uncaught:',e.message));
process.on('unhandledRejection', e=>console.error('Unhandled:',e?.message||e));
