#!/usr/bin/env node
// run-simulations.js
// Offline daily simulation runner for all three chambers (Senate, Governor, House).
// Produces simulation_results.json with:
//   - per-chamber 10k MC control probability + expected D seats (used for odds-over-time)
//   - per-state/district 10k MC win probability (individual race results)
//   - historical daily snapshots appended over time
//
// Run once daily via cron or scheduler:
//   node run-simulations.js
//
// Requires: Node 18+ (global fetch) and the following files in the same directory:
//   polls.json, entries_all.csv, house_district_ratios_filled.csv, state_polls_by_date.csv

const fs = require("fs");
const path = require("path");

/* ========== CONFIG ========== */
const NUM_SIMS = 10000;
const PROB_ERROR_SD_PTS = 7;
const HOUSE_MC_SWING_RANGE_PTS = 7;
const SENATE_MC_SWING_RANGE_PTS = 7;
const WEIGHTS = { gb: 35, polls: 50, ind: 15 };
const GB_WINDOW_POLLS = 24;
const STATE_POLL_WINDOW = 6;

const SEAT_RULES = {
  senate:   { total: 100, majorityLine: 51,  baseR: 31, baseD: 34 },
  governor: { total: 50,  majorityLine: 26,  baseR: 8,  baseD: 6  },
  house:    { total: 435, majorityLine: 218, baseR: 0,  baseD: 0  },
};
const SENATE_CONTROL_RULE = { demAtLeast: 51, repAtLeast: 50 };

const RESULTS_FILE = path.join(__dirname, "simulation_results.json");

/* ========== MATH HELPERS ========== */
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));

function normalizePair(D, R) {
  const d = Number(D), r = Number(R);
  const s = d + r;
  if (!isFinite(s) || s <= 0) return { D: 50, R: 50 };
  return { D: 100 * d / s, R: 100 * r / s };
}

function marginRD(pair) { return pair.R - pair.D; }

function erf(x) {
  const sign = x < 0 ? -1 : 1;
  x = Math.abs(x);
  const a1 = 0.254829592, a2 = -0.284496736, a3 = 1.421413741,
        a4 = -1.453152027, a5 = 1.061405429, p = 0.3275911;
  const t = 1 / (1 + p * x);
  const y = 1 - (((((a5 * t + a4) * t) + a3) * t + a2) * t + a1) * t * Math.exp(-x * x);
  return sign * y;
}

function normalCDF(x) { return 0.5 * (1 + erf(x / Math.SQRT2)); }

function winProbFromMargin(m) {
  const z = m / PROB_ERROR_SD_PTS;
  const pR = clamp(normalCDF(z), 0, 1);
  return { pD: 1 - pR, pR };
}

// Fast win-prob lookup table
const WINP_MIN = -40, WINP_MAX = 40, WINP_STEP = 0.1;
const WINP_N = Math.round((WINP_MAX - WINP_MIN) / WINP_STEP) + 1;
const WINP_PD_TABLE = new Float32Array(WINP_N);
for (let i = 0; i < WINP_N; i++) {
  const m = WINP_MIN + i * WINP_STEP;
  WINP_PD_TABLE[i] = winProbFromMargin(m).pD;
}
function winProbD_fast(m) {
  if (!isFinite(m)) return 0.5;
  const mm = clamp(m, WINP_MIN, WINP_MAX);
  const idx = Math.round((mm - WINP_MIN) / WINP_STEP);
  return WINP_PD_TABLE[idx] ?? 0.5;
}

function median(arr) {
  const a = arr.filter(x => isFinite(x)).slice().sort((x, y) => x - y);
  const n = a.length;
  if (n === 0) return NaN;
  const mid = Math.floor(n / 2);
  return (n % 2 === 1) ? a[mid] : (a[mid - 1] + a[mid]) / 2;
}

function toNum(v) {
  if (v === null || v === undefined) return NaN;
  const s = String(v).trim();
  if (!s) return NaN;
  const n = Number(s);
  return isFinite(n) ? n : NaN;
}

function isoDate(d) {
  const y = d.getFullYear();
  const m = String(d.getMonth() + 1).padStart(2, "0");
  const day = String(d.getDate()).padStart(2, "0");
  return `${y}-${m}-${day}`;
}

function parseDate(s) {
  if (!s) return null;
  const m = String(s).match(/^(\d{4})-(\d{2})-(\d{2})/);
  if (!m) return null;
  return new Date(+m[1], +m[2] - 1, +m[3]);
}

/* ========== CSV PARSER (minimal, no deps) ========== */
function parseCSV(text) {
  const lines = text.split(/\r?\n/);
  if (lines.length < 2) return [];
  const headers = parseCSVLine(lines[0]);
  const rows = [];
  for (let i = 1; i < lines.length; i++) {
    if (!lines[i].trim()) continue;
    const vals = parseCSVLine(lines[i]);
    const obj = {};
    for (let j = 0; j < headers.length; j++) {
      obj[headers[j]] = vals[j] || "";
    }
    rows.push(obj);
  }
  return rows;
}

function parseCSVLine(line) {
  const result = [];
  let current = "";
  let inQuotes = false;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (inQuotes) {
      if (ch === '"') {
        if (i + 1 < line.length && line[i + 1] === '"') {
          current += '"';
          i++;
        } else {
          inQuotes = false;
        }
      } else {
        current += ch;
      }
    } else {
      if (ch === '"') {
        inQuotes = true;
      } else if (ch === ',') {
        result.push(current.trim());
        current = "";
      } else {
        current += ch;
      }
    }
  }
  result.push(current.trim());
  return result;
}

/* ========== POLLSTER ALLOWLIST ========== */
const AP = [
  { pattern: /yougov/ }, { pattern: /verasight/ }, { pattern: /ipsos/ },
  { pattern: /americanresearchgroup|arg\b/ }, { pattern: /tipp/ },
  { pattern: /emerson/ }, { pattern: /gallup/ }, { pattern: /marist/ },
  { pattern: /quinnipiac/ }, { pattern: /apnorc|ap-norc|norc/ },
  { pattern: /marquette/ }, { pattern: /cnnssrs|cnn\/ssrs|ssrs/ },
  { pattern: /atlasintel|atlas/ }, { pattern: /beaconresearch|shaw/ },
  { pattern: /hartresearch|publicopinionstrategies/ }, { pattern: /pewresearch|pew/ },
  { pattern: /surveymonkey/ }, { pattern: /leger/ },
  { pattern: /massachusetts|umass|departmentofpoliticalscience/ },
  { pattern: /siena|newyorktimes/ }, { pattern: /foxnews/ },
  { pattern: /wallstreetjournal|wsj/ },
];

function normPollster(s) {
  return String(s || "").toLowerCase().replace(/&/g, "and").replace(/[^a-z0-9]+/g, "");
}

function isAllowedPollster(pollster) {
  const n = normPollster(pollster);
  if (!n) return false;
  return AP.some(x => x.pattern.test(n));
}

/* ========== DATA LOADING ========== */
const DATA = {
  senate:   { gb: null, ratios: {}, polls: {} },
  governor: { gb: null, ratios: {}, polls: {} },
  house:    { gb: null, ratios: {}, polls: {}, meta: {} },
};

const USPS_TO_NAME = {
  AL:"Alabama",AK:"Alaska",AZ:"Arizona",AR:"Arkansas",CA:"California",CO:"Colorado",CT:"Connecticut",DE:"Delaware",DC:"District of Columbia",
  FL:"Florida",GA:"Georgia",HI:"Hawaii",ID:"Idaho",IL:"Illinois",IN:"Indiana",IA:"Iowa",KS:"Kansas",KY:"Kentucky",LA:"Louisiana",ME:"Maine",
  MD:"Maryland",MA:"Massachusetts",MI:"Michigan",MN:"Minnesota",MS:"Mississippi",MO:"Missouri",MT:"Montana",NE:"Nebraska",NV:"Nevada",NH:"New Hampshire",
  NJ:"New Jersey",NM:"New Mexico",NY:"New York",NC:"North Carolina",ND:"North Dakota",OH:"Ohio",OK:"Oklahoma",OR:"Oregon",PA:"Pennsylvania",RI:"Rhode Island",
  SC:"South Carolina",SD:"South Dakota",TN:"Tennessee",TX:"Texas",UT:"Utah",VT:"Vermont",VA:"Virginia",WA:"Washington",WV:"West Virginia",WI:"Wisconsin",WY:"Wyoming"
};
const NAME_TO_USPS = Object.fromEntries(
  Object.entries(USPS_TO_NAME).map(([usps, name]) => [name.trim().toLowerCase(), usps])
);

function houseDistrictCode(usps, cd) {
  if (!usps) return "";
  if (cd === 0) return `${usps}-AL`;
  return `${usps}-${String(cd).padStart(2, "0")}`;
}

function loadEntriesCSV() {
  const csvPath = path.join(__dirname, "entries_all.csv");
  const text = fs.readFileSync(csvPath, "utf-8");
  const rows = parseCSV(text);

  for (const row of rows) {
    const mode = String(row.mode || "").trim().toLowerCase();
    if (!DATA[mode]) continue;

    const st = String(row.state || "").trim().toUpperCase();
    const ratioD = toNum(row.ratioD);
    const ratioR = toNum(row.ratioR);

    if (st && isFinite(ratioD) && isFinite(ratioR)) {
      DATA[mode].ratios[st] = { D: ratioD, R: ratioR };
    }

    const gbD = toNum(row.gbD);
    const gbR = toNum(row.gbR);
    if (!DATA[mode].gb && isFinite(gbD) && isFinite(gbR)) {
      DATA[mode].gb = normalizePair(gbD, gbR);
    }

    const pollD = toNum(row.pollD);
    const pollR = toNum(row.pollR);
    const pollSigma = toNum(row.pollSigma);
    if (st && isFinite(pollD) && isFinite(pollR)) {
      DATA[mode].polls[st] = { D: pollD, R: pollR, S: isFinite(pollSigma) ? pollSigma : 3 };
    }
  }

  // Cross-fill generic ballot if missing
  if (!DATA.senate.gb && DATA.governor.gb) DATA.senate.gb = DATA.governor.gb;
  if (!DATA.governor.gb && DATA.senate.gb) DATA.governor.gb = DATA.senate.gb;
}

function loadHouseRatios() {
  const csvPath = path.join(__dirname, "house_district_ratios_filled.csv");
  const text = fs.readFileSync(csvPath, "utf-8");
  const rows = parseCSV(text);

  for (const row of rows) {
    // CSV columns: path_id, state_name, congressional_district_number, d_ratio, r_ratio
    const stateName = String(row.state_name || row.stateName || row.state || "").trim();
    const cd = Number(row.congressional_district_number || row.cd || row.district || 0);
    const dRatio = toNum(row.d_ratio || row.ratioD || row.ratio_d || row.D_ratio);
    const rRatio = toNum(row.r_ratio || row.ratioR || row.ratio_r || row.R_ratio);

    let usps = String(row.usps || "").trim().toUpperCase();
    if (!usps || usps.length !== 2) {
      usps = NAME_TO_USPS[stateName.toLowerCase()] || "";
    }

    let did = "";
    if (usps && usps.length === 2) {
      did = houseDistrictCode(usps, isFinite(cd) ? cd : 0);
    }

    if (did && isFinite(dRatio) && isFinite(rRatio)) {
      DATA.house.ratios[did] = { D: dRatio, R: rRatio };
      const uCode = did.split("-")[0];
      const sn = stateName || (USPS_TO_NAME[uCode] || uCode);
      DATA.house.meta[did] = { code: did, name: sn, state: sn, cd: isFinite(cd) ? cd : 0, usps: uCode };
    }
  }

  if (!DATA.house.gb) {
    DATA.house.gb = DATA.senate.gb || DATA.governor.gb || { D: 50, R: 50 };
  }
}

function loadGenericBallotFromPollsJSON() {
  const pollsPath = path.join(__dirname, "polls.json");
  if (!fs.existsSync(pollsPath)) {
    console.warn("polls.json not found, skipping generic ballot load");
    return null;
  }
  const j = JSON.parse(fs.readFileSync(pollsPath, "utf-8"));
  const gbRaw = Array.isArray(j.genericBallot) ? j.genericBallot : [];

  function norm(s) { return String(s || "").trim().toLowerCase().replace(/\s+/g, " "); }
  function getAns(p, keys) {
    if (!p || !Array.isArray(p.answers)) return null;
    const want = keys.map(norm);
    for (const a of p.answers) {
      const c = norm(a.choice || "");
      if (want.includes(c)) return +a.pct;
    }
    for (const a of p.answers) {
      const c = norm(a.choice || "");
      for (const k of want) {
        if (c === k || c.includes(k)) return +a.pct;
      }
    }
    return null;
  }

  const gbPollsRaw = gbRaw.map(p => {
    const date = parseDate(p.end_date || p.start_date || p.created_at);
    const dem = getAns(p, ["dem", "democrat", "democrats", "democratic"]);
    const rep = getAns(p, ["rep", "republican", "republicans", "gop"]);
    const pollster = p.pollster || p.pollster_name || p.pollsterName || p.sponsor || p.firm || p.source || "";
    return { date, dem, rep, pollster };
  }).filter(p => p.date && isFinite(p.dem) && isFinite(p.rep));

  // Filter by strict allowlist
  const gbPolls = gbPollsRaw.filter(p => isAllowedPollster(p.pollster))
    .sort((a, b) => a.date - b.date);

  // Build last-N polls series
  const series = calcLastNPollsSeries(gbPolls, GB_WINDOW_POLLS);
  series.sort((a, b) => a.date.localeCompare(b.date));

  if (series.length) {
    const latest = series[series.length - 1];
    const pair = normalizePair(latest.dem, latest.rep);
    DATA.house.gb = pair;
    DATA.senate.gb = pair;
    DATA.governor.gb = pair;
  }

  return series;
}

function calcLastNPollsSeries(gbPolls, N) {
  const polls = (gbPolls || []).filter(p => p && p.date instanceof Date && isFinite(p.dem) && isFinite(p.rep))
    .slice().sort((a, b) => a.date - b.date);
  if (!polls.length) return [];
  const n = polls.length;

  const dates = new Array(n);
  const psD = new Float64Array(n + 1);
  const psR = new Float64Array(n + 1);

  for (let i = 0; i < n; i++) {
    dates[i] = polls[i].date;
    psD[i + 1] = psD[i] + polls[i].dem;
    psR[i + 1] = psR[i] + polls[i].rep;
  }

  const t0 = new Date(dates[0]);
  const lastPollDay = new Date(dates[n - 1]);
  const today = new Date(); today.setHours(0, 0, 0, 0);
  const t1 = (today > lastPollDay) ? new Date(today) : lastPollDay;
  const out = [];
  let hi = 0;

  for (let day = new Date(t0); day <= t1; day.setDate(day.getDate() + 1)) {
    while (hi < n && dates[hi] <= day) hi++;
    const lo = Math.max(0, hi - N);
    const cnt = hi - lo;
    if (cnt <= 0) continue;
    const meanD = (psD[hi] - psD[lo]) / cnt;
    const meanR = (psR[hi] - psR[lo]) / cnt;
    out.push({ date: isoDate(day), dem: meanD, rep: meanR, count: cnt });
  }
  return out;
}

/* State polls by date */
const STATE_POLL_DATA = { senate: {}, governor: {}, house: {} };

function loadStatePollsByDate() {
  const csvPath = path.join(__dirname, "state_polls_by_date.csv");
  if (!fs.existsSync(csvPath)) return;
  const text = fs.readFileSync(csvPath, "utf-8");
  const rows = parseCSV(text);

  function normMode(x) {
    const v = String(x || "").trim().toLowerCase();
    if (!v) return "";
    if (v === "sen" || v === "senate" || v.includes("senate")) return "senate";
    if (v === "gov" || v === "governor" || v.includes("governor")) return "governor";
    if (v === "house" || v === "us house" || v.includes("house")) return "house";
    const u = v.toUpperCase();
    if (u.includes("SEN")) return "senate";
    if (u.includes("GOV")) return "governor";
    if (u.includes("HOUSE")) return "house";
    return "";
  }

  function pickDR(r) {
    const aP = String(r.candA_party || r.partyA || "").trim().toUpperCase();
    const bP = String(r.candB_party || r.partyB || "").trim().toUpperCase();
    const aPct = Number(r.candA_pct ?? r.candAPct ?? r.candA ?? NaN);
    const bPct = Number(r.candB_pct ?? r.candBPct ?? r.candB ?? NaN);
    if (!isFinite(aPct) || !isFinite(bPct)) return { D: NaN, R: NaN };
    let D = NaN, R = NaN;
    if (aP === "D") D = aPct; if (bP === "D") D = bPct;
    if (aP === "R") R = aPct; if (bP === "R") R = bPct;
    return { D, R };
  }

  for (const r of rows) {
    const mode = normMode(r.race || r.office || r.mode || r.type || "");
    if (!mode || !STATE_POLL_DATA[mode]) continue;

    const st = String(r.state || "").trim().toUpperCase();
    if (!st) continue;

    const dateStr = r.end_date || r.date || "";
    const date = parseDate(dateStr);
    if (!date) continue;

    let D = toNum(r.dem || r.D || r.pollD);
    let R = toNum(r.rep || r.R || r.pollR);

    if (!isFinite(D) || !isFinite(R)) {
      const dr = pickDR(r);
      D = dr.D; R = dr.R;
    }
    if (!isFinite(D) || !isFinite(R)) continue;

    const sigma = toNum(r.sigma) || 3;

    if (!STATE_POLL_DATA[mode][st]) STATE_POLL_DATA[mode][st] = [];
    STATE_POLL_DATA[mode][st].push({ date, D, R, sigma });
  }

  // Sort each state's polls by date
  for (const mode of ["senate", "governor", "house"]) {
    for (const st of Object.keys(STATE_POLL_DATA[mode])) {
      STATE_POLL_DATA[mode][st].sort((a, b) => a.date - b.date);
    }
  }
}

function applyLatestStatePollsToData() {
  for (const mode of ["senate", "governor"]) {
    for (const st of Object.keys(STATE_POLL_DATA[mode])) {
      const polls = STATE_POLL_DATA[mode][st];
      if (!polls || !polls.length) continue;
      const window = Math.min(STATE_POLL_WINDOW, polls.length);
      const recent = polls.slice(-window);
      const meanD = recent.reduce((s, p) => s + p.D, 0) / recent.length;
      const meanR = recent.reduce((s, p) => s + p.R, 0) / recent.length;
      const meanS = recent.reduce((s, p) => s + (p.sigma || 3), 0) / recent.length;
      DATA[mode].polls[st] = { D: meanD, R: meanR, S: meanS };
    }
  }
}

/* ========== MODEL COMPUTATION ========== */
function computeGenericBallotState(gb, ratio) {
  return normalizePair(gb.D * ratio.D, gb.R * ratio.R);
}

function computePollState(poll) {
  if (!poll) return null;
  const D = Number(poll.D), R = Number(poll.R);
  if (!isFinite(D) || !isFinite(R) || (D + R) <= 0) return null;
  return normalizePair(D, R);
}

function computeIndicatorNationalFromPolls(modeKey) {
  const ratios = DATA[modeKey].ratios;
  const polls = DATA[modeKey].polls;
  const implied = [];
  for (const st of Object.keys(ratios)) {
    const p = computePollState(polls[st]);
    if (!p) continue;
    const r = ratios[st];
    implied.push({ D: p.D / r.D, R: p.R / r.R });
  }
  if (implied.length === 0) return null;
  const medD = median(implied.map(x => x.D));
  const medR = median(implied.map(x => x.R));
  return normalizePair(medD, medR);
}

function computeIndicatorState(indNat, ratio) {
  return normalizePair(indNat.D * ratio.D, indNat.R * ratio.R);
}

function weightedCombine(components) {
  let W = 0, D = 0, R = 0;
  for (const c of components) {
    if (!c || !c.pair || !isFinite(c.w) || c.w <= 0) continue;
    W += c.w;
    D += c.w * c.pair.D;
    R += c.w * c.pair.R;
  }
  if (W <= 0) return { D: 50, R: 50 };
  return normalizePair(D / W, R / W);
}

function getStateModel(modeKey, st, cachedIndNat) {
  const gb = DATA[modeKey].gb || { D: 50, R: 50 };
  const ratio = DATA[modeKey].ratios[st];
  if (!ratio) return null;

  const gbPair = computeGenericBallotState(gb, ratio);
  const pollRaw = DATA[modeKey].polls[st];
  const pollPair = computePollState(pollRaw);
  const indPair = cachedIndNat ? computeIndicatorState(cachedIndNat, ratio) : null;

  const comps = [
    { pair: gbPair,   w: WEIGHTS.gb },
    { pair: pollPair, w: pollPair ? WEIGHTS.polls : 0 },
    { pair: indPair,  w: indPair ? WEIGHTS.ind : 0 },
  ];
  const combinedPair = weightedCombine(comps);
  const mFinal = marginRD(combinedPair);
  const winProb = winProbFromMargin(mFinal);
  return { combinedPair, winProb };
}

function getHouseModel(did) {
  const gb = DATA.house.gb || DATA.senate.gb || DATA.governor.gb || { D: 50, R: 50 };
  const ratio = DATA.house.ratios[did];
  if (!ratio) return null;
  const combinedPair = computeGenericBallotState(gb, ratio);
  const mFinal = marginRD(combinedPair);
  const winProb = winProbFromMargin(mFinal);
  return { combinedPair, winProb };
}

/* ========== MONTE CARLO SIMULATIONS ========== */

// House: 10k sims, national swing model
function runHouseSimulation() {
  const rules = SEAT_RULES.house;
  const ratioKeys = Object.keys(DATA.house.ratios || {}).sort();
  const upSeats = rules.total - rules.baseD - rules.baseR;

  // Precompute baseline margins
  const margins = new Float32Array(upSeats);
  let n = 0;
  for (let i = 0; i < ratioKeys.length && n < upSeats; i++) {
    const model = getHouseModel(ratioKeys[i]);
    if (!model) continue;
    margins[n++] = isFinite(marginRD(model.combinedPair)) ? marginRD(model.combinedPair) : 0;
  }
  for (; n < upSeats; n++) margins[n] = 0;

  let demControl = 0;
  const seatSamples = new Int16Array(NUM_SIMS);
  // Per-district win counts
  const districtDemWins = new Int32Array(upSeats);

  for (let s = 0; s < NUM_SIMS; s++) {
    const swing = (Math.random() * 2 - 1) * HOUSE_MC_SWING_RANGE_PTS;
    let dSeats = rules.baseD;

    for (let i = 0; i < upSeats; i++) {
      const pD = winProbD_fast(margins[i] + swing);
      if (Math.random() < pD) {
        dSeats++;
        districtDemWins[i]++;
      }
    }

    seatSamples[s] = dSeats;
    if (dSeats >= rules.majorityLine) demControl++;
  }

  // Per-district results
  const perDistrict = {};
  let idx = 0;
  for (let i = 0; i < ratioKeys.length && idx < upSeats; i++) {
    const model = getHouseModel(ratioKeys[i]);
    if (!model) continue;
    perDistrict[ratioKeys[i]] = {
      pDem: +(districtDemWins[idx] / NUM_SIMS).toFixed(4),
      margin: +marginRD(model.combinedPair).toFixed(2),
    };
    idx++;
  }

  // Seat distribution histogram (binned by 12, offset 2 like original)
  const seatDist = buildSeatHistogram(seatSamples, "house");

  return {
    pDem: +(demControl / NUM_SIMS).toFixed(4),
    pRep: +((NUM_SIMS - demControl) / NUM_SIMS).toFixed(4),
    expectedDSeats: +(Array.from(seatSamples).reduce((a, b) => a + b, 0) / NUM_SIMS).toFixed(1),
    sims: NUM_SIMS,
    perState: perDistrict,
    seatDistribution: seatDist,
  };
}

// Senate: 10k sims, national swing model
function runSenateSimulation(cachedIndNat) {
  const rules = SEAT_RULES.senate;
  const ratioKeys = Object.keys(DATA.senate.ratios || {}).sort();
  const upSeats = rules.total - rules.baseD - rules.baseR;

  const margins = new Float32Array(upSeats);
  let n = 0;
  for (let i = 0; i < ratioKeys.length && n < upSeats; i++) {
    const model = getStateModel("senate", ratioKeys[i], cachedIndNat);
    if (!model) continue;
    margins[n++] = isFinite(marginRD(model.combinedPair)) ? marginRD(model.combinedPair) : 0;
  }
  for (; n < upSeats; n++) margins[n] = 0;

  let demControl = 0;
  const seatSamples = new Int16Array(NUM_SIMS);
  const stateDemWins = new Int32Array(upSeats);

  for (let s = 0; s < NUM_SIMS; s++) {
    const swing = (Math.random() * 2 - 1) * SENATE_MC_SWING_RANGE_PTS;
    let dSeats = rules.baseD;

    for (let i = 0; i < upSeats; i++) {
      const pD = winProbD_fast(margins[i] + swing);
      if (Math.random() < pD) {
        dSeats++;
        stateDemWins[i]++;
      }
    }

    seatSamples[s] = dSeats;
    if (dSeats >= SENATE_CONTROL_RULE.demAtLeast) demControl++;
  }

  const perState = {};
  let idx = 0;
  for (let i = 0; i < ratioKeys.length && idx < upSeats; i++) {
    const model = getStateModel("senate", ratioKeys[i], cachedIndNat);
    if (!model) continue;
    perState[ratioKeys[i]] = {
      pDem: +(stateDemWins[idx] / NUM_SIMS).toFixed(4),
      margin: +marginRD(model.combinedPair).toFixed(2),
    };
    idx++;
  }

  const seatDist = buildSeatHistogram(seatSamples, "senate");

  return {
    pDem: +(demControl / NUM_SIMS).toFixed(4),
    pRep: +((NUM_SIMS - demControl) / NUM_SIMS).toFixed(4),
    expectedDSeats: +(Array.from(seatSamples).reduce((a, b) => a + b, 0) / NUM_SIMS).toFixed(1),
    sims: NUM_SIMS,
    perState,
    seatDistribution: seatDist,
  };
}

// Governor: 10k sims, national swing model (exact Poisson-binomial for control, MC for per-state)
function runGovernorSimulation(cachedIndNat) {
  const rules = SEAT_RULES.governor;
  const ratioKeys = Object.keys(DATA.governor.ratios || {}).sort();
  const upSeats = rules.total - rules.baseD - rules.baseR;

  const margins = new Float32Array(upSeats);
  let n = 0;
  for (let i = 0; i < ratioKeys.length && n < upSeats; i++) {
    const model = getStateModel("governor", ratioKeys[i], cachedIndNat);
    if (!model) continue;
    margins[n++] = isFinite(marginRD(model.combinedPair)) ? marginRD(model.combinedPair) : 0;
  }
  for (; n < upSeats; n++) margins[n] = 0;

  let demControl = 0;
  const seatSamples = new Int16Array(NUM_SIMS);
  const stateDemWins = new Int32Array(upSeats);

  for (let s = 0; s < NUM_SIMS; s++) {
    const swing = (Math.random() * 2 - 1) * SENATE_MC_SWING_RANGE_PTS;
    let dSeats = rules.baseD;

    for (let i = 0; i < upSeats; i++) {
      const pD = winProbD_fast(margins[i] + swing);
      if (Math.random() < pD) {
        dSeats++;
        stateDemWins[i]++;
      }
    }

    seatSamples[s] = dSeats;
    if (dSeats >= rules.majorityLine) demControl++;
  }

  const perState = {};
  let idx = 0;
  for (let i = 0; i < ratioKeys.length && idx < upSeats; i++) {
    const model = getStateModel("governor", ratioKeys[i], cachedIndNat);
    if (!model) continue;
    perState[ratioKeys[i]] = {
      pDem: +(stateDemWins[idx] / NUM_SIMS).toFixed(4),
      margin: +marginRD(model.combinedPair).toFixed(2),
    };
    idx++;
  }

  const seatDist = buildSeatHistogram(seatSamples, "governor");

  return {
    pDem: +(demControl / NUM_SIMS).toFixed(4),
    pRep: +((NUM_SIMS - demControl) / NUM_SIMS).toFixed(4),
    expectedDSeats: +(Array.from(seatSamples).reduce((a, b) => a + b, 0) / NUM_SIMS).toFixed(1),
    sims: NUM_SIMS,
    perState,
    seatDistribution: seatDist,
  };
}

/* ========== ODDS OVER TIME (daily simulation for historical GB series) ========== */
function runOddsOverTimeHouse(gbSeries) {
  const rules = SEAT_RULES.house;
  const ratioKeys = Object.keys(DATA.house.ratios || {}).sort();
  const seatTotal = rules.total;
  const majorityLine = rules.majorityLine;

  const ratioD = [];
  const ratioR = [];
  for (const k of ratioKeys) {
    const rr = DATA.house.ratios[k];
    ratioD.push((rr && isFinite(rr.D)) ? rr.D : 1);
    ratioR.push((rr && isFinite(rr.R)) ? rr.R : 1);
  }

  const results = [];
  for (let day = 0; day < gbSeries.length; day++) {
    const d0 = +gbSeries[day].dem;
    const r0 = +gbSeries[day].rep;

    // Compute per-seat baseline margins
    const margins = new Float32Array(seatTotal);
    for (let k = 0; k < seatTotal; k++) {
      if (k < ratioD.length) {
        const a = ratioD[k], b = ratioR[k];
        const den = d0 * a + r0 * b;
        margins[k] = den > 0 ? 100 * (r0 * b - d0 * a) / den : 0;
      } else {
        margins[k] = 0;
      }
    }

    // Discrete swing grid for semi-analytic MC
    const swings = [];
    for (let s = -HOUSE_MC_SWING_RANGE_PTS; s <= HOUSE_MC_SWING_RANGE_PTS + 1e-9; s += 0.1) swings.push(s);
    const nSw = swings.length;

    const muBy = new Float32Array(nSw);
    const vaBy = new Float32Array(nSw);
    for (let j = 0; j < nSw; j++) {
      const sw = swings[j];
      let mu = 0, va = 0;
      for (let k = 0; k < seatTotal; k++) {
        const p = winProbD_fast(margins[k] + sw);
        mu += p;
        va += p * (1 - p);
      }
      muBy[j] = mu;
      vaBy[j] = va;
    }

    let demWins = 0, seatSum = 0;
    for (let s = 0; s < NUM_SIMS; s++) {
      const j = (Math.random() * nSw) | 0;
      let seats = muBy[j];
      if (vaBy[j] > 1e-9) {
        // Box-Muller
        let u = 0, v = 0;
        while (u === 0) u = Math.random();
        while (v === 0) v = Math.random();
        seats += Math.sqrt(vaBy[j]) * Math.sqrt(-2.0 * Math.log(u)) * Math.cos(2.0 * Math.PI * v);
      }
      seats = Math.round(seats);
      if (seats < 0) seats = 0;
      if (seats > seatTotal) seats = seatTotal;
      seatSum += seats;
      if (seats >= majorityLine) demWins++;
    }

    results.push({
      date: gbSeries[day].date,
      pDem: +(demWins / NUM_SIMS).toFixed(4),
      expDem: +(seatSum / NUM_SIMS).toFixed(1),
    });

    if (day % 20 === 0) process.stdout.write(`  House odds: ${day + 1}/${gbSeries.length}\r`);
  }
  console.log(`  House odds: ${gbSeries.length}/${gbSeries.length} done`);
  return results;
}

function runOddsOverTimeState(modeKey, gbSeries, cachedIndNat) {
  const rules = SEAT_RULES[modeKey];
  const ratioKeys = Object.keys(DATA[modeKey]?.ratios || {}).sort();
  const n = ratioKeys.length;
  const baseD = rules.baseD;
  const baseR = rules.baseR;
  const total = rules.total;
  const controlLine = (modeKey === "senate") ? SENATE_CONTROL_RULE.demAtLeast : rules.majorityLine;
  const tieIsDem = (modeKey === "governor");
  const tieSeat = rules.majorityLine - 1;
  const swingRange = SENATE_MC_SWING_RANGE_PTS;

  // Precompute static arrays
  const ratioD = new Float32Array(n);
  const ratioR = new Float32Array(n);
  const pollD0 = new Float32Array(n);
  const pollR0 = new Float32Array(n);
  for (let i = 0; i < n; i++) {
    const k = ratioKeys[i];
    const rr = DATA[modeKey].ratios[k];
    ratioD[i] = (rr && isFinite(rr.D)) ? rr.D : 1;
    ratioR[i] = (rr && isFinite(rr.R)) ? rr.R : 1;
    const pp = DATA[modeKey].polls ? DATA[modeKey].polls[k] : null;
    pollD0[i] = (pp && isFinite(pp.D)) ? pp.D : NaN;
    pollR0[i] = (pp && isFinite(pp.R)) ? pp.R : NaN;
  }

  // Build poll matrix for daily rolling window
  const dates = gbSeries.map(d => d.date);
  const pm = buildPollMatrixForDays(modeKey, ratioKeys, dates, STATE_POLL_WINDOW);

  const indD = cachedIndNat ? cachedIndNat.D : NaN;
  const indR = cachedIndNat ? cachedIndNat.R : NaN;
  const wGb = WEIGHTS.gb, wPoll = WEIGHTS.polls, wInd = WEIGHTS.ind;

  const margins = new Float32Array(n);
  const results = [];
  // Per-state MC tracking: for each day, count D wins per state across all sims
  const perStateResults = {};
  for (let i = 0; i < n; i++) perStateResults[ratioKeys[i]] = [];

  for (let day = 0; day < gbSeries.length; day++) {
    const gbd = +gbSeries[day].dem;
    const gbr = +gbSeries[day].rep;

    // Compute per-seat margins
    for (let i = 0; i < n; i++) {
      const gbPair = normalizePair(gbd * ratioD[i], gbr * ratioR[i]);

      let pollPair = null;
      let pDi = NaN, pRi = NaN;
      if (pm) {
        const pd = pm.pollDDay[day * n + i];
        const pr = pm.pollRDay[day * n + i];
        if (isFinite(pd) && isFinite(pr)) { pDi = pd; pRi = pr; }
      }
      if (!isFinite(pDi) || !isFinite(pRi)) {
        pDi = pollD0[i]; pRi = pollR0[i];
      }
      if (isFinite(pDi) && isFinite(pRi)) {
        pollPair = normalizePair(pDi, pRi);
      }

      let indPair = null;
      if (isFinite(indD) && isFinite(indR)) {
        indPair = normalizePair(indD * ratioD[i], indR * ratioR[i]);
      }

      // Weighted combine
      let wd = 0, wr = 0, w = 0;
      if (gbPair && wGb > 0) { wd += wGb * gbPair.D; wr += wGb * gbPair.R; w += wGb; }
      if (pollPair && wPoll > 0) { wd += wPoll * pollPair.D; wr += wPoll * pollPair.R; w += wPoll; }
      if (indPair && wInd > 0) { wd += wInd * indPair.D; wr += wInd * indPair.R; w += wInd; }
      const comb = (w > 0) ? normalizePair(wd / w, wr / w) : { D: 50, R: 50 };
      margins[i] = comb.R - comb.D;
    }

    // MC sims with per-state tracking
    let demControl = 0, sumDSeats = 0;
    const stateDemWins = new Int32Array(n);
    for (let s = 0; s < NUM_SIMS; s++) {
      const swing = (Math.random() * 2 - 1) * swingRange;
      let dWins = 0;
      for (let i = 0; i < n; i++) {
        const pD = winProbD_fast(margins[i] + swing);
        if (Math.random() < pD) {
          dWins++;
          stateDemWins[i]++;
        }
      }
      const dSeats = baseD + dWins;
      sumDSeats += dSeats;
      const isDemCtrl = (dSeats >= controlLine) || (tieIsDem && dSeats === tieSeat);
      if (isDemCtrl) demControl++;
    }

    const dateStr = gbSeries[day].date;
    results.push({
      date: dateStr,
      pDem: +(demControl / NUM_SIMS).toFixed(4),
      expDem: +(sumDSeats / NUM_SIMS).toFixed(1),
    });

    // Record per-state MC pDem for this day
    for (let i = 0; i < n; i++) {
      perStateResults[ratioKeys[i]].push({
        date: dateStr,
        pDem: +(stateDemWins[i] / NUM_SIMS).toFixed(4),
        margin: +margins[i].toFixed(2),
      });
    }

    if (day % 20 === 0) process.stdout.write(`  ${modeKey} odds: ${day + 1}/${gbSeries.length}\r`);
  }
  console.log(`  ${modeKey} odds: ${gbSeries.length}/${gbSeries.length} done (${n} states tracked per day)`);
  return { chamber: results, perState: perStateResults };
}

function buildPollMatrixForDays(modeKey, keys, dateStrs, windowN) {
  const src = STATE_POLL_DATA[modeKey];
  if (!src) return null;

  const nStates = keys.length;
  const nDays = dateStrs.length;

  const pollDDay = new Float32Array(nStates * nDays);
  const pollRDay = new Float32Array(nStates * nDays);
  pollDDay.fill(NaN);
  pollRDay.fill(NaN);

  const windowSize = Math.max(1, windowN | 0);
  const dayDates = dateStrs.map(parseDate);

  for (let i = 0; i < nStates; i++) {
    const k = keys[i];
    const polls = src[k] || null;
    if (!polls || polls.length === 0) continue;

    const m = polls.length;
    const psD = new Float64Array(m + 1);
    const psR = new Float64Array(m + 1);
    for (let j = 0; j < m; j++) {
      psD[j + 1] = psD[j] + polls[j].D;
      psR[j + 1] = psR[j] + polls[j].R;
    }

    let hi = 0;
    for (let day = 0; day < nDays; day++) {
      const dt = dayDates[day];
      if (!dt) continue;
      while (hi < m && polls[hi].date <= dt) hi++;
      const lo = Math.max(0, hi - windowSize);
      const cnt = hi - lo;
      if (cnt <= 0) continue;
      pollDDay[day * nStates + i] = (psD[hi] - psD[lo]) / cnt;
      pollRDay[day * nStates + i] = (psR[hi] - psR[lo]) / cnt;
    }
  }

  return { pollDDay, pollRDay, nStates, nDays };
}

/* ========== SEAT DISTRIBUTION HISTOGRAM ========== */
function buildSeatHistogram(seatSamples, modeKey) {
  // Match the format used by midterm.html for drawSeatSimMini
  const rules = SEAT_RULES[modeKey];
  if (modeKey === "house") {
    // House: binned by 12, offset 2 (matching midterm.html histogramFromSamplesBinned)
    return buildBinnedHistogram(seatSamples, 12, 2);
  } else if (modeKey === "senate") {
    // Senate: full range from baseD to baseD+upSeats (matching midterm.html histogramFromProbDist)
    const upSeats = rules.total - rules.baseD - rules.baseR;
    return buildRangeHistogram(seatSamples, rules.baseD, rules.baseD + upSeats);
  } else {
    // Governor: range 21-31 (matching midterm.html histogramFromProbDistRange)
    return buildRangeHistogram(seatSamples, 21, 31);
  }
}

function buildBinnedHistogram(samples, binSize, binOffset) {
  binSize = Math.max(1, Math.floor(binSize || 1));
  binOffset = Math.floor(binOffset || 0);

  let min = Infinity, max = -Infinity;
  for (let i = 0; i < samples.length; i++) {
    const v = Math.floor(samples[i]);
    if (v < min) min = v;
    if (v > max) max = v;
  }
  if (!isFinite(min) || !isFinite(max)) { min = 0; max = 0; }

  const toBinStart = (v) => Math.floor((v - binOffset) / binSize) * binSize + binOffset;
  const minB = toBinStart(min);
  const maxB = toBinStart(max);
  const n = Math.max(1, Math.floor((maxB - minB) / binSize) + 1);
  const counts = new Array(n).fill(0);
  const total = samples.length || 1;

  for (let i = 0; i < samples.length; i++) {
    const v = Math.floor(samples[i]);
    const b = toBinStart(v);
    const idx = Math.floor((b - minB) / binSize);
    if (idx >= 0 && idx < n) counts[idx]++;
  }

  return { counts, min: minB, max: (minB + (n - 1) * binSize + (binSize - 1)), isProb: false, total, binSize, binOffset };
}

function buildRangeHistogram(samples, showMin, showMax) {
  showMin = Math.floor(showMin);
  showMax = Math.floor(showMax);
  const counts = new Array(showMax - showMin + 1).fill(0);
  const total = samples.length || 1;

  for (let i = 0; i < samples.length; i++) {
    const v = Math.floor(samples[i]);
    if (v < showMin || v > showMax) continue;
    counts[v - showMin]++;
  }
  return { counts, min: showMin, max: showMax, isProb: false, total, binSize: 1 };
}

// House districts: analytical tracking for competitive ones to keep file size manageable
// (Senate/Governor per-state tracking is MC-based, built into runOddsOverTimeState above)
function computeHouseDistrictOddsOverTime(gbSeries) {
  const ratioKeys = Object.keys(DATA.house.ratios || {}).sort();
  if (!ratioKeys.length || !gbSeries.length) return {};

  // Identify competitive districts: check margin at the first, middle, and last GB point.
  // A district that was competitive at ANY point in the GB series gets tracked.
  const checkDays = [0, Math.floor(gbSeries.length / 2), gbSeries.length - 1];
  const competitiveSet = new Set();
  for (const dayIdx of checkDays) {
    const gbNat = normalizePair(+gbSeries[dayIdx].dem, +gbSeries[dayIdx].rep);
    for (const did of ratioKeys) {
      if (competitiveSet.has(did)) continue;
      const ratio = DATA.house.ratios[did];
      if (!ratio) continue;
      const gbPair = computeGenericBallotState(gbNat, ratio);
      if (Math.abs(marginRD(gbPair)) < 15) {
        competitiveSet.add(did);
      }
    }
  }
  const competitive = [];
  for (const did of competitiveSet) {
    competitive.push({ did, ratio: DATA.house.ratios[did] });
  }

  const result = {};
  for (const { did } of competitive) {
    result[did] = [];
  }

  for (let day = 0; day < gbSeries.length; day++) {
    const gbNat = normalizePair(+gbSeries[day].dem, +gbSeries[day].rep);
    const dateStr = gbSeries[day].date;

    for (const { did, ratio } of competitive) {
      const gbPair = computeGenericBallotState(gbNat, ratio);
      const margin = marginRD(gbPair);
      const pDem = winProbFromMargin(margin).pD;

      result[did].push({
        date: dateStr,
        pDem: +pDem.toFixed(4),
        margin: +margin.toFixed(2),
      });
    }

    if (day % 50 === 0) process.stdout.write(`  house district odds: ${day + 1}/${gbSeries.length}\r`);
  }
  console.log(`  house district odds: ${gbSeries.length}/${gbSeries.length} done (${competitive.length} competitive districts)`);
  return result;
}

/* ========== DOWNSAMPLE OPTIMIZATION ========== */
// For states with very little variance (safe seats), downsample to every Nth point
// to reduce JSON size. States with pDem range < 2% get sampled every 7 days,
// states with range < 5% every 3 days. Always keep first and last points.
function downsampleStateOdds(stateOddsMap) {
  const result = {};
  let saved = 0, total = 0;
  for (const [key, arr] of Object.entries(stateOddsMap)) {
    if (!arr || arr.length <= 2) { result[key] = arr; continue; }

    total += arr.length;
    const vals = arr.map(d => d.pDem);
    const mn = Math.min(...vals);
    const mx = Math.max(...vals);
    const range = mx - mn;

    let step;
    if (range < 0.02) step = 7;       // <2% range: weekly
    else if (range < 0.05) step = 3;  // <5% range: every 3 days
    else { result[key] = arr; saved += arr.length; continue; }  // competitive: keep all

    const downsampled = [];
    for (let i = 0; i < arr.length; i++) {
      if (i === 0 || i === arr.length - 1 || i % step === 0) {
        downsampled.push(arr[i]);
      }
    }
    result[key] = downsampled;
    saved += downsampled.length;
  }
  if (total > 0) {
    console.log(`  Downsampled: ${total} → ${saved} points (${((1 - saved/total)*100).toFixed(0)}% reduction)`);
  }
  return result;
}

/* ========== COLUMNAR ENCODING ========== */
// Convert per-state odds from [{date, pDem, margin}, ...] to a columnar format
// with a shared dates array. Reduces JSON size by ~75% by eliminating repeated date strings.
function encodeStateOddsColumnar(stateOddsMap) {
  // Collect all unique dates across all states/districts
  const allDates = new Set();
  for (const [key, arr] of Object.entries(stateOddsMap)) {
    for (const entry of arr) allDates.add(entry.date);
  }
  const dates = [...allDates].sort();
  const dateIndex = Object.fromEntries(dates.map((d, i) => [d, i]));

  // Build columnar representation per state
  const states = {};
  for (const [key, arr] of Object.entries(stateOddsMap)) {
    const indices = [];
    const pDem = [];
    const margin = [];
    for (const entry of arr) {
      indices.push(dateIndex[entry.date]);
      pDem.push(entry.pDem);
      margin.push(entry.margin);
    }

    // Dense (sequential) states: store start index + arrays
    // Sparse (downsampled with gaps): store full index array
    const isDense = indices.length > 0 &&
      indices.length === (indices[indices.length - 1] - indices[0] + 1) &&
      indices.every((v, i) => i === 0 || v === indices[i - 1] + 1);

    if (isDense) {
      states[key] = { s: indices[0], p: pDem, m: margin };
    } else {
      states[key] = { i: indices, p: pDem, m: margin };
    }
  }

  return { dates, states };
}

/* ========== MAIN ========== */
function main() {
  const today = isoDate(new Date());
  console.log(`=== Running simulations for ${today} ===`);

  // Load all data
  console.log("Loading entries_all.csv...");
  loadEntriesCSV();

  console.log("Loading house_district_ratios_filled.csv...");
  loadHouseRatios();

  console.log("Loading polls.json (generic ballot)...");
  const gbSeries = loadGenericBallotFromPollsJSON() || [];
  console.log(`  GB series: ${gbSeries.length} points`);

  console.log("Loading state_polls_by_date.csv...");
  loadStatePollsByDate();
  applyLatestStatePollsToData();

  // Compute indicator caches
  const indSenate = computeIndicatorNationalFromPolls("senate");
  const indGovernor = computeIndicatorNationalFromPolls("governor");

  // Run current-day simulations for each chamber
  console.log("\nRunning Senate simulation (10k sims)...");
  const senateResult = runSenateSimulation(indSenate);
  console.log(`  Senate: D control ${(senateResult.pDem * 100).toFixed(1)}%, E[D seats] ${senateResult.expectedDSeats}`);

  console.log("Running Governor simulation (10k sims)...");
  const governorResult = runGovernorSimulation(indGovernor);
  console.log(`  Governor: D control ${(governorResult.pDem * 100).toFixed(1)}%, E[D seats] ${governorResult.expectedDSeats}`);

  console.log("Running House simulation (10k sims)...");
  const houseResult = runHouseSimulation();
  console.log(`  House: D control ${(houseResult.pDem * 100).toFixed(1)}%, E[D seats] ${houseResult.expectedDSeats}`);

  // Run odds-over-time for each chamber using the full GB series
  // Senate and Governor also track per-state MC results (true 10k sims/state/day)
  console.log("\nRunning chamber + per-state odds over time (all GB series days)...");
  const senateOddsResult = runOddsOverTimeState("senate", gbSeries, indSenate);
  const governorOddsResult = runOddsOverTimeState("governor", gbSeries, indGovernor);
  const houseOdds = runOddsOverTimeHouse(gbSeries);

  // House districts: analytical per-district tracking (competitive only, too many for MC)
  console.log("\nRunning competitive house district odds over time (analytical)...");
  const houseDistrictOdds = computeHouseDistrictOddsOverTime(gbSeries);

  // Load existing results to append daily history
  let existing = { history: [] };
  if (fs.existsSync(RESULTS_FILE)) {
    try {
      existing = JSON.parse(fs.readFileSync(RESULTS_FILE, "utf-8"));
      if (!existing.history) existing.history = [];
    } catch (e) {
      console.warn("Could not parse existing results file, starting fresh.");
      existing = { history: [] };
    }
  }

  // Build today's snapshot
  const snapshot = {
    date: today,
    timestamp: new Date().toISOString(),
    senate: senateResult,
    governor: governorResult,
    house: houseResult,
  };

  // Replace if today already exists, otherwise append
  const existingIdx = existing.history.findIndex(h => h.date === today);
  if (existingIdx >= 0) {
    existing.history[existingIdx] = snapshot;
  } else {
    existing.history.push(snapshot);
  }

  // Sort history by date
  existing.history.sort((a, b) => a.date.localeCompare(b.date));

  // Update odds-over-time (full replacement each run)
  existing.oddsOverTime = {
    senate: senateOddsResult.chamber,
    governor: governorOddsResult.chamber,
    house: houseOdds,
  };

  // Per-state/district odds over time (MC-based for Senate/Gov, analytical for House)
  // Downsample flat/non-competitive states, then encode columnar to save space
  existing.stateOddsOverTime = {
    senate: encodeStateOddsColumnar(downsampleStateOdds(senateOddsResult.perState)),
    governor: encodeStateOddsColumnar(downsampleStateOdds(governorOddsResult.perState)),
    house: encodeStateOddsColumnar(downsampleStateOdds(houseDistrictOdds)),
  };
  existing.stateOddsFormat = "columnar-v1";

  // Add metadata
  existing.lastUpdated = new Date().toISOString();
  existing.lastRunDate = today;
  existing.gbSeriesLength = gbSeries.length;
  existing.simsPerDay = NUM_SIMS;
  existing.gbWindowPolls = GB_WINDOW_POLLS;
  existing.gbFilterStrict = true; // run-simulations.js always uses strict allowlist

  // Write output (compact JSON to minimize file size for browser loading)
  fs.writeFileSync(RESULTS_FILE, JSON.stringify(existing));
  const senateStateCount = Object.keys(senateOddsResult.perState).length;
  const govStateCount = Object.keys(governorOddsResult.perState).length;
  const districtOddsCount = Object.keys(houseDistrictOdds).length;
  console.log(`\nResults saved to ${RESULTS_FILE}`);
  console.log(`  History entries: ${existing.history.length}`);
  console.log(`  Senate states: ${Object.keys(senateResult.perState).length}`);
  console.log(`  Governor states: ${Object.keys(governorResult.perState).length}`);
  console.log(`  House districts: ${Object.keys(houseResult.perState).length}`);
  console.log(`  Per-state MC odds: ${senateStateCount} senate + ${govStateCount} governor (10k sims/state/day)`);
  console.log(`  Competitive house districts (analytical): ${districtOddsCount}`);
  console.log(`  File size: ${(fs.statSync(RESULTS_FILE).size / 1024 / 1024).toFixed(1)} MB`);
  console.log("Done.");
}

main();
