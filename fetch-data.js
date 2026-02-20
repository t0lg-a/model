// fetch-data.js
// Node 18+ (global fetch). If you're on Node <18: npm i node-fetch@3 and import it.

const fs = require("fs");

const API_BASE = "https://api.votehub.com/polls";

// CONFIG
const LOOKBACK_DAYS = 400;
const APPROVAL_SUBJECT = "Donald Trump"; // canonical name per /subjects docs
const SLICE_DAYS = 30;                  // initial chunk size
const MAX_RETRIES = 4;                  // transient retry count
const RETRY_BASE_MS = 750;              // backoff base

function isoDate(d) {
  return d.toISOString().slice(0, 10);
}

function addDays(d, n) {
  const x = new Date(d);
  x.setDate(x.getDate() + n);
  return x;
}

function daysBetween(a, b) {
  const ms = (new Date(b) - new Date(a));
  return Math.floor(ms / (24 * 3600 * 1000));
}

// VoteHub docs emphasize %20. URLSearchParams uses '+' for spaces.
// Some backends are picky; force %20.
function buildQuery(paramsObj) {
  return new URLSearchParams(paramsObj).toString().replace(/\+/g, "%20");
}

function buildUrl(paramsObj) {
  return `${API_BASE}?${buildQuery(paramsObj)}`;
}

function extractList(json) {
  if (Array.isArray(json)) return json;
  if (json && Array.isArray(json.polls)) return json.polls;   // per VoteHub docs
  if (json && Array.isArray(json.results)) return json.results;
  if (json && Array.isArray(json.data)) return json.data;
  return [];
}

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

async function fetchJson(url) {
  let lastErr = null;

  for (let attempt = 1; attempt <= MAX_RETRIES; attempt++) {
    try {
      const res = await fetch(url, {
        headers: {
          Accept: "application/json",
          "User-Agent": "votehub-polls-script/2.0",
        },
      });

      const text = await res.text();

      // Retryable throttling
      if (res.status === 429) {
        const wait = RETRY_BASE_MS * Math.pow(2, attempt - 1);
        console.warn(`429 rate limit. Waiting ${wait}ms then retrying...`);
        await sleep(wait);
        continue;
      }

      if (!res.ok) {
        const err = new Error(
          `HTTP ${res.status} ${res.statusText}\nURL: ${url}\nBody (first 1200):\n${text.slice(0, 1200)}`
        );
        // 5xx can be transient; retry a couple times
        if (res.status >= 500 && attempt < MAX_RETRIES) {
          const wait = RETRY_BASE_MS * Math.pow(2, attempt - 1);
          console.warn(`HTTP ${res.status}. Waiting ${wait}ms then retrying...`);
          await sleep(wait);
          lastErr = err;
          continue;
        }
        throw err;
      }

      try {
        return JSON.parse(text);
      } catch {
        throw new Error(
          `Non-JSON response\nURL: ${url}\nBody (first 1200):\n${text.slice(0, 1200)}`
        );
      }
    } catch (e) {
      lastErr = e;
      if (attempt < MAX_RETRIES) {
        const wait = RETRY_BASE_MS * Math.pow(2, attempt - 1);
        console.warn(`Fetch error. Waiting ${wait}ms then retrying...`);
        await sleep(wait);
      }
    }
  }

  throw lastErr;
}

// Fetch a single slice [from_date, to_date] inclusive via API filters.
async function fetchPollSlice({ poll_type, subject, from_date, to_date }) {
  const params = {
    poll_type,
    from_date,
    to_date,
    sort: "-end_date",
  };
  if (subject) params.subject = subject;

  const url = buildUrl(params);
  const json = await fetchJson(url);
  return extractList(json);
}

// Robust range fetch: try slice; on 500-schema bugs, split until day-level.
// If day-level still fails, skip that day and continue.
async function fetchRangeRobust({ poll_type, subject, from_date, to_date, debug }) {
  const span = daysBetween(from_date, to_date) + 1;

  try {
    const list = await fetchPollSlice({ poll_type, subject, from_date, to_date });
    debug.okSlices++;
    return list;
  } catch (e) {
    const msg = String(e);

    // If it’s not a server failure, don’t pretend we can salvage it.
    // But VoteHub’s current issue is 500. We’ll only split on 5xx.
    const is5xx = msg.includes("HTTP 5") || msg.includes("Internal Server Error");

    if (!is5xx) throw e;

    debug.failedSlices++;

    // If already at day-level, skip
    if (span <= 1) {
      debug.skippedDays.push(from_date);
      console.warn(`Skipping ${from_date} (VoteHub 5xx).`);
      return [];
    }

    // Split range in half
    const mid = isoDate(addDays(new Date(from_date), Math.floor(span / 2) - 1));
    const leftFrom = from_date;
    const leftTo = mid;
    const rightFrom = isoDate(addDays(new Date(mid), 1));
    const rightTo = to_date;

    const left = await fetchRangeRobust({ poll_type, subject, from_date: leftFrom, to_date: leftTo, debug });
    const right = await fetchRangeRobust({ poll_type, subject, from_date: rightFrom, to_date: rightTo, debug });

    return left.concat(right);
  }
}

function dedupeById(polls) {
  const m = new Map();
  for (const p of polls) {
    if (!p || !p.id) continue;
    m.set(p.id, p);
  }
  return Array.from(m.values());
}

async function run() {
  const today = new Date();
  const start = addDays(today, -LOOKBACK_DAYS);

  const data = {
    updatedAt: new Date().toISOString(),
    approval: [],
    genericBallot: [],
    debug: {
      approvalSubject: APPROVAL_SUBJECT,
      lookbackDays: LOOKBACK_DAYS,
      okSlices: 0,
      failedSlices: 0,
      skippedDays: [],
    },
  };

  try {
    // Generic ballot (works fine as you saw)
    console.log("Fetching Generic Ballot...");
    {
      const url = buildUrl({
        poll_type: "generic-ballot",
        from_date: isoDate(start),
        sort: "-end_date",
      });
      const json = await fetchJson(url);
      data.genericBallot = extractList(json);
      console.log(`Generic Ballot: Found ${data.genericBallot.length} polls.`);
    }

    // Approval: fetch in slices to avoid VoteHub’s broken record(s)
    console.log(`Fetching Approval in ${SLICE_DAYS}-day slices for "${APPROVAL_SUBJECT}"...`);

    let all = [];
    for (let d = new Date(start); d <= today; d = addDays(d, SLICE_DAYS)) {
      const from_date = isoDate(d);
      const to_date = isoDate(addDays(d, SLICE_DAYS - 1) > today ? today : addDays(d, SLICE_DAYS - 1));

      process.stdout.write(`  Slice ${from_date} → ${to_date} ... `);

      const slicePolls = await fetchRangeRobust({
        poll_type: "approval",
        subject: APPROVAL_SUBJECT,
        from_date,
        to_date,
        debug: data.debug,
      });

      all = all.concat(slicePolls);
      console.log(`+${slicePolls.length}`);
    }

    data.approval = dedupeById(all).sort((a, b) => String(b.end_date).localeCompare(String(a.end_date)));
    console.log(`Approval: Found ${data.approval.length} polls (after dedupe).`);

    fs.writeFileSync("polls.json", JSON.stringify(data, null, 2));
    console.log("Done. Data saved to polls.json");

    if (data.debug.skippedDays.length) {
      console.warn(`WARNING: Skipped ${data.debug.skippedDays.length} day(s) due to VoteHub 5xx.`);
      console.warn(`See polls.json debug.skippedDays.`);
    }
  } catch (e) {
    console.error("Critical Error:\n" + String(e));
    process.exit(1);
  }
}

run();
