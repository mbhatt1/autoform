// Runner for the differential harness's `wasm` C execution mode.
//
// Reads a JSON request file [{id, name, args:[int,...]}, ...], executes each call
// against a wasm32 module, and writes one JSON result line per request to stdout,
// FLUSHED AS IT GOES. The flushing matters: a wasm function can loop forever, and the
// parent recovers by noticing which id never produced a line. A silently truncated
// batch would otherwise read as "no cases", which is the failure mode this harness is
// built to avoid.
//
// Every call gets a FRESH instance. Wasm linear memory is mutable and a call that
// scribbles on it would otherwise change the meaning of later calls in the batch,
// making results order-dependent and non-reproducible.
import fs from 'fs';
import { WASI } from 'node:wasi';

const wasmPath = process.argv[2];
const reqPath = process.argv[3];
const requests = JSON.parse(fs.readFileSync(reqPath, 'utf8'));
const mod = new WebAssembly.Module(fs.readFileSync(wasmPath));

// A trap is a RECORDED OUTCOME, not a crash. Classify it so "read out of bounds"
// (usually: we passed an integer where the C wanted a pointer) is distinguishable
// from "divided by zero" (a real property of the program under test).
function trapKind(msg) {
  const m = (msg || '').toLowerCase();
  if (m.includes('out of bounds')) return 'oob';
  if (m.includes('divide by zero')) return 'divzero';
  if (m.includes('unrepresentable')) return 'div-overflow';
  if (m.includes('unreachable')) return 'unreachable';
  if (m.includes('null function') || m.includes('signature mismatch')) return 'indirect-call';
  if (m.includes('call stack') || m.includes('stack overflow')) return 'stack-exhausted';
  return 'other';
}

// We link with `-Wl,--allow-undefined`, so any libc symbol the corpus references
// becomes an IMPORT rather than a link error. That buys coverage on real code, but
// only honestly: we implement the handful of pure/allocating routines whose semantics
// are unambiguous, and every other import throws a distinctive error that the parent
// records as `unsupported-import`. A stub that returned a plausible-looking 0 would
// manufacture agreement out of a function we never actually ran.
function makeImports(instRef) {
  const mem = () => new Uint8Array(instRef.inst.exports.memory.buffer);
  const bump = { next: 0 };
  const malloc = (n) => {
    if (bump.next === 0) {
      const hb = instRef.inst.exports.__heap_base;
      bump.next = (hb && hb.value) ? hb.value : 65536;
    }
    n = (n + 15) & ~15;
    const total = instRef.inst.exports.memory.buffer.byteLength;
    if (n < 0 || bump.next + n > total) return 0;   // OOM -> NULL, as malloc may
    const p = bump.next; bump.next += n; return p;
  };
  const known = {
    malloc, free: () => {},
    calloc: (n, s) => { const p = malloc(n * s); if (p) mem().fill(0, p, p + n * s); return p; },
    realloc: (p, n) => { const q = malloc(n); if (q && p) mem().copyWithin(q, p, p + n); return q; },
    memcpy: (d, s, n) => { mem().copyWithin(d, s, s + n); return d; },
    memmove: (d, s, n) => { mem().copyWithin(d, s, s + n); return d; },
    memset: (d, c, n) => { mem().fill(c & 0xff, d, d + n); return d; },
    strlen: (p) => { const m = mem(); let i = p; while (m[i] !== 0) i++; return i - p; },
    memcmp: (a, b, n) => { const m = mem(); for (let i = 0; i < n; i++) { if (m[a + i] !== m[b + i]) return m[a + i] - m[b + i]; } return 0; },
  };
  // A wasi-libc build imports the `wasi_snapshot_preview1` namespace. node ships a real
  // implementation, so we use it rather than stubbing: sandboxed, no preopened dirs, no
  // inherited stdio, so a function that tries to touch the filesystem gets a genuine
  // WASI error instead of the host's real files.
  let wasiImport = {};
  try {
    instRef.wasi = new WASI({ version: 'preview1', args: [], env: {}, preopens: {} });
    wasiImport = instRef.wasi.wasiImport;
  } catch { /* older node, or no wasi imports needed */ }

  const imports = {};
  for (const { module, name } of WebAssembly.Module.imports(mod)) {
    imports[module] = imports[module] || {};
    if (module === 'wasi_snapshot_preview1' && wasiImport[name]) {
      imports[module][name] = wasiImport[name];
      continue;
    }
    imports[module][name] = known[name] || (() => {
      const e = new Error('unsupported import: ' + name);
      e.unsupportedImport = name;
      throw e;
    });
  }
  return imports;
}

const out = (o) => fs.writeSync(1, JSON.stringify(o) + '\n');

for (const r of requests) {
  let instRef = {};
  try {
    instRef.inst = new WebAssembly.Instance(mod, makeImports(instRef));
  } catch (e) {
    out({ id: r.id, status: 'error', reason: 'instantiate: ' + e.message });
    continue;
  }
  // Bind node's WASI to this instance's memory, then run static constructors. Both are
  // best-effort: a freestanding module has neither, and a module that needs them but
  // fails here will surface as a trap on the actual call rather than being skipped.
  try { if (instRef.wasi) instRef.wasi.initialize(instRef.inst); } catch { /* reactor w/o _initialize */ }
  try { instRef.inst.exports.__wasm_call_ctors?.(); } catch { /* no ctors */ }

  const fn = instRef.inst.exports[r.name];
  if (typeof fn !== 'function') { out({ id: r.id, status: 'missing' }); continue; }
  try {
    const v = fn(...r.args);
    // Exports are i32 here; JS hands them back as signed numbers already. A BigInt
    // would mean an i64 return, which the parent's int model does not cover.
    if (typeof v === 'bigint') { out({ id: r.id, status: 'unsupported', reason: 'i64-return' }); continue; }
    if (typeof v !== 'number' || !Number.isInteger(v)) {
      out({ id: r.id, status: 'unsupported', reason: 'non-integer-return:' + typeof v });
      continue;
    }
    // memBytes lets the parent ask "is this value a plausible pointer into linear
    // memory?", which is how a pointer-return disagreement is told apart from a real
    // cross-implementation value disagreement.
    out({ id: r.id, status: 'val', value: v,
          memBytes: instRef.inst.exports.memory ? instRef.inst.exports.memory.buffer.byteLength : 0 });
  } catch (e) {
    if (e && e.unsupportedImport) {
      out({ id: r.id, status: 'unsupported', reason: 'import:' + e.unsupportedImport });
    } else if (e instanceof WebAssembly.RuntimeError || (e && e.constructor && e.constructor.name === 'RuntimeError')) {
      out({ id: r.id, status: 'trap', kind: trapKind(e.message), message: String(e.message).slice(0, 120) });
    } else {
      out({ id: r.id, status: 'error', reason: String(e && e.message).slice(0, 120) });
    }
  }
}
