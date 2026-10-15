// Constraint-level negatives — a test-only helper (FR-019 of the readable
// wallet arms; usable by any suite).
//
// The generated JavaScript of a contract repeats every `assert` of its
// circuits, so a bad call normally aborts during local execution, before
// anything reaches the proof server. A negative that stops there shows that
// the JavaScript checks the rule; it does not show that the PROOF enforces it.
// This helper closes that gap:
//
//   1. loadBypassedContract copies a compiled contract module and replaces its
//      runtime `assert` with one that RECORDS, instead of throwing, the
//      failures of the named assert messages (every other assert still
//      throws). The copy runs only on the client: it builds the witness and
//      the transcript of the bad call, nothing else.
//   2. The call is built with that copy as usual (midnight-js, or the
//      runtime directly), so local execution completes.
//   3. recordingProofProvider sends it to the proof server through a proving
//      provider that records every /check and /prove request with its status
//      and body, without retries.
//   4. expectRefusal classifies the layer that refused the call:
//        client   a strict client decoder (messages "descriptor: ...",
//                 "blind: ...") before any contract code runs;
//        runtime  the generated JavaScript (a failed assert, a type or range
//                 check) during local execution;
//        prover   the proof server (HTTP 4xx from /check or /prove): the
//                 constraints are unsatisfiable;
//        node     the node or ledger refused the submitted transaction.
//
// Fail-closed: a negative passes only when the expected layer refused it AND
// every bypassed assert fired (otherwise the tampering missed its target); a
// call that goes through is a FAIL; an unreachable or failing proof server,
// indexer, or node (connection errors, timeouts, HTTP 5xx) is an ERROR, never
// a pass. Run a positive control through the same path first, so that a
// refusal is attributable to the tampering and not to the path.

import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { randomUUID } from 'node:crypto';
import { tmpdir } from 'node:os';
import * as path from 'node:path';
import { pathToFileURL } from 'node:url';
import {
  CostModel,
  createCheckPayload,
  createProvingPayload,
  parseCheckResult,
  type ProvingProvider,
} from '@midnightntwrk/ledger-v9';
import { createProofProviderFromHandlers, type ProofProvider } from '@midnight-ntwrk/midnight-js-types';
import { httpClientProvingProvider } from '@midnight-ntwrk/midnight-js-http-client-proof-provider';

// ── 1. A contract module with chosen asserts bypassed ───────────────────────

const RUNTIME_IMPORT = "import * as __compactRuntime from '@midnight-ntwrk/compact-runtime';";
const REGISTRY = Symbol.for('midnight-passport.constraint-negative');

interface BypassState { messages: Set<string>; fired: Map<string, number> }
const registry: Map<string, BypassState> = ((globalThis as any)[REGISTRY] ??= new Map());

export interface FiredAssert { message: string; count: number }

export interface BypassedContractModule {
  /** The patched module's exports (Contract, ledger, pureCircuits, ...). */
  readonly module: any;
  readonly Contract: any;
  readonly ledger: any;
  readonly pureCircuits: any;
  /** The assert messages this copy records instead of throwing. */
  readonly bypassed: readonly string[];
  /** The bypassed asserts that failed since the last reset. */
  fired(): FiredAssert[];
  resetFired(): void;
  /** The patched copy on disk (outside the repository). */
  readonly file: string;
}

/**
 * Loads a copy of the compiled contract module at `contractJs` whose runtime
 * `assert` records, instead of throwing, a failure of any message in
 * `bypass`. Refuses a message that is not an assert message of the module,
 * so a typo cannot silently bypass nothing.
 */
export async function loadBypassedContract(contractJs: string, bypass: readonly string[]): Promise<BypassedContractModule> {
  const source = await readFile(contractJs, 'utf8');
  if (source.split(RUNTIME_IMPORT).length !== 2) {
    throw new Error(`constraint-negative: ${contractJs} does not import the runtime exactly once as expected`);
  }
  for (const m of bypass) {
    if (!source.includes(`'${m}'`) && !source.includes(JSON.stringify(m))) {
      throw new Error(`constraint-negative: no assert message ${JSON.stringify(m)} in ${contractJs}`);
    }
  }
  const id = randomUUID();
  const state: BypassState = { messages: new Set(bypass), fired: new Map() };
  registry.set(id, state);
  // The same runtime module instance the original resolves to (one copy is
  // installed), so values cross between the copy and midnight-js unchanged.
  const runtimeUrl = import.meta.resolve('@midnight-ntwrk/compact-runtime');
  const prelude = [
    `import * as __compactRuntimeOriginal from ${JSON.stringify(runtimeUrl)};`,
    `const __bypass = globalThis[Symbol.for('midnight-passport.constraint-negative')].get(${JSON.stringify(id)});`,
    'const __compactRuntime = Object.freeze({',
    '  ...__compactRuntimeOriginal,',
    '  assert(condition, message) {',
    '    if (!condition && __bypass.messages.has(message)) {',
    '      __bypass.fired.set(message, (__bypass.fired.get(message) ?? 0) + 1);',
    '      return;',
    '    }',
    '    return __compactRuntimeOriginal.assert(condition, message);',
    '  },',
    '});',
  ].join('\n');
  const patched = source.replace(RUNTIME_IMPORT, prelude).replace(/^\/\/# sourceMappingURL=.*$/m, '');
  // .mjs: outside any package.json, a .js file would go through Node's
  // CommonJS detection and load a second runtime instance.
  const dir = await mkdtemp(path.join(tmpdir(), 'constraint-negative-'));
  const file = path.join(dir, 'index.mjs');
  await writeFile(file, patched);
  const module = await import(pathToFileURL(file).href);
  return {
    module,
    Contract: module.Contract,
    ledger: module.ledger,
    pureCircuits: module.pureCircuits,
    bypassed: [...bypass],
    fired: () => [...state.fired].map(([message, count]) => ({ message, count })),
    resetFired: () => state.fired.clear(),
    file,
  };
}

// ── 3. A proving provider that records every request ────────────────────────

export interface ProofServerRequest {
  endpoint: '/check' | '/prove';
  keyLocation: string;
  startedAt: string;
  ms: number;
  status: number | null;
  ok: boolean;
  /** The response body of a refused request (text, at most 4 kB). */
  body?: string;
  /** A transport failure (no HTTP status). */
  error?: string;
}

/** The proof server answered with an HTTP error status. */
export class ProofServerRefusal extends Error {
  constructor(readonly endpoint: string, readonly keyLocation: string, readonly status: number, readonly body: string) {
    super(`proof server ${endpoint} refused (${status}): ${body.slice(0, 300)}`);
    this.name = 'ProofServerRefusal';
  }
}

/** A ledger ProvingProvider over a proof server: no retries; every request
 *  and its answer are appended to `log`. */
export function recordingProvingProvider(
  url: string, zkConfigProvider: any, log: ProofServerRequest[], timeoutMs = 600_000,
): ProvingProvider {
  const { lookupKey } = httpClientProvingProvider(url, zkConfigProvider);
  const endpointUrl = (endpoint: string) => {
    const u = new URL(url);
    u.pathname = u.pathname.replace(/\/$/, '') + endpoint;
    return u;
  };
  const post = async (endpoint: '/check' | '/prove', keyLocation: string, payload: Uint8Array): Promise<Uint8Array> => {
    const rec: ProofServerRequest = { endpoint, keyLocation, startedAt: new Date().toISOString(), ms: 0, status: null, ok: false };
    const t0 = Date.now();
    let res: Response;
    try {
      res = await fetch(endpointUrl(endpoint), {
        method: 'POST', body: new Uint8Array(payload), headers: { 'Content-Type': 'application/octet-stream' },
        signal: AbortSignal.timeout(timeoutMs),
      });
    } catch (e: any) {
      rec.ms = Date.now() - t0;
      rec.error = String(e?.cause?.code ?? e?.message ?? e);
      log.push(rec);
      throw e;
    }
    const bytes = new Uint8Array(await res.arrayBuffer());
    rec.ms = Date.now() - t0;
    rec.status = res.status;
    rec.ok = res.ok;
    if (!res.ok) {
      rec.body = new TextDecoder().decode(bytes).slice(0, 4096);
      log.push(rec);
      throw new ProofServerRefusal(endpoint, keyLocation, res.status, rec.body);
    }
    log.push(rec);
    return bytes;
  };
  return {
    async check(serializedPreimage, keyLocation) {
      const km = await lookupKey(keyLocation);
      return parseCheckResult(await post('/check', keyLocation, createCheckPayload(serializedPreimage, km?.ir)));
    },
    async prove(serializedPreimage, keyLocation, overwriteBindingInput) {
      const km = await lookupKey(keyLocation);
      return post('/prove', keyLocation, createProvingPayload(serializedPreimage, overwriteBindingInput, km));
    },
    lookupKey,
  };
}

/** A midnight-js ProofProvider (current era) over recordingProvingProvider:
 *  substitute it for `providers.proofProvider` to record a call's proving. */
export function recordingProofProvider(url: string, zkConfigProvider: any, log: ProofServerRequest[]): ProofProvider {
  const proving = recordingProvingProvider(url, zkConfigProvider, log);
  return createProofProviderFromHandlers({
    currentEra: (tx) => tx.prove(proving, CostModel.initialCostModel()),
  });
}

// ── 4. Classification ────────────────────────────────────────────────────────

export type RefusalLayer = 'client' | 'runtime' | 'prover' | 'node';

export interface Classification {
  /** The refusing layer, or `infrastructure` (an ERROR) or `unknown`. */
  layer: RefusalLayer | 'infrastructure' | 'unknown';
  detail: string;
  /** The error's cause chain, outermost first. */
  chain: { name: string; message: string }[];
}

const errorChain = (e: unknown): any[] => {
  const out: any[] = [];
  let cur: any = e;
  for (let i = 0; cur && i < 10; i++) { out.push(cur); cur = cur.cause ?? cur.error; }
  return out;
};

/** The layer an error comes from (see the header). */
export function classifyRefusal(err: unknown): Classification {
  const chain = errorChain(err);
  const shown = chain.map((c) => ({ name: String(c?.name ?? typeof c), message: String(c?.message ?? c).slice(0, 2000) }));
  const text = shown.map((c) => c.message).join(' | ');
  const lower = text.toLowerCase();
  const refusal = chain.find((c) => c instanceof ProofServerRefusal) as ProofServerRefusal | undefined;
  if (refusal) {
    return refusal.status >= 400 && refusal.status < 500
      ? { layer: 'prover', detail: `${refusal.endpoint} ${refusal.status}: ${refusal.body.slice(0, 500)}`, chain: shown }
      : { layer: 'infrastructure', detail: `proof server ${refusal.endpoint} ${refusal.status}: ${refusal.body.slice(0, 500)}`, chain: shown };
  }
  // The ledger's proving loop crosses a WASM boundary that keeps only the
  // message of the provider's error ("'check' returned an error:
  // ProofServerRefusal: proof server /check refused (400): ...").
  const relayed = lower.match(/proof server (\/check|\/prove) refused \((\d+)\)/);
  if (relayed) {
    const status = Number(relayed[2]);
    return { layer: status >= 400 && status < 500 ? 'prover' : 'infrastructure', detail: text.slice(0, 500), chain: shown };
  }
  const httpProver = lower.match(/failed proof server response:.*code="(\d+)"/);
  if (httpProver) {
    const status = Number(httpProver[1]);
    return { layer: status >= 400 && status < 500 ? 'prover' : 'infrastructure', detail: text.slice(0, 500), chain: shown };
  }
  if (/econnrefused|econnreset|enotfound|etimedout|fetch failed|socket hang up|aborterror|timed? ?out|network error/.test(lower)) {
    return { layer: 'infrastructure', detail: text.slice(0, 500), chain: shown };
  }
  if (chain.some((c) => /^(descriptor|blind): /.test(String(c?.message ?? '')))) {
    return { layer: 'client', detail: text.slice(0, 500), chain: shown };
  }
  if (chain.some((c) => c?.isCompactError) || /failed assert: |type error: |cast from field or uint value/.test(lower)) {
    return { layer: 'runtime', detail: text.slice(0, 500), chain: shown };
  }
  if (/custom error:\s*\d+|invalid transaction|submissionerror|malformederror|transaction failed|failentirely|failfallible/.test(lower)) {
    return { layer: 'node', detail: text.slice(0, 500), chain: shown };
  }
  return { layer: 'unknown', detail: text.slice(0, 500), chain: shown };
}

// ── 2 and 4. Running a negative and its positive control ────────────────────

export type Verdict = 'PASS' | 'FAIL' | 'ERROR';

export interface NegativeResult {
  name: string;
  expectedLayer: RefusalLayer;
  layer: Classification['layer'] | 'none';
  verdict: Verdict;
  reason: string;
  bypassed: readonly string[];
  fired: FiredAssert[];
  proofServer: ProofServerRequest[];
  detail?: string;
  chain?: Classification['chain'];
  startedAt: string;
  ms: number;
}

/**
 * Runs `attempt`, which must be refused at `expectedLayer`. PASS only when it
 * is, and every assert bypassed by `bypassed` fired; FAIL when it is refused
 * elsewhere, goes through, or a bypassed assert never fired; ERROR when the
 * infrastructure failed or the refusal cannot be classified.
 */
export async function expectRefusal(opts: {
  name: string;
  expectedLayer: RefusalLayer;
  attempt: () => Promise<unknown>;
  bypassed?: BypassedContractModule;
  proofLog?: ProofServerRequest[];
}): Promise<NegativeResult> {
  const startedAt = new Date().toISOString();
  const t0 = Date.now();
  const logStart = opts.proofLog?.length ?? 0;
  opts.bypassed?.resetFired();
  const base = {
    name: opts.name, expectedLayer: opts.expectedLayer, bypassed: opts.bypassed?.bypassed ?? [], startedAt,
  };
  const finish = (r: Omit<NegativeResult, keyof typeof base | 'fired' | 'proofServer' | 'ms'>): NegativeResult => ({
    ...base, ...r,
    fired: opts.bypassed?.fired() ?? [],
    proofServer: opts.proofLog?.slice(logStart) ?? [],
    ms: Date.now() - t0,
  });
  try {
    await opts.attempt();
    return finish({ layer: 'none', verdict: 'FAIL', reason: 'the call was NOT refused' });
  } catch (e) {
    const c = classifyRefusal(e);
    const fired = opts.bypassed?.fired() ?? [];
    const missed = (opts.bypassed?.bypassed ?? []).filter((m) => !fired.some((f) => f.message === m));
    if (c.layer === 'infrastructure' || c.layer === 'unknown') {
      return finish({ layer: c.layer, verdict: 'ERROR', reason: `not a verdict: ${c.layer} failure`, detail: c.detail, chain: c.chain });
    }
    if (c.layer !== opts.expectedLayer) {
      return finish({ layer: c.layer, verdict: 'FAIL', reason: `refused at ${c.layer}, expected ${opts.expectedLayer}`, detail: c.detail, chain: c.chain });
    }
    if (missed.length) {
      return finish({ layer: c.layer, verdict: 'FAIL', reason: `bypassed assert(s) never fired: ${missed.join('; ')}`, detail: c.detail, chain: c.chain });
    }
    return finish({ layer: c.layer, verdict: 'PASS', reason: `refused at ${c.layer}`, detail: c.detail, chain: c.chain });
  }
}

export interface PositiveResult {
  name: string;
  verdict: Verdict;
  reason: string;
  result?: unknown;
  proofServer: ProofServerRequest[];
  detail?: string;
  chain?: Classification['chain'];
  startedAt: string;
  ms: number;
}

/** Runs a call that must go through (the positive control of a path). An
 *  infrastructure failure is an ERROR; any other refusal a FAIL. */
export async function expectSuccess(opts: {
  name: string;
  attempt: () => Promise<unknown>;
  proofLog?: ProofServerRequest[];
}): Promise<PositiveResult> {
  const startedAt = new Date().toISOString();
  const t0 = Date.now();
  const logStart = opts.proofLog?.length ?? 0;
  const done = (r: Omit<PositiveResult, 'name' | 'proofServer' | 'startedAt' | 'ms'>): PositiveResult => ({
    name: opts.name, ...r, proofServer: opts.proofLog?.slice(logStart) ?? [], startedAt, ms: Date.now() - t0,
  });
  try {
    const result = await opts.attempt();
    return done({ verdict: 'PASS', reason: 'went through', result });
  } catch (e) {
    const c = classifyRefusal(e);
    return done({
      verdict: c.layer === 'infrastructure' || c.layer === 'unknown' ? 'ERROR' : 'FAIL',
      reason: `refused at ${c.layer}`, detail: c.detail, chain: c.chain,
    });
  }
}
