// Offline self-test of the constraint-level negative helper
// (src/tests/constraint-negative.ts), on the base probe contract. No proof
// server, node, or network: it checks the mechanics the prover-level suites
// rely on.
//
//   - The patched copy behaves exactly like the original on honest inputs
//     (pure and impure circuits, ledger state).
//   - A bypassed assert is recorded instead of thrown, so the bad call
//     completes local execution and writes its (bad) result; the original
//     refuses the same call in the generated JavaScript.
//   - An assert that is not bypassed still throws in the copy.
//   - A bypass message that is not an assert of the module is refused.
//   - classifyRefusal maps each layer's typical error to that layer, and
//     transport failures to infrastructure (an ERROR, never a pass).
//   - expectRefusal is fail-closed: a call that goes through is a FAIL, a
//     refusal at another layer is a FAIL, a bypassed assert that never fired
//     is a FAIL, and an infrastructure failure is an ERROR.

import { strict as assert } from 'node:assert';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createCircuitContext, createConstructorContext, sampleContractAddress } from '@midnight-ntwrk/compact-runtime';
import * as Original from '../../contracts/managed/probe-wallet-arms-base/contract/index.js';
import {
  loadBypassedContract, classifyRefusal, expectRefusal, expectSuccess, ProofServerRefusal,
} from './constraint-negative.js';

const here = path.dirname(fileURLToPath(import.meta.url));
const PROBE_JS = path.resolve(here, '..', '..', 'contracts', 'managed', 'probe-wallet-arms-base', 'contract', 'index.js');
const W64 = 'descriptor: not a 64-byte device tag';
const pad = (s: string) => { const o = new Uint8Array(32); o.set(Buffer.from(s, 'ascii')); return o; };
const eq = (a: Uint8Array, b: Uint8Array) => Buffer.from(a).equals(Buffer.from(b));
const A = { bytes: new Uint8Array(32).fill(7) };
const k = new Uint8Array(32).fill(1), b = new Uint8Array(32).fill(2);
const GOOD_TAG = pad('midnight:account:device:sol:v1'), BAD_TAG = pad('midnight:account:device:k1:v2');

const patched = await loadBypassedContract(PROBE_JS, [W64]);
assert.ok(!patched.file.startsWith(path.resolve(here, '..', '..')), 'the copy is written outside the repository');

// Pure circuits: identical on honest inputs; the bypassed assert is recorded.
assert.ok(eq(patched.pureCircuits.derive_descriptor_entry_w64(GOOD_TAG, A, k, b, 0n, 0n), Original.pureCircuits.derive_descriptor_entry_w64(GOOD_TAG, A, k, b, 0n, 0n)));
assert.deepEqual(patched.fired(), []);
assert.throws(() => Original.pureCircuits.derive_descriptor_entry_w64(BAD_TAG, A, k, b, 0n, 0n), /failed assert: descriptor: not a 64-byte device tag/);
const bad = patched.pureCircuits.derive_descriptor_entry_w64(BAD_TAG, A, k, b, 0n, 0n);
assert.equal(bad.length, 32);
assert.deepEqual(patched.fired(), [{ message: W64, count: 1 }]);
// Other asserts still throw in the copy.
assert.throws(() => patched.pureCircuits.derive_descriptor_entry_w65(GOOD_TAG, A, k, b, 0n, 0n, 0n), /not a 65-byte device tag/);
assert.throws(() => patched.pureCircuits.label_text_32(new Uint8Array(32)), /not a zero-padded label/);
patched.resetFired();
assert.deepEqual(patched.fired(), []);
console.log('  ✓ pure circuits: identical on honest inputs; the bypassed assert recorded, every other assert still thrown');

// Impure circuits against a local state: the bad call completes and writes
// its result; the original refuses it in the generated JavaScript.
const coinPk = { bytes: new Uint8Array(32).fill(9) };
const run = async (C: any, tag: Uint8Array) => {
  const c = new C({});
  const init = await c.initialState(createConstructorContext({}, coinPk));
  const ctx = createCircuitContext({
    circuitId: 'probe_entry_w64', contractAddress: sampleContractAddress(), coinPublicKeyOrZswapState: coinPk,
    contractState: init.currentContractState, privateState: {},
  });
  const r = await c.impureCircuits.probe_entry_w64(ctx, tag, A, k, b, 0n, 0n);
  return { derived: Original.ledger(r.context.callContext.currentQueryContext.state).derived, trace: r.context.callProofDataTrace };
};
const honest = await run(Original.Contract, GOOD_TAG);
const honestCopy = await run(patched.Contract, GOOD_TAG);
assert.ok(eq(honest.derived, honestCopy.derived), 'same ledger write');
assert.ok(eq(honest.derived, Original.pureCircuits.derive_descriptor_entry_w64(GOOD_TAG, A, k, b, 0n, 0n)));
await assert.rejects(() => run(Original.Contract, BAD_TAG), /failed assert: descriptor: not a 64-byte device tag/);
const forced = await run(patched.Contract, BAD_TAG);
assert.ok(eq(forced.derived, bad), 'the bad call writes the hash the circuit would have refused');
assert.equal(forced.trace.length, 1, 'one call proof data record, ready for the proof server');
assert.deepEqual(patched.fired(), [{ message: W64, count: 1 }]);
console.log('  ✓ impure circuit: the bad call completes local execution with a proof data record; the original refuses it');

await assert.rejects(() => loadBypassedContract(PROBE_JS, ['descriptor: not a 64-byte device tg']), /no assert message/);
console.log('  ✓ a bypass message that is not an assert of the module is refused');

// classifyRefusal.
const cases: [unknown, string][] = [
  [new Error('descriptor: not a canonical Ed25519 point'), 'client'],
  [Object.assign(new Error('failed assert: invalid signature'), { isCompactError: true }), 'runtime'],
  [new Error('wrapper', { cause: Object.assign(new Error('type error: x'), { isCompactError: true }) }), 'runtime'],
  [new Error('call failed', { cause: new ProofServerRefusal('/check', 'k', 400, 'Failed: constraint violated') }), 'prover'],
  [new Error('Failed Proof Server response: url="http://127.0.0.1:6300/check", code="400", status="Bad Request"'), 'prover'],
  [new ProofServerRefusal('/prove', 'k', 500, 'internal error'), 'infrastructure'],
  // As the ledger's proving loop relays it: the message only, as a string.
  [new Error("'check' returned an error: ProofServerRefusal: proof server /check refused (400): bad input: `Failed direct assertion`"), 'prover'],
  [new Error("'prove' returned an error: ProofServerRefusal: proof server /prove refused (503): unavailable"), 'infrastructure'],
  [new Error('1010: Invalid Transaction: Custom error: 134'), 'node'],
  [new Error('fetch failed', { cause: Object.assign(new Error('connect ECONNREFUSED 127.0.0.1:6300'), { code: 'ECONNREFUSED' }) }), 'infrastructure'],
  [new Error('something else'), 'unknown'],
];
for (const [e, layer] of cases) assert.equal(classifyRefusal(e).layer, layer, String((e as any).message));
console.log(`  ✓ classifyRefusal: ${cases.length} cases`);

// expectRefusal is fail-closed.
const notRefused = await expectRefusal({ name: 'goes through', expectedLayer: 'prover', attempt: async () => 1 });
assert.equal(notRefused.verdict, 'FAIL');
const elsewhere = await expectRefusal({ name: 'runtime, not prover', expectedLayer: 'prover', attempt: async () => { throw Object.assign(new Error('failed assert: x'), { isCompactError: true }); } });
assert.equal(elsewhere.verdict, 'FAIL');
const missed = await expectRefusal({
  name: 'bypass never fired', expectedLayer: 'prover', bypassed: patched,
  attempt: async () => { throw new ProofServerRefusal('/check', 'k', 400, 'x'); },
});
assert.equal(missed.verdict, 'FAIL');
assert.match(missed.reason, /never fired/);
const infra = await expectRefusal({ name: 'no proof server', expectedLayer: 'prover', attempt: async () => { throw new Error('fetch failed', { cause: new Error('ECONNREFUSED') }); } });
assert.equal(infra.verdict, 'ERROR');
const good = await expectRefusal({
  name: 'refused at the prover after the bypass fired', expectedLayer: 'prover', bypassed: patched,
  attempt: async () => { patched.pureCircuits.derive_descriptor_entry_w64(BAD_TAG, A, k, b, 0n, 0n); throw new ProofServerRefusal('/check', 'k', 400, 'x'); },
});
assert.equal(good.verdict, 'PASS');
assert.equal((await expectSuccess({ name: 'ok', attempt: async () => 1 })).verdict, 'PASS');
assert.equal((await expectSuccess({ name: 'infra', attempt: async () => { throw new Error('ECONNREFUSED'); } })).verdict, 'ERROR');
console.log('  ✓ expectRefusal / expectSuccess: fail-closed verdicts');

console.log('\n◆ constraint-negative-offline: PASS');
