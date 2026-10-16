// Arm `sol_ed25519`: the device seam, offline (the generated JavaScript, no
// proof server, no node), through `rotate_enc_key_with_sol_ed25519`.
//
// The binding matrix: a valid signature, then one signed value changed at
// execution (the new key, the site's label, the nonce, the account, the
// signing key, the use counter, the blind, the operation), each refused. The
// replay matrix: the same authorisation again, at the old and at the new use
// counter; across two accounts of the same device; across operations. The
// degenerate signatures: R = O, small-order and mixed-order R, S + L. The
// positive control lands first and the state transition is checked (FR-007:
// the entry rolls, auth_nonce and round advance, last-device rule).
//
// The constraint-level half of the same matrix is `npm run test:sol-ed25519`
// (src/tests/sol-ed25519-prover.ts, section `seam`); the on-node half ran
// through the local runner at S5 (the landed transaction replayed at the
// node). No test reads the contract source: what the seams' call sites must
// do is held by these functional calls (AA 00067 Q41, owner 2026-10-16).
//
// Writes $EVIDENCE_DIR/sol-ed25519-seam-offline.json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { randomBytes } from 'node:crypto';
import { ed25519 } from '@noble/curves/ed25519.js';
import { createCircuitContext, createConstructorContext, sampleContractAddress } from '@midnight-ntwrk/compact-runtime';

import { Contract, ledger, pureCircuits } from '../wallet/contract.js';
import { makeWitnesses, emptyCoinStore } from '../wallet/witnesses.js';
import { JubjubDevice, K256Device, authArgs, k256Challenges, p256Challenges } from '../wallet/signer.js';
import { softwarePasskey } from './p256-fixtures.js';
import {
  ED25519_L, SolEd25519Device, authoriseSolDevice, decodeSolSignature, deriveSolBlind, solSoftwareSigner,
  solDeviceMessageCircuit, solEd25519AuthArgs, type SolEd25519Authorisation,
} from '../wallet/signer-sol-ed25519.js';
import { nibblesOf, solShow } from '../wallet/sol-ed25519-message.js';
import { solBlindMessage } from '../wallet/signer-sol-ed25519.js';

interface Case { group: string; name: string; verdict: 'PASS' | 'FAIL'; layer?: string; detail?: string }
const cases: Case[] = [];
const ok = (group: string, name: string, cond: boolean, detail?: string, layer?: string) => {
  cases.push({ group, name, verdict: cond ? 'PASS' : 'FAIL', ...(layer ? { layer } : {}), ...(detail ? { detail } : {}) });
  if (!cond) console.log(`  ✗ ${group}: ${name}${detail ? ` — ${detail}` : ''}`);
};
const refused = async (group: string, name: string, layer: string, re: RegExp, fn: () => Promise<unknown> | unknown) => {
  try { await fn(); ok(group, name, false, 'accepted (expected a refusal)', layer); } catch (e: any) {
    const m = String(e?.message ?? e); ok(group, name, re.test(m), m.slice(0, 200), layer);
  }
};
const rnd = (n: number) => new Uint8Array(randomBytes(n));
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const SITE = 'Seam test';

interface Sim { contract: any; state: any; ps: any; address: string; bytes: Uint8Array }
const ledgerOf = (s: any) => ledger(s?.constructor?.name === 'ContractState' ? s.data : s);
async function deploy(device: SolEd25519Device): Promise<Sim> {
  const contract = new (Contract as any)(makeWitnesses());
  const ps = emptyCoinStore();
  const salt = rnd(32);
  const init = await contract.initialState(createConstructorContext(ps, { bytes: rnd(32) }), device.bootCommitment(salt), rnd(32), JubjubDevice.generate().pk, new Uint8Array(64), 259200n);
  const address = sampleContractAddress();
  const sim: Sim = { contract, state: init.currentContractState, ps, address, bytes: new Uint8Array(Buffer.from(address.replace(/^0x/, ''), 'hex')) };
  await call(sim, 'activate_initial_device_with_sol_ed25519', ...device.activationArgs(salt));
  return sim;
}
async function call(sim: Sim, circuit: string, ...args: unknown[]) {
  const ctx = createCircuitContext({ circuitId: circuit, contractAddress: sim.address, coinPublicKeyOrZswapState: { bytes: rnd(32) }, contractState: sim.state, privateState: sim.ps, time: 1_800_000_000 } as any);
  const r = await sim.contract.impureCircuits[circuit](ctx, ...args);
  sim.state = r.context.callContext.currentQueryContext.state;
  return r.result;
}
const ctxOf = (sim: Sim) => ({ contractAddress: sim.bytes, authNonce: ledgerOf(sim.state).auth_nonce as bigint });
const rotate = (sim: Sim, newKey: Uint8Array, a: SolEd25519Authorisation) => call(sim, 'rotate_enc_key_with_sol_ed25519', newKey, ...authArgs(a));
const withSig = (a: SolEd25519Authorisation, sig: any): SolEd25519Authorisation => ({ ...a, sig });

const signerA = solSoftwareSigner(rnd(32));
const recA = await deriveSolBlind(signerA, { network: 'undeployed', accountIndex: 0 });
const devA = SolEd25519Device.fromSigner(signerA, recA);
const signerB = solSoftwareSigner(rnd(32));
const devB = SolEd25519Device.fromSigner(signerB, await deriveSolBlind(signerB, { network: 'undeployed', accountIndex: 0 }));

// ── 1. Positive control and the state transition (FR-007) ──────────────────
const G1 = '1 positive control';
const sim = await deploy(devA);
const k1 = rnd(32);
const before = ledgerOf(sim.state);
const a1 = await authoriseSolDevice(devA, ctxOf(sim), SITE, { op: 'rotate_enc_key', newKey: k1 }, 0n);
ok(G1, 'authArgs routes through the signer.ts registration branch', JSON.stringify(authArgs(a1), (_k, v) => (typeof v === 'bigint' ? v.toString() : v)) === JSON.stringify(solEd25519AuthArgs(a1), (_k, v) => (typeof v === 'bigint' ? v.toString() : v)));
await rotate(sim, k1, a1);
const after = ledgerOf(sim.state);
ok(G1, 'rotate lands: enc_key set, auth_nonce +1, round +1, entry rolled 0 -> 1, one device', hex(after.enc_key) === hex(k1)
  && after.auth_nonce === before.auth_nonce + 1n && after.round > before.round && after.device_count === 1n
  && !after.devices.member(devA.entryAt(sim.bytes, after.device_epoch, 0n)) && after.devices.member(devA.entryAt(sim.bytes, after.device_epoch, 1n)));
ok(G1, 'the signed message is the contract\'s own bytes (511, format sol v1)', a1.message.length === 511 && a1.text.startsWith('Midnight Passport approval (sol v1)\nOperation: Rotate the encryption key\n'));

// An attacker who changes executed values supplies display inputs that are
// CONSISTENT with them (otherwise the display check refuses first); the
// signature is the one the wallet gave. `exec` builds exactly that call.
const exec = (target: Sim, newKey: Uint8Array, a: SolEd25519Authorisation, opt: { site?: string; key?: Uint8Array } = {}) => {
  const { showArgs } = solDeviceMessageCircuit(opt.key ?? devA.key, ctxOf(target), opt.site ?? SITE, { op: 'rotate_enc_key', newKey });
  return rotate(target, newKey, { ...a, showArgs });
};

// ── 2. Binding: one signed value changed at execution ────────────────────────
const G2 = '2 binding';
const ctx = ctxOf(sim); // auth_nonce 1, counter 1
const k2 = rnd(32);
const a2 = await authoriseSolDevice(devA, ctx, SITE, { op: 'rotate_enc_key', newKey: k2 }, 1n);
await refused(G2, 'another new key at execution (consistent display inputs)', 'runtime', /invalid signature/, () => exec(sim, rnd(32), a2));
await refused(G2, 'another site label at execution (consistent display inputs)', 'runtime', /invalid signature/, () => exec(sim, k2, a2, { site: 'Another site' }));
await refused(G2, "device B's signature presented with A's key", 'runtime', /invalid signature/, async () => {
  const b = await authoriseSolDevice(devB, ctx, SITE, { op: 'rotate_enc_key', newKey: k2 }, 1n);
  return exec(sim, k2, withSig(a2, b.sig));
});
await refused(G2, 'device B presents its own key (no entry in this account)', 'runtime', /unknown device entry/, async () =>
  rotate(sim, k2, await authoriseSolDevice(devB, ctx, SITE, { op: 'rotate_enc_key', newKey: k2 }, 0n)));
await refused(G2, 'another use counter', 'runtime', /unknown device entry/, () => exec(sim, k2, { ...a2, use_counter: 2n }));
await refused(G2, 'another blind', 'runtime', /unknown device entry/, () => exec(sim, k2, { ...a2, blind: rnd(32) }));
await refused(G2, 'the signature of another operation (append_inbox) over the same nonce', 'runtime', /invalid signature/, async () => {
  const other = await authoriseSolDevice(devA, ctx, SITE, { op: 'append_inbox', entry: rnd(192) }, 1n);
  return exec(sim, k2, withSig(a2, other.sig));
});
const G2b = '2b display inputs inconsistent with the executed values';
await refused(G2b, 'nonce digits of another value', 'runtime', /digits do not match/, () => rotate(sim, k2, { ...a2, showArgs: [solShow(SITE, 2n), a2.showArgs[1], a2.showArgs[2]] }));
await refused(G2b, 'hex nibbles of the signed key while another key executes', 'runtime', /hex digits do not match/, () => rotate(sim, rnd(32), a2));
// G1E-1: the frame (account, signing key) is the seam's; foreign frame nibbles are refused.
await refused(G2b, 'frame nibbles of another account', 'runtime', /hex digits do not match/, () => rotate(sim, k2, { ...a2, showArgs: [a2.showArgs[0], nibblesOf(rnd(32), devA.key), a2.showArgs[2]] }));
await refused(G2b, "frame nibbles of another device's key", 'runtime', /hex digits do not match/, () => rotate(sim, k2, { ...a2, showArgs: [a2.showArgs[0], nibblesOf(sim.bytes, devB.key), a2.showArgs[2]] }));

// ── 3. Replay ───────────────────────────────────────────────────────────────
const G3 = '3 replay';
await refused(G3, 'the landed authorisation again (consumed entry)', 'runtime', /unknown device entry/, () => exec(sim, k1, a1));
await refused(G3, 'the landed signature at the current counter (the message now carries nonce 1)', 'runtime', /invalid signature/, () => exec(sim, k1, { ...a1, use_counter: 1n }));
const sim2 = await deploy(devA); // the same device and blind on another account
const a2b = await authoriseSolDevice(devA, ctxOf(sim2), SITE, { op: 'rotate_enc_key', newKey: k2 }, 0n);
await refused(G3, "another account's signature (same device, same blind, nonce 0)", 'runtime', /invalid signature/, () => exec(sim2, k1, withSig(a2b, a1.sig)));
await rotate(sim2, k2, a2b);
ok(G3, 'the same device rotates the second account with its own approval (positive control)', hex(ledgerOf(sim2.state).enc_key) === hex(k2));

// ── 3b. Cross-arm replay (AA 00067 audit G1(S), G1S-3) ───────────────────────
// What another arm's device signs for the same call (its 32-byte challenge for
// rotate_enc_key on this account, nonce and key), or the arm's own blind
// request, signed raw by this Solana key (a wallet that signs whatever bytes
// it is given), presented to this arm's seam with consistent display inputs:
// refused by the signature, because the seam verifies over the sol v1 bytes
// it renders. The reverse direction has no vector on this branch: no other
// arm verifies Ed25519 (jubjub verifies Schnorr over JubJub, k256 and p256
// ECDSA), so a sol_ed25519 signature cannot even be passed to them.
const G3b = '3b cross-arm replay';
{
  const k = K256Device.generate();
  const pass = softwarePasskey();
  const ctxNow = ctxOf(sim); // auth_nonce 1, counter 1 (a2 is still unused)
  const kCh: Uint8Array = k256Challenges.rotateEncKey(ctxNow, k.pk, k2);
  const pCh: Uint8Array = p256Challenges.rotateEncKey(ctxNow, pass.pk, k2);
  const blindReq = solBlindMessage(devA.key, { network: 'undeployed', accountIndex: 0 }).bytes;
  for (const [name, bytes] of [
    ['the k256 arm\'s rotate_enc_key challenge (same account, nonce, key), signed by the Solana key', kCh],
    ['the p256 arm\'s rotate_enc_key challenge (same account, nonce, key), signed by the Solana key', pCh],
    ['the arm\'s own blind request (non-authorising), signed by the same key', blindReq],
  ] as [string, Uint8Array][]) {
    const { sig } = await devA.signBytes(bytes);
    await refused(G3b, name, 'runtime', /invalid signature/, () => exec(sim, k2, withSig(a2, sig)));
  }
  ok(G3b, 'positive control: the same key\'s sol v1 approval for that call is a different message', !Buffer.from(a2.message).equals(Buffer.from(kCh)) && a2.message.length === 511);
}

// ── 4. Degenerate signatures ────────────────────────────────────────────────
const G4 = '4 degenerate signatures';
const sigBytes = (a: SolEd25519Authorisation) => a.sig;
const T8 = ed25519.Point.fromBytes(Buffer.from('c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a', 'hex'), false);
const aff = (p: any) => { const q = p.toAffine(); return { x: q.x, y: q.y }; };
await refused(G4, 'R = O (identity commitment)', 'runtime', /R is the identity/, () => rotate(sim, k2, withSig(a2, { r: { x: 0n, y: 1n }, s: sigBytes(a2).s })));
await refused(G4, 'R of small order (8)', 'runtime', /Curve25519Point|type error/i, () => rotate(sim, k2, withSig(a2, { r: aff(T8), s: sigBytes(a2).s })));
await refused(G4, 'R of mixed order (R + T8)', 'runtime', /Curve25519Point|type error/i, () => rotate(sim, k2, withSig(a2, { r: aff(ed25519.Point.fromAffine(sigBytes(a2).r).add(T8)), s: sigBytes(a2).s })));
await refused(G4, 'S + L (the malleated twin)', 'runtime', /Curve25519Scalar|type error/i, () => rotate(sim, k2, withSig(a2, { r: sigBytes(a2).r, s: sigBytes(a2).s + ED25519_L })));
await refused(G4, 'S + L at the client (never reduced)', 'client', /not below L/, () => {
  const raw = new Uint8Array([...ed25519.Point.fromAffine(sigBytes(a2).r).toBytes(), ...(() => { const o = new Uint8Array(32); let x = sigBytes(a2).s + ED25519_L; for (let i = 0; i < 32; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; })()]);
  return decodeSolSignature(raw);
});
await refused(G4, 'a flipped S bit', 'runtime', /invalid signature/, () => rotate(sim, k2, withSig(a2, { r: sigBytes(a2).r, s: sigBytes(a2).s ^ 1n })));
// The honest call still lands afterwards: the refusals changed nothing.
await rotate(sim, k2, a2);
const end = ledgerOf(sim.state);
ok(G4, 'after every refusal the honest call lands (state untouched by the refusals)', hex(end.enc_key) === hex(k2) && end.auth_nonce === 2n
  && end.devices.member(devA.entryAt(sim.bytes, end.device_epoch, 2n)));


const failed = cases.filter((c) => c.verdict !== 'PASS');
for (const g of [...new Set(cases.map((c) => c.group))]) {
  const cs = cases.filter((c) => c.group === g);
  console.log(`  ${cs.every((c) => c.verdict === 'PASS') ? '✓' : '✗'} ${g}: ${cs.filter((c) => c.verdict === 'PASS').length}/${cs.length}`);
}
const verdict = failed.length ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(path.join(process.env.EVIDENCE_DIR, 'sol-ed25519-seam-offline.json'), JSON.stringify({ suite: 'sol-ed25519-seam-offline', ranAt: new Date().toISOString(), cases, verdict }, null, 2) + '\n');
}
console.log(`\n◆ sol-ed25519-seam-offline: ${verdict} (${cases.length} cases, ${failed.length} failed)`);
process.exit(verdict === 'PASS' ? 0 : 1);
