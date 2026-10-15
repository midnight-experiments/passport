// Arm `sol_ed25519`: scoped grants, offline (the generated JavaScript, no
// proof server, no node). Upstream's grants-offline / grants-caller-offline
// matrices, extended in this new file (upstream's suites are untouched):
//
//   1 issue      a sol_ed25519 owner issues to a grantee of every scheme
//                (sol_ed25519, evm_eip712, k256 and JubJub with the Q17
//                labelled origin hash, a passkey with its origin); each grant
//                id equals the grantee scheme's own derivation; the record
//                (issued_at = auth_nonce, nonce 0, read_pk_hash = SHA-256 of
//                the shown read key);
//   2 rules      the arm's issue rules under a valid signature (a read key
//                without read, read without a key, an RP hash on a
//                non-passkey grantee), the grantee's point (Q37), the shared
//                chip's rules reached through the arm;
//   3 binding    every shown scope field and grantee field changed at
//                execution (consistent display inputs): the signature refuses;
//   4 twins      a sol_ed25519 grantee under its grant: in-scope unshielded
//                and shielded spends (the change entry appended), never
//                touching auth_nonce or a device entry; refused outside the
//                scope (per-call cap, cap, recipient pin, colour, max coin
//                value, stale encryption key, expiry, revoked, revoke-all),
//                the replayed approval, witness substitution (colour);
//   5 roles      cross-role replay (audit G1(S) G1S-3): the same key's
//                device-role approval presented to the grant seam, its
//                grantee-role approval presented to the device seam;
//   6 owners     upstream jubjub and k256 owners issue to a sol_ed25519
//                grantee (grant id from derive_grant_id_with_sol_ed25519),
//                which spends under them;
//   7 caller     the #176 caller pin: refused without a contract caller and
//                with another, lands with the pinned one (callers injected
//                into the simulator, as upstream's grants-caller-offline);
//   8 blind      Q39: a grantee blind never equals the same wallet's device
//                blind, and differs per issuing account.
//
// Writes $EVIDENCE_DIR/sol-ed25519-grants-offline.json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { randomBytes } from 'node:crypto';
import { sha256 } from '@noble/hashes/sha2.js';
import { createCallContext, createCircuitContext, createConstructorContext, sampleContractAddress, type PublicAddress } from '@midnight-ntwrk/compact-runtime';

import { Contract, ledger, pureCircuits } from '../wallet/contract.js';
import { makeWitnesses, emptyCoinStore, withCoin } from '../wallet/witnesses.js';
import {
  JubjubDevice, JubjubGrantee, K256Grantee, authArgs, grantAuthArgs, jubjubChallenges, jubjubGrantChallenges, k256GrantChallenges,
  originHash, scopeArgs, scopeDigest, spendScope, type GrantOpening,
} from '../wallet/signer.js';
import { DESCRIPTOR_TAGS, grantOriginHash, padTag } from '../wallet/descriptors.js';
import {
  SolEd25519Device, SolEd25519Grantee, authoriseSolDevice, authoriseSolGrantee, deriveSolBlind, deriveSolGranteeBlind, solDeviceMessageCircuit,
  solGranteeMessageCircuit, solGranteeOf, solSoftwareSigner, type SolEd25519Authorisation, type SolEd25519GrantAuthorisation, type SolIssueScope,
} from '../wallet/signer-sol-ed25519.js';
import { solGranteeArg, solTargetPoint, solTargetPointArg, labelBytes, type SolAmount, type SolGranteeFields } from '../wallet/sol-ed25519-message.js';
import { softwarePasskey } from './p256-fixtures.js';

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
const rnd = (n = 32) => new Uint8Array(randomBytes(n));
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const eq = (a: Uint8Array, b: Uint8Array) => hex(a) === hex(b);
const SITE = 'Grants test';
const Z32 = new Uint8Array(32);

// ── a sol_ed25519-owned account in the simulator ─────────────────────────────
class Sim {
  contract = new (Contract as any)(makeWitnesses());
  addressHex = sampleContractAddress();
  bytes = new Uint8Array(Buffer.from(this.addressHex.replace(/^0x/, ''), 'hex'));
  coinPk = { bytes: rnd() };
  state: any; ps: any = emptyCoinStore(); now = 1_800_000_000;
  constructor(readonly owner: SolEd25519Device) {}
  static async create(owner: SolEd25519Device) {
    const s = new Sim(owner);
    const salt = rnd();
    const init = await s.contract.initialState(createConstructorContext(s.ps, s.coinPk), owner.bootCommitment(salt), rnd(), JubjubDevice.generate().pk, new Uint8Array(64), 259200n);
    s.state = init.currentContractState;
    await s.call('activate_initial_device_with_sol_ed25519', ...owner.activationArgs(salt));
    return s;
  }
  async call(circuit: string, ...args: unknown[]) { return this.callAs(undefined, circuit, ...args); }
  async callAs(caller: PublicAddress | undefined, circuit: string, ...args: unknown[]) {
    const ctx = createCircuitContext({ circuitId: circuit, contractAddress: this.addressHex, coinPublicKeyOrZswapState: this.coinPk, contractState: this.state, privateState: this.ps, time: this.now } as any);
    if (caller) {
      ctx.callContext = createCallContext(circuit, this.addressHex, this.coinPk, this.state, this.ps, this.now, undefined, caller) as any;
      (ctx as any).queryContexts[this.addressHex] = ctx.callContext.currentQueryContext;
    }
    const r = await this.contract.impureCircuits[circuit](ctx, ...args);
    this.state = r.context.callContext.currentQueryContext.state;
    if (r.context.callContext.currentPrivateState !== undefined) this.ps = r.context.callContext.currentPrivateState;
    return r.result;
  }
  L() { return ledger(this.state); }
  ctx() { return { contractAddress: this.bytes, authNonce: this.L().auth_nonce as bigint }; }
  counter(d = this.owner) { const l = this.L(); for (let k = 0n; k < 64n; k++) if (l.devices.member(d.entryAt(this.bytes, l.device_epoch, k))) return k; throw new Error('no entry'); }
  auth(o: any, d = this.owner) { return authoriseSolDevice(d, this.ctx(), SITE, o, this.counter(d)); }
  shown(o: any, d = this.owner) { return solDeviceMessageCircuit(d.key, this.ctx(), SITE, o).showArgs; }
  snapshot() { return { state: this.state, ps: this.ps, now: this.now }; }
  restore(s: any) { this.state = s.state; this.ps = s.ps; this.now = s.now; }
}
const newDevice = async () => { const s = solSoftwareSigner(rnd()); return { signer: s, dev: SolEd25519Device.fromSigner(s, await deriveSolBlind(s, { network: 'undeployed', accountIndex: 0 })) }; };
const caller = (bytes: Uint8Array): PublicAddress => ({ tag: 'contract', address: hex(bytes) } as PublicAddress);

const issueArgs = (g: SolGranteeFields, sc: SolIssueScope, salt: Uint8Array, a: SolEd25519Authorisation, pk: unknown = solTargetPointArg(g), garg: unknown = solGranteeArg(g)) => [
  garg, pk, sc.opWithdrawUnshielded, sc.opWithdrawShielded, sc.opWithdrawShieldedToContract, sc.read, sc.color, sc.recipientKind, sc.recipient,
  sc.maxCoinValue, sc.perCallCap, sc.cap, sc.expiresAt, sc.rpIdHash, sc.readPk, sc.windowLen, sc.windowCap,
  { is_some: sc.caller !== null, value: { bytes: sc.caller ?? Z32 } }, salt, ...authArgs(a)];
const issue = async (sim: Sim, g: SolGranteeFields, sc: SolIssueScope, salt: Uint8Array) =>
  sim.call('issue_grant_with_sol_ed25519', ...issueArgs(g, sc, salt, await sim.auth({ op: 'issue_grant', grantee: g, ...sc })));
const baseScope = (o: Partial<SolIssueScope> = {}): SolIssueScope => ({
  opWithdrawUnshielded: true, opWithdrawShielded: false, opWithdrawShieldedToContract: false, read: false, color: rnd(), recipientKind: 0n,
  recipient: Z32, maxCoinValue: 500n, perCallCap: 300n, cap: 500n, expiresAt: 0n, rpIdHash: Z32, readPk: Z32, windowLen: 0n, windowCap: 0n, caller: null, ...o,
});
// The plain scope upstream's helpers take (read_pk as its hash).
const plain = (sc: SolIssueScope) => ({ ...sc, readPkHash: sc.read ? sha256(sc.readPk) : Z32, caller: sc.caller ?? undefined });

const owner = await newDevice();
const sim = await Sim.create(owner.dev);
const gSigner = solSoftwareSigner(rnd());
const G = await SolEd25519Grantee.enrol(gSigner, { network: 'undeployed', issuingAccount: sim.bytes }, 'Example dApp');

// ── 1. issue to every grantee scheme ───────────────────────────────────────
const G1 = '1 issue';
const k1 = K256Grantee.generate(), jg = JubjubGrantee.generate(), pass = softwarePasskey();
const evmAddr = rnd(20), evmBlind = rnd();
const ohK = originHash('https://k.example'), ohJ = originHash('https://j.example');
const origin21 = pass.policy.origin;
const grantees: [string, SolGranteeFields, () => Uint8Array][] = [
  ['sol_ed25519', G.grantee(0n), () => G.grantId(sim.bytes, 0n)],
  ['evm_eip712', solGranteeOf({ scheme: 'evm_eip712', address: evmAddr, blind: evmBlind }, { label: 'Example dApp' }, 1n),
    () => sha256(new Uint8Array([...padTag(DESCRIPTOR_TAGS['grant-id'].evm_eip712), ...sim.bytes, ...evmAddr, ...evmBlind, ...grantOriginHash(labelBytes('Example dApp')), 1]))],
  ['k256', solGranteeOf({ scheme: 'k256', x: k1.pk.x, y: k1.pk.y, envelope: 0 }, { originHash: ohK }, 2n), () => k1.grantId(sim.bytes, ohK, 2n)],
  ['jubjub', solGranteeOf({ scheme: 'jubjub', x: jg.pk.x, y: jg.pk.y }, { originHash: ohJ }, 3n), () => jg.grantId(sim.bytes, ohJ, 3n)],
  ['p256', solGranteeOf({ scheme: 'p256', x: pass.pk.x, y: pass.pk.y }, { origin: origin21 }, 4n), () => pass.grantee.grantId(sim.bytes, grantOriginHash(origin21), 4n)],
];
for (const [scheme, g, idOf] of grantees) {
  const readPk = rnd();
  const sc = baseScope({ read: true, readPk, rpIdHash: scheme === 'p256' ? pass.policy.rp_id_hash : Z32 });
  const nonce = sim.L().auth_nonce;
  const a = await sim.auth({ op: 'issue_grant', grantee: g, ...sc });
  ok(G1, `${scheme}: the message (1673 bytes) shows the consequence and the grantee scheme`, a.message.length === 1673
    && a.text.includes('Consequence: lets the grantee key below spend from this account within these limits.\n') && a.text.includes(`Grantee scheme: ${DESCRIPTOR_TAGS['grant-id'][scheme as 'k256']}`));
  await sim.call('issue_grant_with_sol_ed25519', ...issueArgs(g, sc, rnd(), a));
  const id = idOf();
  const l = sim.L();
  const rec = l.grants.member(id) ? l.grants.lookup(id) : null;
  ok(G1, `${scheme}: the grant id equals the ${scheme} grant-id recipe; issued_at = the auth_nonce after the issuing call, nonce 0, read_pk_hash = SHA-256(read key)`,
    !!rec && rec.issued_at === nonce + 1n && rec.nonce === 0n && rec.active && eq(rec.scope.read_pk_hash, sha256(readPk)),
    rec ? `issued_at ${rec.issued_at} (nonce before ${nonce}), nonce ${rec.nonce}, active ${rec.active}` : 'no record');
}

// ── 2. issue rules under a valid signature ─────────────────────────────────
const G2 = '2 rules';
{
  const g = G.grantee(5n);
  const bad = async (name: string, sc: SolIssueScope, re: RegExp, pk?: unknown, gg: SolGranteeFields = g) =>
    refused(G2, name, 'runtime', re, async () => sim.call('issue_grant_with_sol_ed25519', ...issueArgs(gg, sc, rnd(), await sim.auth({ op: 'issue_grant', grantee: gg, ...sc }), pk)));
  await bad('a read key without read', baseScope({ readPk: rnd() }), /a read key without read/);
  await bad('read without a read key', baseScope({ read: true }), /read without a read key/);
  await bad('an RP hash on a non-passkey grantee', baseScope({ rpIdHash: rnd() }), /RP hash belongs to a passkey grantee/);
  await bad('Q37: a sol grantee whose point is another key', baseScope(), /not the point's encoding/, solTargetPoint((await newDevice()).dev.key));
  await bad('Q37: a k256 grantee with a non-identity point', baseScope(), /unused point must be the identity/, solTargetPoint(G.key), { ...grantees[2][1], slot: 9n });
  await bad('the shared chip through the arm: per-call cap above cap', baseScope({ perCallCap: 600n }), /per-call cap above cap/);
  await bad('the shared chip through the arm: spend without cap', baseScope({ cap: 0n, perCallCap: 0n, maxCoinValue: 0n }), /spend without cap/);
  await bad('the shared chip through the arm: shielded spend without read', baseScope({ opWithdrawShielded: true }), /shielded spend requires read/);
  await bad('the shared chip through the arm: an empty scope', baseScope({ opWithdrawUnshielded: false }), /empty scope/);
  ok(G2, 'nothing was issued at slot 5', !sim.L().grants.member(G.grantId(sim.bytes, 5n)));
}

// ── 3. binding: a shown field changed at execution ─────────────────────────
const G3 = '3 binding';
{
  const g = G.grantee(6n);
  const sc = baseScope({ read: true, readPk: rnd(), recipientKind: 1n, recipient: rnd(), expiresAt: 1_900_000_000n });
  const a = await sim.auth({ op: 'issue_grant', grantee: g, ...sc });
  const exec = (eg: SolGranteeFields, esc: SolIssueScope) => sim.call('issue_grant_with_sol_ed25519',
    ...issueArgs(eg, esc, rnd(), { ...a, showArgs: sim.shown({ op: 'issue_grant', grantee: eg, ...esc }) }));
  const flip = (b: Uint8Array) => { const o = new Uint8Array(b); o[0] ^= 1; return o; };
  const fields: [string, Partial<SolIssueScope>][] = [
    ['withdraw unshielded flag', { opWithdrawUnshielded: false, opWithdrawShieldedToContract: true }], ['read flag (and key)', { read: false, readPk: Z32 }],
    ['token', { color: rnd() }], ['recipient kind', { recipientKind: 2n }], ['recipient', { recipient: rnd() }], ['max coin value', { maxCoinValue: 501n }],
    ['per-call cap', { perCallCap: 299n }], ['cap', { cap: 499n }], ['expiry', { expiresAt: 1_900_000_001n }], ['read key', { readPk: rnd() }],
    ['caller pin', { caller: rnd() }],
  ];
  for (const [name, d] of fields) await refused(G3, `issue_grant: the ${name} changed at execution`, 'runtime', /invalid signature/, () => exec(g, { ...sc, ...d }));
  await refused(G3, 'issue_grant: the grantee slot changed', 'runtime', /invalid signature/, () => exec({ ...g, slot: 7n }, sc));
  await refused(G3, 'issue_grant: the grantee label changed', 'runtime', /invalid signature/, () => exec({ ...g, label: 'Other dApp' }, sc));
  await refused(G3, 'issue_grant: the grantee key changed (another valid key)', 'runtime', /invalid signature/, async () => exec({ ...g, a: (await newDevice()).dev.key }, sc));
  await refused(G3, 'issue_grant: the grantee privacy salt changed', 'runtime', /invalid signature/, () => exec({ ...g, b: flip(g.b!) }, sc));
  const gk = grantees[2][1];
  const ak = await sim.auth({ op: 'issue_grant', grantee: gk, ...sc });
  await refused(G3, 'issue_grant: the Q17 labelled origin hash of a k256 grantee changed', 'runtime', /invalid signature/, () => sim.call('issue_grant_with_sol_ed25519',
    ...issueArgs({ ...gk, originHash: flip(gk.originHash!) }, sc, rnd(), { ...ak, showArgs: sim.shown({ op: 'issue_grant', grantee: { ...gk, originHash: flip(gk.originHash!) }, ...sc }) })));
  await refused(G3, 'issue_grant: the k256 grantee envelope changed', 'runtime', /invalid signature/, () => sim.call('issue_grant_with_sol_ed25519',
    ...issueArgs({ ...gk, envelope: 1n }, sc, rnd(), { ...ak, showArgs: sim.shown({ op: 'issue_grant', grantee: { ...gk, envelope: 1n }, ...sc }) })));
  // revoke_grant: another grantee executed under the signature for G's slot 0
  const ar = await sim.auth({ op: 'revoke_grant', grantee: G.grantee(0n) });
  await refused(G3, 'revoke_grant: another slot executed', 'runtime', /invalid signature/, () =>
    sim.call('revoke_grant_with_sol_ed25519', solGranteeArg(G.grantee(1n)), solTargetPointArg(G.grantee(1n)), ...authArgs({ ...ar, showArgs: sim.shown({ op: 'revoke_grant', grantee: G.grantee(1n) }) })));
}

// ── 4. a sol grantee under its grant ───────────────────────────────────────
const G4 = '4 twins';
const twinSim = await Sim.create(owner.dev);
const T = await SolEd25519Grantee.enrol(gSigner, { network: 'undeployed', issuingAccount: twinSim.bytes }, 'Example dApp');
const U = rnd();
await twinSim.call('deposit_unshielded', U, 1000n);
const pin = rnd();
const salt = rnd();
const scU = baseScope({ color: U, recipientKind: 1n, recipient: pin, perCallCap: 300n, cap: 500n, maxCoinValue: 500n, expiresAt: 1_900_000_000n });
await issue(twinSim, T.grantee(0n), scU, salt);
const opening = (spentPrev: bigint, sc = scU, s = salt, slot = 0n): GrantOpening => ({ originHash: grantOriginHash(labelBytes(T.label)), slot, scopeSalt: s,
  recipientKind: sc.recipientKind, pinnedRecipient: sc.recipient, maxCoinValue: sc.maxCoinValue, spentPrev });
const gctx = (s: Sim, g = T, slot = 0n) => { const id = g.grantId(s.bytes, slot); const r = s.L().grants.lookup(id); return { contractAddress: s.bytes, label: g.label, slot, issuedAt: r.issued_at, grantNonce: r.nonce }; };
const amt = (n: bigint, color = U): SolAmount => ({ color, amount: n, decimals: 0, symbol: 'tU' });
const unsh = async (s: Sim, n: bigint, to: Uint8Array, spent: bigint, a?: SolEd25519GrantAuthorisation, o = opening(spent)) => {
  const au = a ?? await authoriseSolGrantee(T.device, gctx(s), SITE, { op: 'withdraw_unshielded_with_grant', amount: amt(n), recipient: to });
  return s.call('withdraw_unshielded_with_grant_sol_ed25519', U, n, { bytes: to }, ...grantAuthArgs(o, au));
};
{
  const before = twinSim.L();
  const a1 = await authoriseSolGrantee(T.device, gctx(twinSim), SITE, { op: 'withdraw_unshielded_with_grant', amount: amt(200n), recipient: pin });
  ok(G4, 'the grantee message (746 bytes) shows the grant label, slot, issued-at nonce and use nonce', a1.message.length === 746
    && a1.text.includes('Role: grantee of a scoped grant\n') && a1.text.includes('Grant label: Example dApp') && a1.text.includes('Grant use nonce: 0'));
  await unsh(twinSim, 200n, pin, 0n, a1);
  const after = twinSim.L();
  const rec = after.grants.lookup(T.grantId(twinSim.bytes, 0n));
  ok(G4, 'in scope: lands; the record nonce +1; auth_nonce and the device entries untouched (FR-008)', rec.nonce === 1n && after.auth_nonce === before.auth_nonce
    && JSON.stringify([...after.devices]) === JSON.stringify([...before.devices]) && after.unshielded_balances.lookup(U) === 800n);
  await refused(G4, 'replay of the landed approval verbatim (the spent opening moved)', 'runtime', /spent opening mismatch/, () => unsh(twinSim, 200n, pin, 0n, a1));
  await refused(G4, 'replay of the landed approval with the current opening and display inputs for the current nonce (stale grant nonce)', 'runtime', /invalid grant signature/, () =>
    unsh(twinSim, 200n, pin, 200n, { ...a1, showArgs: solGranteeMessageCircuit(T.key, gctx(twinSim), SITE, { op: 'withdraw_unshielded_with_grant', amount: amt(200n), recipient: pin }).showArgs }));
  await refused(G4, 'replay of the landed approval with the current opening (its nonce digits no longer match)', 'runtime', /digits do not match/, () => unsh(twinSim, 200n, pin, 200n, a1));
  await refused(G4, 'above the per-call cap (301)', 'runtime', /per-call cap/, () => unsh(twinSim, 301n, pin, 200n));
  await refused(G4, 'above the cumulative cap (200 + 301 > 500)', 'runtime', /per-call cap|cumulative cap/, () => unsh(twinSim, 301n, pin, 200n));
  await unsh(twinSim, 250n, pin, 200n);
  await refused(G4, 'the cumulative cap (450 + 100 > 500)', 'runtime', /cumulative cap exceeded/, () => unsh(twinSim, 100n, pin, 450n));
  await refused(G4, 'another recipient than the pin', 'runtime', /recipient not admitted by pin/, () => unsh(twinSim, 10n, rnd(), 450n));
  await refused(G4, 'a wrong opening (spent so far)', 'runtime', /spent opening mismatch/, () => unsh(twinSim, 10n, pin, 0n));
  await refused(G4, 'the grantee shows another label (another grant id)', 'runtime', /unknown grant/, async () => {
    const other = new SolEd25519Grantee(T.device, 'Other dApp');
    const au = await authoriseSolGrantee(other.device, { ...gctx(twinSim), label: 'Other dApp' }, SITE, { op: 'withdraw_unshielded_with_grant', amount: amt(10n), recipient: pin });
    return twinSim.call('withdraw_unshielded_with_grant_sol_ed25519', U, 10n, { bytes: pin }, ...grantAuthArgs(opening(450n), au));
  });
  await refused(G4, 'a device blind instead of the grantee blind (Q39)', 'runtime', /unknown grant/, async () => {
    const asDevice = SolEd25519Device.fromSigner(gSigner, await deriveSolBlind(gSigner, { network: 'undeployed', accountIndex: 0 }));
    const au = await authoriseSolGrantee(asDevice, gctx(twinSim), SITE, { op: 'withdraw_unshielded_with_grant', amount: amt(10n), recipient: pin });
    return twinSim.call('withdraw_unshielded_with_grant_sol_ed25519', U, 10n, { bytes: pin }, ...grantAuthArgs(opening(450n), au));
  });
  const snap = twinSim.snapshot();
  twinSim.now = 1_900_000_001;
  await refused(G4, 'after its expiry', 'runtime', /grant expired/, () => unsh(twinSim, 10n, pin, 450n));
  twinSim.restore(snap);
  // shielded: a grant scoped to colour A with a read key
  const A = rnd(), B = rnd(), nonceH = rnd();
  const scS = baseScope({ opWithdrawUnshielded: false, opWithdrawShielded: true, read: true, readPk: rnd(), color: A, perCallCap: 400n, cap: 400n, maxCoinValue: 1000n });
  const saltS = rnd();
  await issue(twinSim, T.grantee(1n), scS, saltS);
  const coin = { nonce: nonceH, color: A, value: 1000n, mtIndex: 3n };
  twinSim.ps = withCoin(emptyCoinStore(), coin);
  const encPk = twinSim.L().enc_key;
  const to = rnd();
  const sOpen = (spent: bigint, sc = scS): GrantOpening => ({ ...opening(spent, sc, saltS, 1n) });
  const shArgs = async (n: bigint, change: Uint8Array, enc = encPk, c = coin) => {
    const au = await authoriseSolGrantee(T.device, gctx(twinSim, T, 1n), SITE, { op: 'withdraw_shielded_with_grant', amount: amt(n, A), recipient: to, changeEntry: change, encPk: enc,
      coin: { nonce: c.nonce, color: c.color, value: c.value, mt_index: c.mtIndex } });
    return [{ bytes: to }, A, n, change, enc, ...grantAuthArgs(sOpen(0n), au)];
  };
  const change = rnd(192);
  const snapS = twinSim.snapshot();
  // witness substitution first, from the state before any shielded spend
  {
    const args = await shArgs(300n, change);
    twinSim.ps = { ...emptyCoinStore(), coins: { [hex(A)]: { nonceHex: hex(nonceH), colorHex: hex(B), value: '1000', mtIndex: '3' } } };
    await refused(G4, 'witness substitution: colour B for an approval of colour A', 'runtime', /held coin colour does not match/, () =>
      twinSim.call('withdraw_shielded_with_grant_sol_ed25519', ...args));
    twinSim.restore(snapS);
    twinSim.ps = withCoin(emptyCoinStore(), coin);
  }
  const inboxBefore = twinSim.L().inbox_count;
  const sAuthBefore = twinSim.L().auth_nonce;
  const r: any = await twinSim.call('withdraw_shielded_with_grant_sol_ed25519', ...(await shArgs(300n, change)));
  ok(G4, 'shielded twin in scope: 300 of the 1000 coin, the change entry appended, auth_nonce untouched', r?.is_some === true && r.value.value === 700n
    && twinSim.L().inbox_count === inboxBefore + 1n && eq(twinSim.L().inbox.lookup(inboxBefore), change) && twinSim.L().auth_nonce === sAuthBefore);
  twinSim.ps = withCoin(emptyCoinStore(), { ...coin, value: 2000n });
  await refused(G4, 'a coin above the max coin value (2000 > 1000)', 'runtime', /coin above max_coin_value/, async () => {
    const au = await authoriseSolGrantee(T.device, gctx(twinSim, T, 1n), SITE, { op: 'withdraw_shielded_with_grant', amount: amt(10n, A), recipient: to, changeEntry: change, encPk,
      coin: { nonce: nonceH, color: A, value: 2000n, mt_index: 3n } });
    return twinSim.call('withdraw_shielded_with_grant_sol_ed25519', { bytes: to }, A, 10n, change, encPk, ...grantAuthArgs(sOpen(300n), au));
  });
  twinSim.ps = withCoin(emptyCoinStore(), coin);
  await refused(G4, 'a stale encryption key', 'runtime', /stale encryption key/, async () => twinSim.call('withdraw_shielded_with_grant_sol_ed25519', ...(await shArgs(10n, change, rnd()))));
  // an approval built now (opening at 300), executed after revoke_all_grants
  const late = await (async () => {
    const au = await authoriseSolGrantee(T.device, gctx(twinSim, T, 1n), SITE, { op: 'withdraw_shielded_with_grant', amount: amt(10n, A), recipient: to, changeEntry: change, encPk,
      coin: { nonce: coin.nonce, color: A, value: coin.value, mt_index: coin.mtIndex } });
    return [{ bytes: to }, A, 10n, change, encPk, ...grantAuthArgs(sOpen(300n), au)];
  })();
  // revoke by descriptor, then revoke-all
  const rv = await twinSim.auth({ op: 'revoke_grant', grantee: T.grantee(0n) });
  await twinSim.call('revoke_grant_with_sol_ed25519', solGranteeArg(T.grantee(0n)), solTargetPointArg(T.grantee(0n)), ...authArgs(rv));
  ok(G4, 'revoke_grant by descriptor: the record is inactive', twinSim.L().grants.lookup(T.grantId(twinSim.bytes, 0n)).active === false);
  await refused(G4, 'after revoke_grant', 'runtime', /grant revoked/, () => unsh(twinSim, 10n, pin, 450n));
  const gen = twinSim.L().grant_generation;
  await twinSim.call('revoke_all_grants_with_sol_ed25519', ...authArgs(await twinSim.auth({ op: 'revoke_all_grants' })));
  ok(G4, 'revoke_all_grants: generation +1', twinSim.L().grant_generation === gen + 1n);
  await refused(G4, 'the shielded grant after revoke_all_grants (an approval made before it)', 'runtime', /unknown grant|grant generation stale/, () => twinSim.call('withdraw_shielded_with_grant_sol_ed25519', ...late));
}

// ── 5. cross-role replay (G1S-3) ───────────────────────────────────────────
const G5 = '5 roles';
{
  // One wallet as a device of account R and as a grantee of R (another blind).
  const w = await newDevice();
  const R = await Sim.create(w.dev);
  const Ug = await SolEd25519Grantee.enrol(w.signer, { network: 'undeployed', issuingAccount: R.bytes }, 'Example dApp');
  const U2 = rnd();
  await R.call('deposit_unshielded', U2, 1000n);
  const sc = baseScope({ color: U2 });
  const s2 = rnd();
  await issue(R, Ug.grantee(0n), sc, s2);
  const to = rnd();
  const op = (n: bigint): GrantOpening => ({ originHash: grantOriginHash(labelBytes(Ug.label)), slot: 0n, scopeSalt: s2, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: 500n, spentPrev: 0n });
  const grCtx = { contractAddress: R.bytes, label: Ug.label, slot: 0n, issuedAt: R.L().grants.lookup(Ug.grantId(R.bytes, 0n)).issued_at, grantNonce: 0n };
  const gAuth = await authoriseSolGrantee(Ug.device, grCtx, SITE, { op: 'withdraw_unshielded_with_grant', amount: { color: U2, amount: 100n, decimals: 0, symbol: 'tU' }, recipient: to });
  // the device-role approval of the same withdrawal by the same key
  const dAuth = await R.auth({ op: 'withdraw_unshielded', amount: { color: U2, amount: 100n, decimals: 0, symbol: 'tU' }, recipient: to }, w.dev);
  await refused(G5, 'the device-role approval (same key, same withdrawal) presented to the grant seam', 'runtime', /invalid grant signature/, () =>
    R.call('withdraw_unshielded_with_grant_sol_ed25519', U2, 100n, { bytes: to }, ...grantAuthArgs(op(0n), { ...gAuth, sig: dAuth.sig })));
  await refused(G5, 'the grantee-role approval (same key, same withdrawal) presented to the device seam', 'runtime', /invalid signature/, () =>
    R.call('withdraw_unshielded_with_sol_ed25519', U2, 100n, { bytes: to }, ...authArgs({ ...dAuth, sig: gAuth.sig })));
  ok(G5, 'the two roles render different messages (the Role line and the tail differ)', !eq(gAuth.message, dAuth.message)
    && gAuth.text.includes('Role: grantee of a scoped grant') && dAuth.text.includes('Role: device of this account'));
  await R.call('withdraw_unshielded_with_grant_sol_ed25519', U2, 100n, { bytes: to }, ...grantAuthArgs(op(0n), gAuth));
  ok(G5, 'positive control: the grantee approval lands under the grant', R.L().unshielded_balances.lookup(U2) === 900n);
}

// ── 6. upstream owners issue to a sol_ed25519 grantee ──────────────────────
const G6 = '6 upstream owners';
{
  const { AccountSim } = await import('./sim.js');
  const js = await AccountSim.create({ initialRecoveryPk: JubjubDevice.generate().pk, initialWrap: rnd(64), vetoWindowSeconds: 60n });
  const Ux = await SolEd25519Grantee.enrol(gSigner, { network: 'undeployed', issuingAccount: js.address }, 'Example dApp');
  const oh = grantOriginHash(labelBytes(Ux.label));
  const id = Ux.grantId(js.address, 0n);
  ok(G6, 'the sol grant id: derive_grant_id_with_sol_ed25519 == SHA-256 of the spec preimage',
    eq(id, sha256(new Uint8Array([...padTag(DESCRIPTOR_TAGS['grant-id'].sol_ed25519), ...js.address, ...Ux.key, ...Ux.blind, ...oh, 0]))));
  const U3 = rnd();
  await js.call('deposit_unshielded', U3, 1000n);
  const scope = spendScope({ withdrawUnshielded: true, color: U3, cap: 300n });
  const s3 = rnd();
  await js.authorised('issue_grant', (c, d) => jubjubChallenges.issueGrant(c, d.pk, id, scopeDigest(s3, scope)), [id, ...scopeArgs(scope), s3]);
  const rec = js.ledger().grants.lookup(id);
  const to = rnd();
  const au = await authoriseSolGrantee(Ux.device, { contractAddress: js.address, label: Ux.label, slot: 0n, issuedAt: rec.issued_at, grantNonce: 0n }, SITE,
    { op: 'withdraw_unshielded_with_grant', amount: { color: U3, amount: 120n, decimals: 0, symbol: 'tU' }, recipient: to });
  await js.call('withdraw_unshielded_with_grant_sol_ed25519', U3, 120n, { bytes: to },
    ...grantAuthArgs({ originHash: oh, slot: 0n, scopeSalt: s3, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: 300n, spentPrev: 0n }, au));
  ok(G6, 'a jubjub owner issues to a sol grantee; it spends 120 under the grant', js.ledger().unshielded_balances.lookup(U3) === 880n && js.ledger().grants.lookup(id).nonce === 1n);
  // the reverse: a sol owner's grant to a jubjub grantee spent through upstream's jubjub twin
  const owner2 = await newDevice();
  const so = await Sim.create(owner2.dev);
  const U4 = rnd();
  await so.call('deposit_unshielded', U4, 1000n);
  const jgr = JubjubGrantee.generate();
  const ohj = originHash('https://j.example');
  const gj = solGranteeOf({ scheme: 'jubjub', x: jgr.pk.x, y: jgr.pk.y }, { originHash: ohj }, 0n);
  const sc4 = baseScope({ color: U4, cap: 300n, perCallCap: 300n, maxCoinValue: 300n });
  const s4 = rnd();
  await issue(so, gj, sc4, s4);
  const jid = jgr.grantId(so.bytes, ohj, 0n);
  const jr = so.L().grants.lookup(jid);
  const ja = jgr.sign(jubjubGrantChallenges.withdrawUnshielded({ contractAddress: so.bytes, grantId: jid, issuedAt: jr.issued_at, grantNonce: 0n }, jgr.pk, U4, 50n, to));
  await so.call('withdraw_unshielded_with_grant_jubjub', U4, 50n, { bytes: to }, ...grantAuthArgs({ originHash: ohj, slot: 0n, scopeSalt: s4, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: 300n, spentPrev: 0n }, ja));
  ok(G6, 'a sol owner issues to a jubjub grantee (Q17 label); it spends through upstream\'s jubjub twin', so.L().unshielded_balances.lookup(U4) === 950n);
  void k256GrantChallenges;
}

// ── 7. the caller pin (#176) ───────────────────────────────────────────────
const G7 = '7 caller pin';
{
  const owner3 = await newDevice();
  const cs = await Sim.create(owner3.dev);
  const Uc = await SolEd25519Grantee.enrol(gSigner, { network: 'undeployed', issuingAccount: cs.bytes }, 'Example dApp');
  const U5 = rnd();
  await cs.call('deposit_unshielded', U5, 1000n);
  const pinned = rnd();
  const sc = baseScope({ color: U5, caller: pinned });
  const s5 = rnd();
  const ia = await cs.auth({ op: 'issue_grant', grantee: Uc.grantee(0n), ...sc });
  ok(G7, 'the issue message shows the caller pin', ia.text.includes('Caller restricted to a contract: yes\nCaller: ' + hex(pinned)));
  await cs.call('issue_grant_with_sol_ed25519', ...issueArgs(Uc.grantee(0n), sc, s5, ia));
  const to = rnd();
  const callUnder = async (who: PublicAddress | undefined) => {
    const rec = cs.L().grants.lookup(Uc.grantId(cs.bytes, 0n));
    const au = await authoriseSolGrantee(Uc.device, { contractAddress: cs.bytes, label: Uc.label, slot: 0n, issuedAt: rec.issued_at, grantNonce: rec.nonce }, SITE,
      { op: 'withdraw_unshielded_with_grant', amount: { color: U5, amount: 10n, decimals: 0, symbol: 'tU' }, recipient: to });
    return cs.callAs(who, 'withdraw_unshielded_with_grant_sol_ed25519', U5, 10n, { bytes: to },
      ...grantAuthArgs({ originHash: grantOriginHash(labelBytes(Uc.label)), slot: 0n, scopeSalt: s5, recipientKind: 0n, pinnedRecipient: Z32, maxCoinValue: 500n, spentPrev: 0n }, au));
  };
  await refused(G7, 'no contract caller', 'runtime', /grant requires a contract caller/, () => callUnder(undefined));
  await refused(G7, 'a user caller', 'runtime', /grant requires a contract caller/, () => callUnder({ tag: 'user', address: hex(pinned) } as PublicAddress));
  await refused(G7, 'another contract', 'runtime', /grant caller mismatch/, () => callUnder(caller(rnd())));
  await callUnder(caller(pinned));
  ok(G7, 'the pinned contract caller: lands', cs.L().unshielded_balances.lookup(U5) === 990n);
}

// ── 8. the grantee blind (Q39) ─────────────────────────────────────────────
const G8 = '8 grantee blind';
{
  const w = solSoftwareSigner(rnd());
  const devBlinds = await Promise.all([0, 1, 2].map(async (i) => hex((await deriveSolBlind(w, { network: 'undeployed', accountIndex: i })).blind)));
  const accounts = [rnd(), rnd(), rnd()];
  const gBlinds = await Promise.all(accounts.map(async (acc) => hex(await deriveSolGranteeBlind(w, { network: 'undeployed', issuingAccount: acc }))));
  ok(G8, 'no grantee blind equals a device blind of the same wallet (3 issuing accounts × 3 account indexes)', gBlinds.every((g) => !devBlinds.includes(g)));
  ok(G8, 'grantee blinds differ per issuing account', new Set(gBlinds).size === 3);
  const again = hex(await deriveSolGranteeBlind(w, { network: 'undeployed', issuingAccount: accounts[0] }));
  ok(G8, 'and are re-derivable (deterministic)', again === gBlinds[0]);
  ok(G8, 'another network gives another grantee blind', hex(await deriveSolGranteeBlind(w, { network: 'preview', issuingAccount: accounts[0] })) !== gBlinds[0]);
}
// the client: an unregistered grantee scheme is refused before any message
await refused(G1, 'an unregistered grantee scheme: the facade refuses the descriptor (no message, no call)', 'client', /not a registered descriptor scheme \(zz\)/,
  () => solGranteeOf({ scheme: 'zz' } as any, { label: 'Example dApp' }, 0n));

const failed = cases.filter((c) => c.verdict !== 'PASS');
for (const gname of [...new Set(cases.map((c) => c.group))]) {
  const cs = cases.filter((c) => c.group === gname);
  console.log(`  ${cs.every((c) => c.verdict === 'PASS') ? '✓' : '✗'} ${gname}: ${cs.filter((c) => c.verdict === 'PASS').length}/${cs.length}`);
}
const verdict = failed.length ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(path.join(process.env.EVIDENCE_DIR, 'sol-ed25519-grants-offline.json'), JSON.stringify({ suite: 'sol-ed25519-grants-offline', ranAt: new Date().toISOString(), cases, verdict }, null, 2) + '\n');
}
console.log(`\n◆ sol-ed25519-grants-offline: ${verdict} (${cases.length} cases, ${failed.length} failed)`);
process.exit(verdict === 'PASS' ? 0 : 1);
