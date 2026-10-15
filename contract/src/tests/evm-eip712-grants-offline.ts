// Off-node grant matrices for the `evm_eip712` arm, through the
// compact-runtime local simulator (no node, no proof, no Zswap). They extend
// upstream's grants-offline.ts and grants-caller-offline.ts, which are left
// unchanged, to the new arm in both roles:
//
//   - the arm as OWNER: issue, revoke and revoke-all behind the evm_eip712
//     device seam, each grantee shown by its readable descriptor (FR-005,
//     FR-006), for k256, JubJub and evm_eip712 grantees;
//   - the arm as GRANTEE: withdraw_unshielded_with_grant_evm_eip712 under
//     evm_eip712, k256 and JubJub owners, signed as readable EIP-712 over the
//     grant frame (the record's issuedAt and nonce, never auth_nonce).
//
// Per pairing, upstream's matrix: the issue rules (and the arm's own: a read
// key only with read, an RP hash only for a passkey grantee), the caller pin
// stored and bound by the owner's signature, the record's fields, re-issue
// and revoke refusals, a read-only grant, one spend (record nonce +1, spent
// commitment, auth_nonce and every device entry untouched, round +1, mirror
// debited), the rejection matrix (stale nonce, per-call cap, cumulative cap,
// spent opening, recipient pin, recipient kind, scope salt, foreign key,
// out-of-scope operation), the grantee key against the device seam, expiry,
// the tombstone and re-issue, revoke-all and the new generation. For the
// evm_eip712 grantee also: a wrong blind, label or slot (another grant id),
// r = 0, and the device-role message type presented as a grantee approval.
//
// The caller pin (#176) as grants-caller-offline.ts drives it (callers
// injected into the simulator): a pinned grant refuses no caller, a user
// caller and another contract, and accepts the pinned contract; an
// unrestricted grant's transcript does not depend on the caller; the shared
// gate also dominates the evm_eip712 shielded twins.

import { createHash, randomBytes } from 'node:crypto';
import {
  createCallContext,
  createCircuitContext,
  createConstructorContext,
  sampleContractAddress,
  type PublicAddress,
} from '@midnight-ntwrk/compact-runtime';

import { Contract, ledger, pureCircuits } from '../wallet/contract.js';
import { hexToBytes } from '../wallet/hex.js';
import { makeWitnesses, emptyCoinStore, withCoin, type CoinStorePrivateState } from '../wallet/witnesses.js';
import {
  JubjubDevice, JubjubGrantee, K256Device, K256Grantee,
  jubjubChallenges, k256Challenges, jubjubGrantChallenges, k256GrantChallenges,
  authArgs, grantAuthArgs, scopeArgs, scopeDigest, originHash,
  RECIPIENT_USER_ADDRESS, RECIPIENT_ZSWAP_COIN_PUBLIC_KEY,
  type PlainScope, type GrantOpening, type GrantContext, type GrantAuthorisation,
} from '../wallet/signer.js';
import {
  SoftwareEvmWallet, EvmEip712Device, EvmEip712Grantee, evmEip712GranteeInput, evmEip712IssueArgs, parseEvmSignature,
  type EvmEip712GrantAuthorisation, solArg} from '../wallet/signer-evm-eip712.js';
import { evmEip712Messages, typedDataDigest, type IssueScope, type EvmEip712GranteeInput } from '../wallet/evm-eip712-codec.js';
import { grantLabel } from '../wallet/descriptors.js';

const rnd = (n = 32) => new Uint8Array(randomBytes(n));
const ZERO32 = new Uint8Array(32);
const eq = (a: Uint8Array, b: Uint8Array) => Buffer.from(a).equals(Buffer.from(b));
const sha256 = (b: Uint8Array) => new Uint8Array(createHash('sha256').update(b).digest());
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');

// ── Reporting (upstream's shape) ────────────────────────────────────────────

let pass = 0, fail = 0;
const failures: string[] = [];
function ok(condition: boolean, label: string) {
  if (condition) pass++; else { fail++; failures.push(label); console.log(`  ✗ ${label}`); }
}
async function expectAbort(label: string, f: () => Promise<unknown>, needle: string | string[]) {
  const needles = Array.isArray(needle) ? needle : [needle];
  try { await f(); ok(false, `${label} (NOT refused)`); }
  catch (e: any) {
    const m = String(e?.message ?? e);
    const hit = needles.some((n) => m.includes(n));
    ok(hit, `${label}${hit ? '' : ` (refused by "${m.slice(0, 160)}", expected ${needles.join(' | ')})`}`);
  }
}
const sections: { label: string; pass: number; fail: number }[] = [];
async function section(label: string, f: () => Promise<void>) {
  const p0 = pass, f0 = fail;
  console.log(`── ${label}`);
  try { await f(); } catch (e: any) { ok(false, `${label}: unexpected error ${String(e?.message ?? e).slice(0, 300)}`); }
  sections.push({ label, pass: pass - p0, fail: fail - f0 });
}

// ── Scope: one plaintext, both owner encodings ──────────────────────────────

/** The scope in the evm_eip712 owner's terms (the read key itself). */
type Scope = IssueScope;
const plain = (s: Scope): PlainScope => ({
  opWithdrawUnshielded: s.opWithdrawUnshielded, opWithdrawShielded: s.opWithdrawShielded,
  opWithdrawShieldedToContract: s.opWithdrawShieldedToContract, read: s.read, color: s.color,
  recipientKind: s.recipientKind, recipient: s.recipient, maxCoinValue: s.maxCoinValue, perCallCap: s.perCallCap,
  cap: s.cap, expiresAt: s.expiresAt, rpIdHash: s.rpIdHash, readPkHash: s.read ? sha256(s.readPk) : ZERO32,
  windowLen: s.windowLen, windowCap: s.windowCap, ...(s.caller ? { caller: s.caller } : {}),
});
const spendScope = (o: Partial<Scope>): Scope => ({
  opWithdrawUnshielded: false, opWithdrawShielded: false, opWithdrawShieldedToContract: false, read: false,
  color: ZERO32, recipientKind: 0n, recipient: ZERO32, maxCoinValue: 0n, perCallCap: 0n, cap: 0n, expiresAt: 0n,
  rpIdHash: ZERO32, readPk: ZERO32, windowLen: 0n, windowCap: 0n, caller: null, ...o,
});
const openingOf = (s: Scope, salt: Uint8Array, origin: Uint8Array, slot: bigint): GrantOpening => ({
  originHash: origin, slot, scopeSalt: salt, recipientKind: s.recipientKind, pinnedRecipient: s.recipient,
  maxCoinValue: s.maxCoinValue, spentPrev: 0n,
});

// ── Grantees ────────────────────────────────────────────────────────────────

type GranteeArm = 'k256' | 'jubjub' | 'evm_eip712';
interface Grantee {
  arm: GranteeArm;
  origin: Uint8Array;
  grantId(account: Uint8Array, slot: bigint): Uint8Array;
  /** As an evm_eip712 owner shows it. */
  descriptor(slot: bigint): EvmEip712GranteeInput;
  /** The unshielded twin's authorisation over `g` (a record's frame). */
  sign(g: GrantContext, slot: bigint, color: Uint8Array, amount: bigint, recipient: Uint8Array): Promise<GrantAuthorisation>;
  /** The grantee's key presented to the DEVICE seam of its own arm (it has
   *  no device entry): the circuit and its arguments for rotate_enc_key. */
  asDevice(account: Uint8Array, authNonce: bigint, newKey: Uint8Array): { circuit: string; args: unknown[] };
  /** evm_eip712 only: the key, for hand-built approvals. */
  evm?: { pk: any; blind: Uint8Array; address: Uint8Array; label: Uint8Array; wallet: SoftwareEvmWallet };
}
const BANK = 'https://bank.example';
/** A grantee key of `arm`; an evm_eip712 grantee derives its blind for the
 *  issuing account (the grantee request, Q39). */
async function makeGrantee(arm: GranteeArm, issuingAccount: Uint8Array): Promise<Grantee> {
  if (arm === 'k256') {
    const k = K256Grantee.generate();
    const origin = originHash(BANK);
    return { arm, origin, grantId: (a, slot) => k.grantId(a, origin, slot),
      descriptor: (slot) => evmEip712GranteeInput({ scheme: 'k256', x: k.pk.x, y: k.pk.y, envelope: 0 }, { originHash: origin, clientId: BANK }, slot),
      sign: async (g, _slot, c, amt, r) => k.sign(k256GrantChallenges.withdrawUnshielded(g, k.pk, c, amt, r)),
      asDevice: (account, authNonce, newKey) => {
        const a = k.sign(k256Challenges.rotateEncKey({ contractAddress: account, authNonce }, k.pk, newKey));
        return { circuit: 'rotate_enc_key_with_k256', args: [newKey, ...authArgs({ arm: 'k256', pk: a.pk, use_counter: 0n, sig: a.sig, envelope: a.envelope })] };
      } };
  }
  if (arm === 'jubjub') {
    const j = JubjubGrantee.generate();
    const origin = originHash(BANK);
    return { arm, origin, grantId: (a, slot) => j.grantId(a, origin, slot),
      descriptor: (slot) => evmEip712GranteeInput({ scheme: 'jubjub', x: j.pk.x, y: j.pk.y }, { originHash: origin, clientId: BANK }, slot),
      sign: async (g, _slot, c, amt, r) => j.sign(jubjubGrantChallenges.withdrawUnshielded(g, j.pk, c, amt, r)),
      asDevice: (account, authNonce, newKey) => {
        const a = j.sign(jubjubChallenges.rotateEncKey({ contractAddress: account, authNonce }, j.pk, newKey));
        return { circuit: 'rotate_enc_key_with_jubjub', args: [newKey, ...authArgs({ arm: 'jubjub', pk: a.pk, use_counter: 0n, sig_r: a.sig_r, sig_s: a.sig_s, grind_nonce: a.grind_nonce })] };
      } };
  }
  const label = grantLabel('bank.example');
  const wallet = SoftwareEvmWallet.generate();
  const base = await EvmEip712Grantee.enrol(wallet, 'undeployed', issuingAccount, label, 0n);
  const at = (slot: bigint) => new EvmEip712Grantee(base.pk, base.blind, label, slot, wallet);
  return { arm, origin: base.originHash, grantId: (a, slot) => at(slot).grantId(a),
    descriptor: (slot) => at(slot).descriptor(),
    sign: async (g, slot, c, amt, r) => at(slot).authorise(evmEip712Messages.withdrawUnshieldedAsGrantee(
      { account: g.contractAddress, grantee: base.address, label, slot, issuedAt: g.issuedAt, grantNonce: g.grantNonce }, c, amt, r)),
    asDevice: (account, authNonce, newKey) => {
      // the grantee's own wallet signs a device-role RotateEncKey, with its blind
      const td = evmEip712Messages.rotateEncKey({ account, device: base.address, authNonce }, newKey);
      const sig = parseEvmSignature(wallet.signDigest(typedDataDigest(td)));
      return { circuit: 'rotate_enc_key_with_evm_eip712', args: [newKey, { pk: base.pk, use_counter: 0n, blind: base.blind, sig: { r: sig.r, s: sig.s } }] };
    },
    evm: { pk: base.pk, blind: base.blind, address: base.address, label, wallet } };
}

// ── The simulated account, its owner, and caller injection ──────────────────

type OwnerArm = 'k256' | 'jubjub' | 'evm_eip712';
/** `tamperCaller`: the owner signs the scope as given, the call carries this
 *  caller instead (the signed-policy item). `rawReadPk` (evm_eip712 owner):
 *  the read key passed to the circuit as given, not canonicalised by the
 *  client. `plain` (upstream owners): fields of the hashed scope overridden
 *  (for example a zero read_pk_hash). */
interface IssueOpts { tamperCaller?: Uint8Array | null; rawReadPk?: Uint8Array; plain?: Partial<PlainScope> }
interface Account {
  address: Uint8Array;
  ownerArm: OwnerArm;
  L(): any;
  /** Invoke an impure circuit (optionally with an injected caller). */
  call(name: string, args: unknown[], caller?: PublicAddress): Promise<any>;
  issue(grantee: Grantee, slot: bigint, scope: Scope, salt: Uint8Array, opts?: IssueOpts): Promise<void>;
  revoke(grantee: Grantee, slot: bigint): Promise<void>;
  revokeAll(): Promise<void>;
  /** The evm_eip712 owner (when ownerArm is evm_eip712). */
  evmOwner?: EvmEip712Device;
  snapshot(): any; restore(s: any): void;
  setTime(t: number): void; time(): number;
  setCoins(ps: CoinStorePrivateState): void;
}

async function openAccount(ownerArm: OwnerArm): Promise<Account> {
  const contract: any = new (Contract as any)(makeWitnesses());
  const impure: Record<string, (...a: any[]) => Promise<any>> = contract.impureCircuits;
  const coinPk = { bytes: rnd() };
  const addressHex: string = sampleContractAddress();
  const address = hexToBytes(addressHex.replace(/^0x/, ''));
  let privateState: CoinStorePrivateState = emptyCoinStore();
  const salt = rnd();
  const jub = ownerArm === 'jubjub' ? JubjubDevice.generate() : undefined;
  const k1 = ownerArm === 'k256' ? K256Device.generate() : undefined;
  const evmOwner = ownerArm === 'evm_eip712' ? await EvmEip712Device.enrol(SoftwareEvmWallet.generate(), 'undeployed', 0) : undefined;
  const boot = jub ? jub.bootCommitment(salt) : k1 ? k1.bootCommitment(salt) : evmOwner!.bootCommitment(salt);
  const init = await contract.initialState(createConstructorContext(privateState, coinPk), boot, rnd(), JubjubDevice.generate().pk, new Uint8Array(64), 259_200n);
  let state: any = init.currentContractState;
  let counter = 0n;
  let time = 1_800_000_000;
  const L = () => ledger(state) as any;
  async function call(name: string, args: unknown[], caller?: PublicAddress) {
    const ctx: any = createCircuitContext({ circuitId: name, contractAddress: addressHex, coinPublicKeyOrZswapState: coinPk,
      contractState: state, privateState, time } as any);
    if (caller !== undefined) {
      ctx.callContext = createCallContext(name, addressHex, coinPk, state, privateState, time, undefined, caller);
      ctx.queryContexts[addressHex] = ctx.callContext.currentQueryContext;
    }
    const res = await impure[name](ctx, ...args);
    state = res.context.callContext.currentQueryContext.state;
    privateState = res.context.callContext.currentPrivateState ?? privateState;
    return res;
  }
  if (jub) await call('activate_initial_device_with_jubjub', [jub.pk, salt]);
  else if (k1) await call('activate_initial_device_with_k256', [k1.pk, salt, k1.envelope]);
  else await call('activate_initial_device_with_evm_eip712', evmOwner!.activationArgs(salt));
  const ctx = () => ({ contractAddress: address, authNonce: L().auth_nonce as bigint });
  const evmFrame = () => ({ account: address, device: evmOwner!.address, authNonce: L().auth_nonce as bigint });
  const evmAuth = async (td: any) => { const { arm, ...a } = await evmOwner!.authorise(td, counter); return a; };

  async function issue(g: Grantee, slot: bigint, s: Scope, scopeSalt: Uint8Array, opts: IssueOpts = {}) {
    const executed = opts.tamperCaller !== undefined ? { ...s, caller: opts.tamperCaller } : s;
    if (evmOwner) {
      const gin = g.descriptor(slot);
      const auth = await evmAuth(evmEip712Messages.issueGrant(evmFrame(), gin, s));
      const args = evmEip712IssueArgs(executed, scopeSalt);
      if (opts.rawReadPk) args[12] = opts.rawReadPk;
      await call('issue_grant_with_evm_eip712', [gin, solArg(gin), ...args, auth]);
    } else {
      const id = g.grantId(address, slot);
      const hashed = { ...plain(s), ...opts.plain };
      const digest = scopeDigest(scopeSalt, hashed);
      const a = jub ? jub.sign(jubjubChallenges.issueGrant(ctx(), jub.pk, id, digest), counter)
                    : k1!.sign(k256Challenges.issueGrant(ctx(), k1!.pk, id, digest), counter);
      await call(`issue_grant_with_${ownerArm}`, [id, ...scopeArgs({ ...plain(executed), ...opts.plain }), scopeSalt, ...authArgs(a)]);
    }
    counter++;
  }
  async function revoke(g: Grantee, slot: bigint) {
    if (evmOwner) {
      const gin = g.descriptor(slot);
      await call('revoke_grant_with_evm_eip712', [gin, solArg(gin), await evmAuth(evmEip712Messages.revokeGrant(evmFrame(), gin))]);
    } else {
      const id = g.grantId(address, slot);
      const a = jub ? jub.sign(jubjubChallenges.revokeGrant(ctx(), jub.pk, id), counter) : k1!.sign(k256Challenges.revokeGrant(ctx(), k1!.pk, id), counter);
      await call(`revoke_grant_with_${ownerArm}`, [id, ...authArgs(a)]);
    }
    counter++;
  }
  async function revokeAll() {
    if (evmOwner) await call('revoke_all_grants_with_evm_eip712', [await evmAuth(evmEip712Messages.revokeAllGrants(evmFrame()))]);
    else {
      const a = jub ? jub.sign(jubjubChallenges.revokeAllGrants(ctx(), jub.pk), counter) : k1!.sign(k256Challenges.revokeAllGrants(ctx(), k1!.pk), counter);
      await call(`revoke_all_grants_with_${ownerArm}`, [...authArgs(a)]);
    }
    counter++;
  }
  return {
    address, ownerArm, L, call, issue, revoke, revokeAll, evmOwner,
    snapshot: () => ({ state, counter, privateState }),
    restore: (x: any) => { state = x.state; counter = x.counter; privateState = x.privateState; },
    setTime: (t) => { time = t; }, time: () => time,
    setCoins: (ps) => { privateState = ps; },
  };
}

/** The unshielded twin for `g` at `slot`, signed over the live record (or a
 *  forced nonce), with optional tampering of the presented authorisation. */
async function spend(acc: Account, g: Grantee, slot: bigint, color: Uint8Array, amount: bigint, recipient: Uint8Array, opening: GrantOpening,
  o: { nonce?: bigint; caller?: PublicAddress; tamper?: (a: any) => any; signer?: Grantee } = {}) {
  const id = g.grantId(acc.address, slot);
  const l = acc.L();
  const rec = l.grants.member(id) ? l.grants.lookup(id) : { issued_at: 0n, nonce: 0n };
  const gc: GrantContext = { contractAddress: acc.address, grantId: id, issuedAt: rec.issued_at, grantNonce: o.nonce ?? rec.nonce };
  let a: any = await (o.signer ?? g).sign(gc, slot, color, amount, recipient);
  if (o.tamper) a = o.tamper(a);
  return acc.call(`withdraw_unshielded_with_grant_${a.arm}`, [color, amount, { bytes: recipient }, ...grantAuthArgs(opening, a)], o.caller);
}

// upstream's badSignatureNeedles: a stale JubJub challenge was ground for
// another nonce, so its cast can fail its range check before verification
const badSignature = (arm: GranteeArm) => arm === 'jubjub' ? ['invalid grant signature', 'range error'] : ['invalid grant signature'];
const readNeedle = (owner: OwnerArm) => owner === 'evm_eip712' ? 'evm_eip712: read without a read key' : 'read without delegate key';

// ── The lifecycle and the unshielded twin, per pairing ──────────────────────

async function scenario(ownerArm: OwnerArm, granteeArm: GranteeArm) {
  const tag = `[owner ${ownerArm} / grantee ${granteeArm}]`;
  const acc = await openAccount(ownerArm);
  const L = () => acc.L();
  const g = await makeGrantee(granteeArm, acc.address);
  const slot = 0n;
  const salt = rnd(), color = rnd(), recipient = rnd();
  const scope = spendScope({ opWithdrawUnshielded: true, color, cap: 450n, perCallCap: 300n, maxCoinValue: 300n,
    recipientKind: RECIPIENT_USER_ADDRESS, recipient });
  const gid = g.grantId(acc.address, slot);
  ok(L().spec_version === 3n && L().grants.isEmpty(), `${tag} spec_version 3, grants empty`);

  // the caller pin stored, and bound by the owner's signature
  const before = acc.snapshot();
  const caller = rnd();
  await acc.issue(g, slot, { ...scope, caller }, salt);
  ok(eq(L().grants.lookup(gid).scope.caller_commit, pureCircuits.derive_grant_caller_commit(salt, { is_some: true, value: { bytes: caller } })),
    `${tag} the owner signs and stores the caller pin`);
  acc.restore(before);
  await expectAbort(`${tag} a caller pin added to a scope signed unrestricted`, () => acc.issue(g, slot, scope, salt, { tamperCaller: caller }),
    ['invalid signature', 'range error']);
  await expectAbort(`${tag} a pin removed from a scope signed pinned`, () => acc.issue(g, slot, { ...scope, caller }, salt, { tamperCaller: null }),
    ['invalid signature', 'range error']);
  // the issue rules (upstream's chip), each refused before any write
  const ro = (o: Partial<Scope> = {}) => spendScope({ read: true, readPk: rnd(), ...o });
  await expectAbort(`${tag} read-only grant cannot restrict caller`, () => acc.issue(g, slot, ro({ caller }), salt), 'read-only grant cannot restrict caller');
  await expectAbort(`${tag} empty scope`, () => acc.issue(g, slot, { ...scope, opWithdrawUnshielded: false, cap: 0n, perCallCap: 0n, recipientKind: 0n, color: ZERO32, recipient: ZERO32, maxCoinValue: 0n }, salt), 'empty scope');
  await expectAbort(`${tag} shielded without read`, () => acc.issue(g, slot, { ...scope, opWithdrawShielded: true }, salt), 'shielded spend requires read');
  await expectAbort(`${tag} per_call_cap > cap`, () => acc.issue(g, slot, { ...scope, perCallCap: 501n }, salt), 'per-call cap above cap');
  await expectAbort(`${tag} max_coin_value < per_call_cap`, () => acc.issue(g, slot, { ...scope, opWithdrawShielded: true, read: true, readPk: rnd(), maxCoinValue: 1n }, salt), 'coin bound below per-call cap');
  await expectAbort(`${tag} read without a delegate key`, () => acc.issue(g, slot, { ...scope, read: true, readPk: ZERO32 }, salt, { plain: { readPkHash: ZERO32 } }), readNeedle(ownerArm));
  await expectAbort(`${tag} window bounds reserved`, () => acc.issue(g, slot, { ...scope, windowLen: 1n }, salt), 'window bounds reserved');
  await expectAbort(`${tag} read-only grant with object fields`, () => acc.issue(g, slot, { ...scope, opWithdrawUnshielded: false, read: true, readPk: rnd(), cap: 0n, perCallCap: 0n }, salt), 'read-only grant carries object fields');
  if (ownerArm === 'evm_eip712') {
    // the arm's own issue rules (G1E-7: nothing stored the wallet did not show)
    // signed with read off (readKey shown as zero), executed with a key
    await expectAbort(`${tag} a read key without read`, () => acc.issue(g, slot, scope, salt, { rawReadPk: rnd() }), 'evm_eip712: a read key without read');
    await expectAbort(`${tag} an RP hash for a non-passkey grantee`, () => acc.issue(g, slot, { ...scope, rpIdHash: rnd() }, salt), 'evm_eip712: an RP hash belongs to a passkey grantee');
  }
  ok(L().grants.isEmpty() && L().auth_nonce === 0n, `${tag} no record written by a refused issue`);

  // issue over an absent id
  await acc.issue(g, slot, scope, salt);
  const g0 = L().grants.lookup(gid);
  ok(g0.epoch === 0n && g0.gen === 0n && g0.active && g0.nonce === 0n, `${tag} record epoch/gen/active/nonce`);
  ok(g0.issued_at === L().auth_nonce && g0.issued_at === 1n, `${tag} issued_at = auth_nonce after the device seam`);
  ok(eq(g0.spent_commit, pureCircuits.derive_grant_spent_commit(salt, 0n)), `${tag} spent_commit commits to 0`);
  ok(eq(g0.scope.object_commit, pureCircuits.derive_grant_object_commit(salt, color, RECIPIENT_USER_ADDRESS, recipient, 300n)), `${tag} object_commit`);
  ok(eq(g0.scope.rp_commit, pureCircuits.derive_grant_rp_commit(salt, ZERO32)), `${tag} rp_commit`);
  ok(eq(g0.scope.read_pk_hash, ZERO32), `${tag} read_pk_hash zero when read is off`);
  ok(g0.scope.per_call_cap === 300n && g0.scope.cap === 450n && g0.scope.expires_at === 0n, `${tag} clear scope fields`);
  await expectAbort(`${tag} re-issue over a live id`, () => acc.issue(g, slot, scope, salt), 'grant already active');

  // a read-only grant under slot 1: read_pk_hash = SHA-256(read key)
  const readPk = rnd();
  await acc.issue(g, 1n, ro({ readPk }), rnd());
  const gRo = L().grants.lookup(g.grantId(acc.address, 1n));
  ok(gRo.scope.read === true && eq(gRo.scope.read_pk_hash, sha256(readPk)), `${tag} read-only grant (slot 1): read_pk_hash = SHA-256(read key)`);

  // one spend
  await acc.call('deposit_unshielded', [color, 1_000n]);
  const opening = openingOf(scope, salt, g.origin, slot);
  const authBefore = L().auth_nonce, roundBefore = L().round, devicesBefore = [...L().devices].map(hex).sort().join(), countBefore = L().device_count;
  await spend(acc, g, slot, color, 200n, recipient, opening);
  opening.spentPrev = 200n;
  const g1 = L().grants.lookup(gid);
  ok(g1.nonce === 1n, `${tag} the grant call advances the record nonce`);
  ok(eq(g1.spent_commit, pureCircuits.derive_grant_spent_commit(salt, 200n)), `${tag} spent_commit re-commits`);
  ok(L().auth_nonce === authBefore, `${tag} auth_nonce untouched by the grant call (GR-5, FR-008)`);
  ok([...L().devices].map(hex).sort().join() === devicesBefore && L().device_count === countBefore, `${tag} no device entry touched (FR-008)`);
  ok(L().round === roundBefore + 1n, `${tag} round advanced once`);
  ok(L().unshielded_balances.lookup(color) === 800n, `${tag} mirror debited`);

  // the rejection matrix; each item leaves state unchanged
  const snap = acc.snapshot();
  await expectAbort(`${tag} identical resubmission (stale nonce)`, () => spend(acc, g, slot, color, 200n, recipient, opening, { nonce: 0n }), badSignature(granteeArm));
  await expectAbort(`${tag} over per_call_cap`, () => spend(acc, g, slot, color, 301n, recipient, opening), 'amount above per-call cap');
  await expectAbort(`${tag} over the cumulative cap`, () => spend(acc, g, slot, color, 300n, recipient, opening), 'cumulative cap exceeded');
  await expectAbort(`${tag} wrong spent_prev`, () => spend(acc, g, slot, color, 100n, recipient, { ...opening, spentPrev: 0n }), 'spent opening mismatch');
  await expectAbort(`${tag} wrong recipient under the pin`, () => spend(acc, g, slot, color, 100n, rnd(), opening), 'recipient not admitted by pin');
  await expectAbort(`${tag} recipient-kind mismatch`, () => spend(acc, g, slot, color, 100n, recipient, { ...opening, recipientKind: RECIPIENT_ZSWAP_COIN_PUBLIC_KEY }), 'scope object mismatch');
  await expectAbort(`${tag} wrong scope_salt`, () => spend(acc, g, slot, color, 100n, recipient, { ...opening, scopeSalt: rnd() }), 'scope object mismatch');
  await expectAbort(`${tag} a foreign key (no record)`, async () => { const f = await makeGrantee(granteeArm, acc.address); return spend(acc, f, slot, color, 100n, recipient, opening); }, 'unknown grant');
  await expectAbort(`${tag} out-of-scope operation (a shielded-only grant used unshielded)`, async () => {
    const sh = spendScope({ opWithdrawShielded: true, read: true, readPk: rnd(), color, cap: 450n, perCallCap: 300n, maxCoinValue: 300n, recipientKind: RECIPIENT_USER_ADDRESS, recipient });
    const s2 = rnd();
    await acc.issue(g, 2n, sh, s2);
    await spend(acc, g, 2n, color, 10n, recipient, openingOf(sh, s2, g.origin, 2n));
  }, 'operation not in scope');
  if (granteeArm === 'evm_eip712') {
    const eg = g;
    await expectAbort(`${tag} evm grantee: r = 0`, () => spend(acc, eg, slot, color, 10n, recipient, opening, { tamper: (a) => ({ ...a, sig: { ...a.sig, r: 0n } }) }), 'evm_eip712: signature scalar is zero');
    await expectAbort(`${tag} evm grantee: another blind (another grant id)`, () => spend(acc, eg, slot, color, 10n, recipient, opening, { tamper: (a) => ({ ...a, blind: rnd() }) }), 'unknown grant');
    await expectAbort(`${tag} evm grantee: another site label (another grant id)`, () => spend(acc, eg, slot, color, 10n, recipient, opening, { tamper: (a) => ({ ...a, label: grantLabel('evil.example') }) }), 'unknown grant');
    await expectAbort(`${tag} evm grantee: another slot (another grant id)`, () => spend(acc, eg, slot, color, 10n, recipient, { ...opening, slot: 7n }), 'unknown grant');
  }
  acc.restore(snap);
  ok(L().grants.lookup(gid).nonce === 1n && L().unshielded_balances.lookup(color) === 800n, `${tag} state restored for the next items`);

  // the grantee key against the device seam of its own arm (no device entry)
  await expectAbort(`${tag} the grantee key against the device seam`, async () => {
    const { circuit, args } = g.asDevice(acc.address, L().auth_nonce, rnd());
    await acc.call(circuit, args);
  }, 'unknown device entry');

  // expiry through the simulated block time
  const exp = { ...scope, expiresAt: BigInt(acc.time() + 100) };
  const sExp = rnd();
  await acc.issue(g, 3n, exp, sExp);
  const oExp = openingOf(exp, sExp, g.origin, 3n);
  await spend(acc, g, 3n, color, 10n, recipient, oExp);
  ok(L().grants.lookup(g.grantId(acc.address, 3n)).nonce === 1n, `${tag} a call before expires_at executes`);
  oExp.spentPrev = 10n;
  acc.setTime(acc.time() + 200);
  await expectAbort(`${tag} a call after expires_at`, () => spend(acc, g, 3n, color, 10n, recipient, oExp), 'grant expired');
  acc.setTime(acc.time() - 200);

  // revoke, tombstone, re-issue
  await acc.revoke(g, slot);
  ok(L().grants.lookup(gid).active === false && L().grants.lookup(gid).nonce === 1n, `${tag} revoke writes a tombstone`);
  await expectAbort(`${tag} a call against a tombstone`, () => spend(acc, g, slot, color, 10n, recipient, opening), 'grant revoked');
  await expectAbort(`${tag} revoke of a tombstone`, () => acc.revoke(g, slot), 'grant not live');
  await expectAbort(`${tag} revoke of an absent id (another slot)`, () => acc.revoke(g, 9n), 'unknown grant');
  const sNew = rnd();
  await acc.issue(g, slot, scope, sNew);
  ok(L().grants.lookup(gid).active && L().grants.lookup(gid).nonce === 0n && L().grants.lookup(gid).issued_at > g0.issued_at, `${tag} re-issue over a tombstone: a fresh incarnation`);
  await expectAbort(`${tag} a prior-incarnation opening`, () => spend(acc, g, slot, color, 10n, recipient, { ...opening, spentPrev: 0n }), 'scope object mismatch');

  // revoke-all and the new generation
  await acc.revokeAll();
  ok(L().grant_generation === 1n && L().grants.isEmpty(), `${tag} revoke_all bumps the generation and clears the map`);
  await expectAbort(`${tag} a call after revoke_all`, () => spend(acc, g, slot, color, 10n, recipient, openingOf(scope, sNew, g.origin, slot)), 'unknown grant');
  await acc.issue(g, slot, scope, sNew);
  ok(L().grants.lookup(gid).gen === 1n, `${tag} re-issue under generation 1`);
}

// ── The caller pin on the evm_eip712 twins (grants-caller-offline's matrix) ─

async function callerMatrix(ownerArm: OwnerArm) {
  const tag = `[caller pin, owner ${ownerArm} / grantee evm_eip712]`;
  const acc = await openAccount(ownerArm);
  const g = await makeGrantee('evm_eip712', acc.address);
  const hexOf = (b: Uint8Array) => Buffer.from(b).toString('hex');
  const pinned = rnd(), wrong = rnd();
  const contractCaller = (b: Uint8Array): PublicAddress => ({ tag: 'contract', address: hexOf(b) } as PublicAddress);
  const good = contractCaller(pinned);
  const bad: (PublicAddress | undefined)[] = [undefined, { tag: 'user', address: hexOf(pinned) } as PublicAddress, contractCaller(wrong)];
  const color = rnd(), recipient = rnd(), salt = rnd();
  await acc.call('deposit_unshielded', [color, 100n]);
  const base = spendScope({ opWithdrawUnshielded: true, color, cap: 20n, perCallCap: 10n, maxCoinValue: 10n });
  await acc.issue(g, 0n, { ...base, caller: pinned }, salt);
  const id = g.grantId(acc.address, 0n);
  ok(eq(acc.L().grants.lookup(id).scope.caller_commit, pureCircuits.derive_grant_caller_commit(salt, { is_some: true, value: { bytes: pinned } })), `${tag} pin stored`);
  const opening = openingOf(base, salt, g.origin, 0n);
  for (const c of bad) {
    await expectAbort(`${tag} caller ${c ? c.tag : 'none'}${c && c.tag === 'contract' ? ' (another contract)' : ''} refused`,
      () => spend(acc, g, 0n, color, 5n, recipient, opening, { caller: c }), ['grant requires a contract caller', 'grant caller mismatch']);
    ok(acc.L().grants.lookup(id).nonce === 0n, `${tag} nonce unchanged after a refused caller`);
  }
  await expectAbort(`${tag} a damaged signature from the pinned contract`, () => spend(acc, g, 0n, color, 5n, recipient, opening,
    { caller: good, tamper: (a) => ({ ...a, sig: { ...a.sig, s: 1n } }) }), 'invalid grant signature');
  await spend(acc, g, 0n, color, 5n, recipient, opening, { caller: good });
  ok(acc.L().grants.lookup(id).nonce === 1n, `${tag} the pinned contract's call executes`);
  // unrestricted: the transcript does not depend on the caller
  await acc.revoke(g, 0n);
  const s2 = rnd();
  await acc.issue(g, 0n, base, s2);
  const o2 = openingOf(base, s2, g.origin, 0n);
  const before = acc.snapshot();
  const transcripts: string[] = [];
  for (const c of [...bad, good]) {
    acc.restore(before);
    const r = await spend(acc, g, 0n, color, 1n, recipient, o2, { caller: c });
    transcripts.push(JSON.stringify(r.context.callProofDataTrace.at(-1).publicTranscript, (_k, v) => (typeof v === 'bigint' ? v.toString() : v)));
  }
  ok(transcripts.every((t) => t === transcripts[0]), `${tag} an unrestricted grant's transcript is caller-independent (4 callers)`);
  // the shared caller gate dominates both evm_eip712 shielded twins
  acc.restore(before);
  await acc.revoke(g, 0n);
  const s3 = rnd();
  const sh = spendScope({ ...base, opWithdrawShielded: true, opWithdrawShieldedToContract: true, read: true, readPk: rnd(), maxCoinValue: 10n, caller: pinned });
  await acc.issue(g, 0n, sh, s3);
  const coin = { nonce: rnd(), color, value: 10n, mtIndex: 0n };
  acc.setCoins(withCoin(emptyCoinStore(), coin));
  const enc = acc.L().enc_key;
  const k = g.evm!;
  for (const name of ['withdraw_shielded', 'withdraw_shielded_to_contract']) {
    const rec = acc.L().grants.lookup(id);
    const frame = { account: acc.address, grantee: k.address, label: grantLabel('bank.example'), slot: 0n, issuedAt: rec.issued_at, grantNonce: rec.nonce };
    const change = rnd(192);
    const td = name === 'withdraw_shielded'
      ? evmEip712Messages.withdrawShieldedAsGrantee(frame, color, 5n, recipient, change, enc, { nonce: coin.nonce, value: 10n, mtIndex: 0n })
      : evmEip712Messages.withdrawShieldedToContractAsGrantee(frame, color, 5n, recipient, change, enc, { nonce: coin.nonce, value: 10n, mtIndex: 0n });
    const sig = parseEvmSignature(k.wallet.signDigest(typedDataDigest(td)));
    const a: EvmEip712GrantAuthorisation = { arm: 'evm_eip712', pk: k.pk, blind: k.blind, label: grantLabel('bank.example'), sig: { r: sig.r, s: sig.s } };
    await expectAbort(`${tag} ${name}: another contract caller refused by the shared gate`,
      () => acc.call(`${name}_with_grant_evm_eip712`, [{ bytes: recipient }, color, 5n, change, enc, ...grantAuthArgs(openingOf(sh, s3, g.origin, 0n), a)], contractCaller(wrong)),
      'grant caller mismatch');
  }
}

async function main() {
  for (const [o, g] of [['evm_eip712', 'k256'], ['evm_eip712', 'jubjub'], ['evm_eip712', 'evm_eip712'], ['k256', 'evm_eip712'], ['jubjub', 'evm_eip712']] as [OwnerArm, GranteeArm][]) {
    await section(`[owner ${o} / grantee ${g}] lifecycle and the unshielded grant twin`, () => scenario(o, g));
  }
  for (const o of ['evm_eip712', 'jubjub'] as OwnerArm[]) await section(`[caller pin] owner ${o}, grantee evm_eip712`, () => callerMatrix(o));
  console.log('');
  for (const s of sections) console.log(`  ${String(s.pass).padStart(3)} passed, ${s.fail} failed  ${s.label}`);
  console.log(`\n◆ evm-eip712-grants-offline: ${fail === 0 ? 'PASS' : 'FAIL'} (${pass} passed, ${fail} failed)`);
  if (process.env.EVIDENCE_DIR) {
    const fs = await import('node:fs');
    fs.writeFileSync(`${process.env.EVIDENCE_DIR}/evm-eip712-grants-offline.json`, JSON.stringify({ suite: 'evm-eip712-grants-offline', ranAt: new Date().toISOString(), sections, pass, fail, failures, verdict: fail === 0 ? 'PASS' : 'FAIL' }, null, 2) + '\n');
  }
  process.exit(fail === 0 ? 0 : 1);
}
await main();
