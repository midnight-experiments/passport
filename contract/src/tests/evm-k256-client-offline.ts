// Offline suite of the `evm_k256` client's behaviour towards the wallet
// (src/wallet/signer-evm-k256.ts, with blind.ts restoreBlind and
// checkSigner). No node, no proof server; software keys only.
//
//   format    the arm's one format: evmK256WalletFormats() is the readable
//             registry's list (eip712-v1, "EIP-712 V1"); typed data under any
//             other domain (the per-account domain, a chainId, a salt,
//             another name, version or verifyingContract, a member missing,
//             another EIP712Domain type) is refused before the wallet is
//             asked, by the device, the grantee and authorisationFrom
//   signer    the signer check at every place a signature comes back: a
//             wallet that answers with another key is refused before any
//             proof by the device and grantee approvals, authorisationFrom,
//             each of the two blind signatures of enrolment, and the call
//             facades (the account's proving surface is never reached; the
//             honest control reaches it); the refusal names the other key
//             only when the signature recovers to it (a candidate another
//             connected wallet reports), never a candidate it does not
//             recover to, the expected address or a malformed candidate;
//             signatures over another digest (another domain, a blind
//             request presented as an approval, an unrecoverable r) are
//             refused with the signer unknown
//   blind     two sessions (two wallet instances of one key) give equal
//             signatures, canonical forms and blinds, for devices (keys ×
//             networks × account indexes) and grantees (× issuing accounts),
//             each blind equal to the contract's derive_blind; the high-S
//             twin gives the same blind; a non-deterministic wallet is
//             refused after exactly two requests, before any transaction, as
//             a device, as a grantee and in a restore
//   records   device and grantee records: the format and the cached blind
//             (and read seed) round-trip; records of another arm, role or
//             format, with a malformed or half cache, a malformed point,
//             address, index or issuing account are refused before the
//             wallet is asked; a record without its cache is refused by
//             fromRecord
//   restore   restoreEvmK256Device and restoreEvmK256Grantee: from the cache
//             (no signature asked); from the stored format when the cache is
//             lost (the blind derived again, equal to the enrolment's, from
//             a signature by the record's key, whatever address the wallet
//             reports); without a record (found by the caller's test; not
//             found: the message that says so and what remains, for each
//             role); a wallet of another key against a record refused,
//             naming the key it reports
//   requests  every wallet request of this suite: `personal_sign` only for
//             a device or grantee blind request, byte for byte,
//             `eth_signTypedData_v4` only for V1 typed data, and no other
//             method
//
// Writes $EVIDENCE_DIR/evm-k256-client-offline.json when EVIDENCE_DIR is
// set; never writes into the repository.

import { strict as assert } from 'node:assert';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { secp256k1 } from '@noble/curves/secp256k1.js';
import { pureCircuits } from '../wallet/contract.js';
import { blindFormats, blindFormatName, blindMessageBytes, granteeBlindMessageBytes, SignerMismatchError } from '../wallet/blind.js';
import { evmChecksumAddress, grantLabel, padTag } from '../wallet/descriptors.js';
import {
  eip712V1Domain, evmK256Messages, typedDataDigest, checkEip712V1TypedData, EIP712_V1_VERIFYING_CONTRACT,
  type Eip712TypedData,
} from '../wallet/evm-k256-codec.js';
import { perAccountDomain, FOREIGN_DOMAINS } from './evm-k256-domains.js';
import {
  EVM_K256_FORMAT, EvmK256Device, EvmK256Grantee, SoftwareEvmWallet, checkEvmK256Signer, enrolEvmBlind, enrolEvmGranteeBlind,
  evmK256WalletFormats, highSTwin, parseEvmSignature, personalMessageDigest, restoreEvmK256Device, restoreEvmK256Grantee,
  revokeAllGrantsWithEvmK256, rotateEncKeyWithEvmK256, serialiseEvmSignature, withdrawUnshieldedAsEvmGrantee, SECP256K1_ORDER,
  type EvmK256GranteeRecord, type EvmK256RosterRecord, type EvmWallet,
} from '../wallet/signer-evm-k256.js';

const SEED = 'evm-k256-client-offline/v1';
let ctr = 0;
const rnd = (n = 32): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, Math.min(32, n - i)), i);
  return out;
};
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const eq = (a: Uint8Array, b: Uint8Array) => Buffer.from(a).equals(Buffer.from(b));
const beInt = (b: Uint8Array) => { let v = 0n; for (const x of b) v = (v << 8n) | BigInt(x); return v; };
const be32 = (v: bigint) => { const o = new Uint8Array(32); let x = v; for (let i = 31; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const scalar = () => { for (;;) { const k = beInt(rnd()); if (k > 0n && k < SECP256K1_ORDER) return k; } };
const clone = <T>(t: T): T => JSON.parse(JSON.stringify(t));
const pc = pureCircuits as any;

const tally: Record<string, { pass: number; refused: number }> = {};
const ok = (k: string, n = 1) => { (tally[k] ??= { pass: 0, refused: 0 }).pass += n; };
const counted = (k: string) => { (tally[k] ??= { pass: 0, refused: 0 }).refused++; };
const refused = (k: string, f: () => unknown, re: RegExp, why: string) => { assert.throws(f, re, `${k}: must refuse ${why}`); counted(k); };
const refusedAsync = async (k: string, f: () => Promise<unknown>, re: RegExp, why: string) => { await assert.rejects(f, re, `${k}: must refuse ${why}`); counted(k); };

// ── A wallet that records what it is asked ───────────────────────────────────

type Request = { method: 'address' } | { method: 'personalSign'; message: Uint8Array } | { method: 'signTypedData'; typedData: Eip712TypedData };
/** Every request any wallet of this suite received, with the address the
 *  wallet reported. */
const ALL_REQUESTS: { reported: Uint8Array; signer: Uint8Array; r: Request }[] = [];

/**
 * A wallet that reports `reported`'s address and signs with `signer`'s key
 * (the same key for an honest wallet; another for a wallet that answers with
 * another account, as a second installed extension does), optionally a
 * different key from the `switchAt`-th signature on, and lists `others` as
 * the addresses of the other connected wallets.
 */
class RecordingWallet implements EvmWallet {
  readonly requests: Request[] = [];
  otherAddresses?: () => Promise<readonly Uint8Array[]>;
  private signatures = 0;
  constructor(
    readonly reported: SoftwareEvmWallet,
    readonly signer: SoftwareEvmWallet = reported,
    others?: Uint8Array[],
    readonly switchTo?: { at: number; signer: SoftwareEvmWallet },
  ) {
    if (others) this.otherAddresses = async () => others.map((a) => new Uint8Array(a));
  }
  private log(r: Request) { this.requests.push(r); ALL_REQUESTS.push({ reported: this.reported.addressBytes, signer: this.signerNow().addressBytes, r }); }
  private signerNow() { return this.switchTo && this.signatures >= this.switchTo.at ? this.switchTo.signer : this.signer; }
  async address() { this.log({ method: 'address' }); return new Uint8Array(this.reported.addressBytes); }
  async personalSign(message: Uint8Array) {
    this.log({ method: 'personalSign', message: new Uint8Array(message) });
    const s = this.signerNow(); this.signatures++;
    return s.personalSign(message);
  }
  async signTypedData(typedData: Eip712TypedData) {
    this.log({ method: 'signTypedData', typedData: clone(typedData) });
    const s = this.signerNow(); this.signatures++;
    return s.signTypedData(typedData);
  }
  count(method: Request['method']) { return this.requests.filter((r) => r.method === method).length; }
}

const NET = 'undeployed';
const LABEL = grantLabel('bank.example');
const SITE = { decimals: 6, symbol: 'TOKEN' };
const addressText = (w: SoftwareEvmWallet) => evmChecksumAddress(w.addressBytes);
const unknownSigner = (expected: SoftwareEvmWallet) =>
  new RegExp(`SignerMismatchError: signer: refused before proving: the signature is not from the expected Ethereum address ${addressText(expected)}, and the signer is unknown$`);
const namedSigner = (expected: SoftwareEvmWallet, signer: SoftwareEvmWallet) =>
  new RegExp(`SignerMismatchError: signer: refused before proving: the signature is not from the expected Ethereum address ${addressText(expected)}; it verifies under Ethereum address ${addressText(signer)}, another wallet's key$`);

/** A device frame's typed data for `d` (rotate_enc_key, an unrelated key). */
const rotateTd = (d: EvmK256Device, account = rnd(), authNonce = 0n) => evmK256Messages.rotateEncKey({ account, device: d.address, authNonce }, rnd());
const granteeTd = (g: EvmK256Grantee, account: Uint8Array) =>
  evmK256Messages.withdrawUnshieldedAsGrantee({ account, grantee: g.address, label: g.label, slot: g.slot, issuedAt: 5n, grantNonce: 6n }, rnd(), 10n, rnd(), SITE);

/** A device-call surface whose proving step only counts: reaching it means
 *  the client went on to prove. */
function deviceSurface(d: EvmK256Device) {
  const account = rnd();
  const s = {
    proved: 0,
    addressBytes: account,
    async ledgerState() {
      const live = d.entryAt(account, 0n, 0n);
      return { auth_nonce: 0n, device_epoch: 0n, devices: { member: (e: Uint8Array) => eq(e, live) } };
    },
    async rotateEncKeyWithAuth() { s.proved++; return { txId: 'tx' }; },
    callTx: { revoke_all_grants_with_evm_k256: async () => { s.proved++; return { public: { txId: 'tx' } }; } } as Record<string, (...a: unknown[]) => Promise<any>>,
  };
  return s;
}
function granteeSurface(g: EvmK256Grantee) {
  const account = rnd();
  const s = {
    proved: 0,
    addressBytes: account,
    async ledgerState() { return { auth_nonce: 0n, device_epoch: 0n, devices: { member: () => false } }; },
    async rotateEncKeyWithAuth() { s.proved++; return { txId: 'tx' }; },
    callTx: {} as Record<string, (...a: unknown[]) => Promise<any>>,
    async heldCoin() { return { nonce: rnd(), color: rnd(), value: 0n, mt_index: 0n }; },
    async encKey() { return rnd(); },
    async grantRecord(id: Uint8Array) { return eq(id, g.grantId(account)) ? { issued_at: 5n, nonce: 6n } : null; },
    async withdrawUnshieldedWithGrantAuth() { s.proved++; return { txId: 'tx' }; },
    async withdrawShieldedWithGrantAuth() { s.proved++; return { txId: 'tx', change: null }; },
    async withdrawShieldedToContractWithGrantAuth() { s.proved++; return { txId: 'tx', sent: null, change: null }; },
  };
  return s;
}
const OPENING = { scopeSalt: new Uint8Array(32), recipientKind: 0n, pinnedRecipient: new Uint8Array(32), maxCoinValue: 0n, spentPrev: 0n };

const report: Record<string, unknown> = {};

// ── Format ───────────────────────────────────────────────────────────────────

{
  assert.deepEqual(evmK256WalletFormats(), ['eip712-v1'], 'every EVM wallet signs the one format');
  assert.deepEqual(evmK256WalletFormats(), [...blindFormats('evm_k256')], 'the formats are the readable registry\'s');
  assert.equal(EVM_K256_FORMAT, 'eip712-v1');
  assert.equal(blindFormatName('evm_k256', EVM_K256_FORMAT), 'EIP-712 V1');
  ok('format', 4);

  const key = new SoftwareEvmWallet(scalar());
  const d = await EvmK256Device.enrol(key, NET, 0);
  const g = await EvmK256Grantee.enrol(key, NET, rnd(), LABEL, 0n);
  assert.equal(d.format, 'eip712-v1'); assert.equal(g.format, 'eip712-v1');
  const honest = rotateTd(d);
  assert.equal(checkEip712V1TypedData(honest), honest, 'the builders\' typed data passes');
  ok('format', 3);
  const P = EIP712_V1_VERIFYING_CONTRACT;
  const otherP = P.slice(0, -2) + (parseInt(P.slice(-2), 16) ^ 1).toString(16).padStart(2, '0');
  const foreign: [string, (t: any) => void][] = [
    ['the per-account domain', (t) => { t.domain = perAccountDomain(rnd()); }],
    ['a chainId in the domain and its type', (t) => { t.domain.chainId = '1'; t.types.EIP712Domain = [...t.types.EIP712Domain, { name: 'chainId', type: 'uint256' }]; }],
    ['a chainId in the domain only', (t) => { t.domain.chainId = '1'; }],
    ['a salt', (t) => { t.domain.salt = '0x' + hex(rnd()); }],
    ['the name "Midnight Passport Account"', (t) => { t.domain.name = 'Midnight Passport Account'; }],
    ['version "2"', (t) => { t.domain.version = '2'; }],
    ['P with its last byte changed', (t) => { t.domain.verifyingContract = otherP; }],
    ['P in lower case', (t) => { t.domain.verifyingContract = P.toLowerCase(); }],
    ['no verifyingContract', (t) => { delete t.domain.verifyingContract; }],
    ['no domain', (t) => { delete t.domain; }],
    ['the EIP712Domain type reordered', (t) => { t.types.EIP712Domain = [t.types.EIP712Domain[1], t.types.EIP712Domain[0], t.types.EIP712Domain[2]]; }],
    ['the EIP712Domain type with chainId', (t) => { t.types.EIP712Domain = [...t.types.EIP712Domain, { name: 'chainId', type: 'uint256' }]; }],
    ['the EIP712Domain type without verifyingContract', (t) => { t.types.EIP712Domain = t.types.EIP712Domain.slice(0, 2); }],
    ['verifyingContract typed as bytes20', (t) => { t.types.EIP712Domain = t.types.EIP712Domain.map((f: any) => (f.name === 'verifyingContract' ? { ...f, type: 'bytes20' } : f)); }],
    ['no EIP712Domain type', (t) => { delete t.types.EIP712Domain; }],
  ];
  const RE = /^Error: eip712: (not the fixed V1 domain|the EIP712Domain type is not the V1 type)/;
  for (const [name, f] of foreign) {
    const td = clone(honest); f(td);
    const w = new RecordingWallet(key);
    const dev = new EvmK256Device(d.pk, d.blind, NET, 0n, w);
    await refusedAsync('format', () => dev.authorise(td, 0n), RE, `a device approval under ${name}`);
    const gt = clone(granteeTd(g, rnd())); f(gt);
    const gw = new RecordingWallet(key);
    await refusedAsync('format', () => new EvmK256Grantee(g.pk, g.blind, LABEL, 0n, gw).authorise(gt), RE, `a grantee approval under ${name}`);
    assert.equal(w.count('signTypedData') + gw.count('signTypedData'), 0, `${name}: the wallet is never asked`);
    // the device's signature over the honest V1 digest, presented with the typed data as changed
    refused('format', () => d.authorisationFrom(td, key.signDigest(typedDataDigest(honest)), 0n), RE, `an existing signature under ${name}`);
  }
  ok('format');
  console.log(`  ✓ format: one format (eip712-v1, "EIP-712 V1") = the registry's; the builders' typed data passes; ${tally.format.refused} requests under ${foreign.length} other domains refused before the wallet was asked`);
}

// ── The signer check ─────────────────────────────────────────────────────────

const signerCases: { case: string; named: string | null }[] = [];
{
  const A = new SoftwareEvmWallet(scalar()), B = new SoftwareEvmWallet(scalar()), C = new SoftwareEvmWallet(scalar());
  const dA = await EvmK256Device.enrol(A, NET, 0);
  const gA = await EvmK256Grantee.enrol(A, NET, rnd(), LABEL, 0n);
  const zero = new Uint8Array(20), short = new Uint8Array(19).fill(1);
  // candidate lists and the key each refusal must name (null: unknown)
  const lists: [string, Uint8Array[] | undefined, SoftwareEvmWallet | null][] = [
    ['no candidate list', undefined, null],
    ['an empty list', [], null],
    ['the signer listed', [B.addressBytes], B],
    ['an unrelated key listed', [C.addressBytes], null],
    ['the unrelated key, then the signer', [C.addressBytes, B.addressBytes], B],
    ['the expected address listed', [A.addressBytes], null],
    ['the zero address and a 19-byte value listed', [zero, short], null],
    ['malformed values before the signer', [zero, short, A.addressBytes, B.addressBytes], B],
  ];
  const expectFor = (named: SoftwareEvmWallet | null) => (named ? namedSigner(A, named) : unknownSigner(A));
  const isMismatch = (named: SoftwareEvmWallet | null) => (e: unknown) => {
    assert.ok(e instanceof SignerMismatchError, 'a SignerMismatchError');
    assert.ok(eq(e.expected, A.addressBytes), 'it names the expected address');
    if (named) assert.ok(e.signer && eq(e.signer, named.addressBytes), 'it names the signer'); else assert.equal(e.signer, undefined, 'no signer named');
    assert.match(String(e), expectFor(named));
    return true;
  };
  for (const [name, others, named] of lists) {
    // device approval: the wallet reports A and answers with B
    const w = new RecordingWallet(A, B, others);
    const dev = new EvmK256Device(dA.pk, dA.blind, NET, 0n, w);
    await assert.rejects(() => dev.authorise(rotateTd(dev), 0n), isMismatch(named)); counted('signer');
    assert.equal(w.count('signTypedData'), 1);
    // authorisationFrom with B's signature
    const td = rotateTd(dA);
    assert.throws(() => dA.authorisationFrom(td, B.signDigest(typedDataDigest(td)), 0n, others ?? []), isMismatch(named)); counted('signer');
    // grantee approval
    const gw = new RecordingWallet(A, B, others);
    await assert.rejects(() => new EvmK256Grantee(gA.pk, gA.blind, LABEL, 0n, gw).authorise(granteeTd(gA, rnd())), isMismatch(named)); counted('signer');
    // enrolment: the first blind signature from B; refused before the second request
    const ew = new RecordingWallet(A, B, others);
    await assert.rejects(() => enrolEvmBlind(ew, NET, 0), isMismatch(named)); counted('signer');
    assert.equal(ew.count('personalSign'), 1, 'refused before the second request');
    const egw = new RecordingWallet(A, B, others);
    await assert.rejects(() => enrolEvmGranteeBlind(egw, NET, rnd()), isMismatch(named)); counted('signer');
    // enrolment: the first from A, the second from B
    const sw = new RecordingWallet(A, A, others, { at: 1, signer: B });
    await assert.rejects(() => EvmK256Device.enrol(sw, NET, 0), isMismatch(named)); counted('signer');
    assert.equal(sw.count('personalSign'), 2);
    const sgw = new RecordingWallet(A, A, others, { at: 1, signer: B });
    await assert.rejects(() => EvmK256Grantee.enrol(sgw, NET, rnd(), LABEL, 0n), isMismatch(named)); counted('signer');
    assert.equal(sgw.count('personalSign'), 2);
    signerCases.push({ case: name, named: named ? addressText(named) : null });
  }
  // the honest wallet passes with every list
  for (const [, others] of lists) {
    const w = new RecordingWallet(A, A, others);
    const dev = new EvmK256Device(dA.pk, dA.blind, NET, 0n, w);
    const a = await dev.authorise(rotateTd(dev), 0n);
    assert.equal(a.pk, dA.pk);
    const td = rotateTd(dA);
    dA.authorisationFrom(td, A.signDigest(typedDataDigest(td)), 0n, others ?? []);
    await new EvmK256Grantee(gA.pk, gA.blind, LABEL, 0n, new RecordingWallet(A, A, others)).authorise(granteeTd(gA, rnd()));
    const e = await enrolEvmBlind(new RecordingWallet(A, A, others), NET, 0);
    assert.ok(eq(e.blind, dA.blind));
    ok('signer', 4);
  }
  // the high-S twin of the device's own signature passes (the same key)
  {
    const td = rotateTd(dA);
    const twin = serialiseEvmSignature(highSTwin(parseEvmSignature(A.signDigest(typedDataDigest(td)))));
    dA.authorisationFrom(td, twin, 0n); ok('signer');
  }
  // signatures over another digest: the signer is unknown, whoever is listed
  {
    const td = rotateTd(dA);
    const all = [A.addressBytes, B.addressBytes, C.addressBytes];
    for (const [name, dom] of Object.entries(FOREIGN_DOMAINS)) {
      refused('signer', () => dA.authorisationFrom(td, A.signDigest(dom.digest(td, rnd())), 0n, all), unknownSigner(A), `the device's key over the message under ${dom.name} (${name})`);
    }
    const blindSig = await A.personalSign(blindMessageBytes({ scheme: 'evm_k256', network: NET, identity: A.addressBytes, accountIndex: 0 }));
    refused('signer', () => dA.authorisationFrom(td, blindSig, 0n, all), unknownSigner(A), 'the device\'s blind signature presented as an approval');
    const approval = A.signDigest(typedDataDigest(td));
    const msg = blindMessageBytes({ scheme: 'evm_k256', network: NET, identity: A.addressBytes, accountIndex: 0 });
    refused('signer', () => checkEvmK256Signer(A.addressBytes, personalMessageDigest(msg), approval, all), unknownSigner(A), 'an approval presented as a blind signature');
    // an r with no curve point: nothing can be recovered
    let r = 0n;
    for (;;) { r = beInt(rnd()) % SECP256K1_ORDER; if (r === 0n) continue; try { secp256k1.Point.fromHex('02' + hex(be32(r))); } catch { break; } }
    const bad = new Uint8Array([...be32(r), ...be32(5n), 27]);
    refused('signer', () => dA.authorisationFrom(td, bad, 0n, all), unknownSigner(A), 'an r that is no point\'s x-coordinate');
    refused('signer', () => dA.authorisationFrom(td, approval.subarray(0, 64), 0n, all), /65 bytes/, 'a 64-byte signature');
  }
  // the call facades: refused before the proving surface is reached
  {
    const s1 = deviceSurface(dA);
    await rotateEncKeyWithEvmK256(s1, new EvmK256Device(dA.pk, dA.blind, NET, 0n, new RecordingWallet(A)), rnd());
    assert.equal(s1.proved, 1, 'the honest control reaches the proving surface');
    const s2 = deviceSurface(dA);
    await refusedAsync('signer', () => rotateEncKeyWithEvmK256(s2, new EvmK256Device(dA.pk, dA.blind, NET, 0n, new RecordingWallet(A, B, [B.addressBytes])), rnd()), namedSigner(A, B), 'rotate_enc_key signed by another wallet');
    const s3 = deviceSurface(dA);
    await refusedAsync('signer', () => revokeAllGrantsWithEvmK256(s3, new EvmK256Device(dA.pk, dA.blind, NET, 0n, new RecordingWallet(A, B))), unknownSigner(A), 'revoke_all_grants signed by another wallet');
    const s4 = deviceSurface(dA);
    await revokeAllGrantsWithEvmK256(s4, new EvmK256Device(dA.pk, dA.blind, NET, 0n, new RecordingWallet(A)));
    assert.equal(s2.proved + s3.proved, 0, 'nothing proved for a refused signature'); assert.equal(s4.proved, 1);
    const gs = granteeSurface(gA);
    await withdrawUnshieldedAsEvmGrantee(gs, new EvmK256Grantee(gA.pk, gA.blind, LABEL, 0n, new RecordingWallet(A)), OPENING, rnd(), 10n, rnd(), SITE);
    assert.equal(gs.proved, 1, 'the honest grantee control reaches the proving surface');
    const gs2 = granteeSurface(gA);
    await refusedAsync('signer', () => withdrawUnshieldedAsEvmGrantee(gs2, new EvmK256Grantee(gA.pk, gA.blind, LABEL, 0n, new RecordingWallet(A, B, [C.addressBytes, B.addressBytes])), OPENING, rnd(), 10n, rnd(), SITE),
      namedSigner(A, B), 'a grantee spend signed by another wallet');
    assert.equal(gs2.proved, 0);
    ok('signer', 4);
  }
  report.signer = signerCases;
  console.log(`  ✓ signer: another wallet's signature refused before proving at ${lists.length} candidate lists × 7 return points (the device's and the grantee's approvals, authorisationFrom, both blind signatures of each role); named only when it recovers; honest signatures pass with every list (${tally.signer.pass}); ${tally.signer.refused} refusals, the facades never reach the proving surface`);
}

// ── Blind: two sessions, the sign-twice check ────────────────────────────────

const BLIND_TAG = padTag('midnight:account:blind:evm:v1');
const sessions: Record<string, string>[] = [];
{
  for (let i = 0; i < 6; i++) {
    const k = i === 0 ? 1n : scalar();
    for (const [network, index] of [[NET, 0], [NET, 1], ['preview', 0], [NET, 0xffffffff]] as [string, number][]) {
      const one = await enrolEvmBlind(new RecordingWallet(new SoftwareEvmWallet(k)), network, index);
      const two = await enrolEvmBlind(new RecordingWallet(new SoftwareEvmWallet(k)), network, index);
      assert.ok(eq(one.signatures[0], two.signatures[0]) && eq(one.canonical, two.canonical) && eq(one.blind, two.blind), 'two sessions give one blind');
      assert.ok(eq(one.blind, pc.derive_blind(BLIND_TAG, one.canonical)), 'the blind == derive_blind');
      assert.equal(one.pk.x, two.pk.x);
      if (i < 2) sessions.push({ role: 'device', scalar: k.toString(16), network, accountIndex: String(index), blind: hex(one.blind) });
      ok('blind');
    }
    for (let j = 0; j < 3; j++) {
      const issuer = rnd();
      const one = await EvmK256Grantee.enrol(new RecordingWallet(new SoftwareEvmWallet(k)), NET, issuer, LABEL, 0n);
      const two = await EvmK256Grantee.enrol(new RecordingWallet(new SoftwareEvmWallet(k)), NET, issuer, LABEL, 0n);
      assert.ok(eq(one.blind, two.blind), 'two sessions give one grantee blind');
      assert.ok(eq(one.readKey(issuer).publicKey, two.readKey(issuer).publicKey), 'and one read key');
      assert.ok(eq(one.grantId(issuer), two.grantId(issuer)));
      if (i < 2 && j === 0) sessions.push({ role: 'grantee', scalar: k.toString(16), network: NET, issuingAccount: hex(issuer), blind: hex(one.blind) });
      ok('blind');
    }
  }
  // a second session that returns the high-S twin
  {
    const k = new SoftwareEvmWallet(scalar());
    const e = await enrolEvmBlind(k, NET, 0);
    const twin = serialiseEvmSignature(highSTwin(parseEvmSignature(e.signatures[0])));
    const viaTwin: EvmWallet = { address: () => k.address(), personalSign: async () => twin, signTypedData: () => { throw new Error('not asked'); } };
    assert.ok(eq((await enrolEvmBlind(viaTwin, NET, 0)).blind, e.blind), 'the high-S twin gives the same blind');
    ok('blind');
  }
  // a non-deterministic wallet: refused after exactly two requests
  const hedged = new SoftwareEvmWallet(scalar(), true);
  for (const [role, run] of [
    ['device', (w: EvmWallet) => EvmK256Device.enrol(w, NET, 0)],
    ['grantee', (w: EvmWallet) => EvmK256Grantee.enrol(w, NET, rnd(), LABEL, 0n)],
    ['device restore', (w: EvmWallet) => restoreEvmK256Device({ wallet: w, network: NET, accountIndex: 0, finds: () => true })],
    ['grantee restore', (w: EvmWallet) => restoreEvmK256Grantee({ wallet: w, label: LABEL, slot: 0n, network: NET, issuingAccount: rnd(), finds: () => true })],
  ] as [string, (w: EvmWallet) => Promise<unknown>][]) {
    const w = new RecordingWallet(hedged);
    await refusedAsync('blind', () => run(w), /not deterministic/, `a hedged wallet as a ${role}`);
    assert.equal(w.count('personalSign'), 2, `${role}: two requests`); assert.equal(w.count('signTypedData'), 0, `${role}: no approval`);
  }
  report.sessions = sessions;
  console.log(`  ✓ blind: two sessions give equal signatures and blinds (${tally.blind.pass} key × network × index and key × issuer cases), == derive_blind; the high-S twin agrees; ${tally.blind.refused} non-deterministic enrolments refused after two requests, nothing signed or proved`);
}

// ── Records ──────────────────────────────────────────────────────────────────

{
  const k = new SoftwareEvmWallet(scalar());
  const d = await EvmK256Device.enrol(k, NET, 3);
  const rec = d.toRecord();
  assert.equal(rec.format, 'eip712-v1'); assert.equal(rec.blind, hex(d.blind));
  const back = EvmK256Device.fromRecord(JSON.parse(JSON.stringify(rec)));
  assert.ok(eq(back.blind, d.blind) && eq(back.address, d.address) && back.accountIndex === 3n && back.format === 'eip712-v1');
  ok('records');
  const { blind: _b, ...lost } = rec;
  refused('records', () => EvmK256Device.fromRecord(lost as EvmK256RosterRecord), /holds no cached blind/, 'a device record without its cache');
  const other = new SoftwareEvmWallet(scalar());
  const bad: [string, Partial<Record<keyof EvmK256RosterRecord, unknown>>, RegExp][] = [
    ['another scheme', { scheme: 'sol_ed25519' }, /not an evm_k256 record/],
    ['no format', { format: undefined }, /has no format/],
    ['the format raw', { format: 'raw' }, /has no format/],
    ['the format EIP712-V1', { format: 'EIP712-V1' }, /has no format/],
    ['the format constructor', { format: 'constructor' }, /has no format/],
    ['a blind that is not hex', { blind: 'zz' }, /hex/],
    ['a 31-byte blind', { blind: hex(rnd(31)) }, /32 bytes/],
    ['a numeric blind', { blind: 7 }, /is hex/],
    ['an upper-case coordinate', { pk: { ...rec.pk, x: rec.pk.x.toUpperCase() } }, /64-digit lower-case hex/],
    ['a short coordinate', { pk: { ...rec.pk, x: rec.pk.x.slice(2) } }, /64-digit lower-case hex/],
    ['an off-curve point', { pk: { ...rec.pk, y: rec.pk.x } }, /not on curve|invalid|bad point/i],
    ['the point at infinity', { pk: { x: '0'.repeat(64), y: '0'.repeat(64) } }, /point at infinity/],
    ['another key\'s address', { address: addressText(other) }, /not the point's address/],
    ['no address', { address: undefined }, /not the point's address/],
    ['an account index 01', { accountIndex: '01' }, /decimal number/],
    ['an account index -1', { accountIndex: '-1' }, /decimal number/],
    ['an account index 0x1', { accountIndex: '0x1' }, /decimal number/],
    ['a numeric account index', { accountIndex: 1 }, /decimal number/],
    ['no network', { network: undefined }, /names its network/],
  ];
  for (const [why, patch, re] of bad) refused('records', () => EvmK256Device.fromRecord({ ...rec, ...patch } as EvmK256RosterRecord), re, `a device record with ${why}`);
  // the same refusals in a restore, before the wallet is asked
  for (const [why, patch, re] of bad) {
    const w = new RecordingWallet(k);
    await refusedAsync('records', () => restoreEvmK256Device({ wallet: w, record: { ...rec, ...patch } as EvmK256RosterRecord }), re, `a restore from a record with ${why}`);
    assert.equal(w.requests.length, 0, `${why}: the wallet is not asked`);
  }

  const issuer = rnd();
  const g = await EvmK256Grantee.enrol(k, NET, issuer, LABEL, 2n);
  const grec = g.toRecord();
  assert.equal(grec.role, 'grantee'); assert.equal(grec.format, 'eip712-v1'); assert.equal(grec.issuingAccount, hex(issuer));
  const gback = EvmK256Grantee.fromRecord(JSON.parse(JSON.stringify(grec)), LABEL, 2n);
  assert.ok(eq(gback.blind, g.blind) && eq(gback.grantId(issuer), g.grantId(issuer)) && eq(gback.readKey(issuer).publicKey, g.readKey(issuer).publicKey));
  const shop = grantLabel('shop.example');
  assert.ok(eq(EvmK256Grantee.fromRecord(grec, shop, 0n).grantId(issuer), g.withGrant(shop, 0n).grantId(issuer)), 'one record serves every grant of the issuer');
  ok('records', 2);
  refused('records', () => new EvmK256Grantee(g.pk, g.blind, LABEL, 2n).toRecord(), /only a grantee enrolled from its wallet/, 'a record of the issuer\'s view of a grantee');
  const { blind: _gb, readSeed: _rs, ...glost } = grec;
  refused('records', () => EvmK256Grantee.fromRecord(glost as EvmK256GranteeRecord, LABEL, 2n), /holds no cached blind/, 'a grantee record without its cache');
  const gbad: [string, Partial<Record<keyof EvmK256GranteeRecord, unknown>>, RegExp][] = [
    ['the role device', { role: 'device' }, /not a grantee record/],
    ['no role', { role: undefined }, /not a grantee record/],
    ['the blind without the read seed', { readSeed: undefined }, /together/],
    ['the read seed without the blind', { blind: undefined }, /together/],
    ['a 31-byte issuing account', { issuingAccount: hex(rnd(31)) }, /issuing account/],
    ['an upper-case issuing account', { issuingAccount: hex(issuer).toUpperCase() }, /issuing account/],
    ['the format raw', { format: 'raw' }, /has no format/],
    ['a malformed read seed', { readSeed: 'zz' }, /hex/],
  ];
  for (const [why, patch, re] of gbad) refused('records', () => EvmK256Grantee.fromRecord({ ...grec, ...patch } as EvmK256GranteeRecord, LABEL, 2n), re, `a grantee record with ${why}`);
  console.log(`  ✓ records: device and grantee records carry the format and the cached blind (and read seed), round trip; ${tally.records.refused} malformed records and requests refused, the wallet never asked`);
}

// ── Restore ──────────────────────────────────────────────────────────────────

const restoreCases: Record<string, unknown>[] = [];
{
  const A = new SoftwareEvmWallet(scalar()), B = new SoftwareEvmWallet(scalar());
  const d = await EvmK256Device.enrol(A, NET, 1);
  const rec = d.toRecord();
  const { blind: _b, ...lost } = rec;
  const request = blindMessageBytes({ scheme: 'evm_k256', network: NET, identity: A.addressBytes, accountIndex: 1 });
  const signs = (w: RecordingWallet) => w.requests.filter((r) => r.method !== 'address');

  // 1. the cache: no signature asked
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Device({ wallet: w, record: rec });
    assert.ok(r.ok === true && r.source === 'cache' && eq(r.value.blind, d.blind) && eq(r.value.address, d.address) && r.value.wallet === w);
    assert.equal(signs(w).length, 0, 'nothing signed');
    restoreCases.push({ case: 'device, cached', source: 'cache', signatures: 0 });
    ok('restore');
  }
  // 2. the cache lost: derived again in the stored format
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Device({ wallet: w, record: lost as EvmK256RosterRecord });
    assert.ok(r.ok === true && r.source === 'stored-format' && eq(r.value.blind, d.blind) && r.value.pk.x === d.pk.x);
    assert.equal(w.count('personalSign'), 2); assert.equal(w.count('signTypedData'), 0);
    assert.ok(signs(w).every((x) => x.method === 'personalSign' && eq(x.message, request)), 'the device request of the record');
    restoreCases.push({ case: 'device, cache lost', source: 'stored-format', signatures: 2 });
    ok('restore');
  }
  // 3. the cache lost, the wallet reporting another address but signing with the record's key
  {
    const w = new RecordingWallet(B, A);
    const r = await restoreEvmK256Device({ wallet: w, record: lost as EvmK256RosterRecord });
    assert.ok(r.ok === true && r.source === 'stored-format' && eq(r.value.blind, d.blind), 'the record\'s key, whatever the wallet reports');
    ok('restore');
  }
  // 4. the cache lost, a wallet of another key: refused, naming the key it reports
  {
    const w = new RecordingWallet(B);
    await refusedAsync('restore', () => restoreEvmK256Device({ wallet: w, record: lost as EvmK256RosterRecord }), namedSigner(A, B), 'another key\'s wallet against a device record');
    assert.equal(w.count('personalSign'), 1, 'refused at the first signature');
    restoreCases.push({ case: 'device, cache lost, another key', refused: true });
  }
  // 5. no record, found
  const A1 = rnd(), live = new Set([hex(d.entryAt(A1, 0n, 2n))]);
  const finds = (x: EvmK256Device) => [0n, 1n, 2n, 3n].some((c) => live.has(hex(x.entryAt(A1, 0n, c))));
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Device({ wallet: w, network: NET, accountIndex: 1, finds });
    assert.ok(r.ok === true && r.source === 'search' && eq(r.value.blind, d.blind) && r.value.accountIndex === 1n);
    assert.equal(w.count('personalSign'), 2);
    restoreCases.push({ case: 'device, no record, found', source: 'search', signatures: 2 });
    ok('restore');
  }
  // 6. no record, not found: the message names the formats tried and what remains
  const NOT_FOUND = 'No account was found in the formats this wallet can sign (EIP-712 V1). Add this wallet as a new device from another device of the account, or through the account\'s recovery.';
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Device({ wallet: w, network: NET, accountIndex: 0, finds });
    assert.ok(r.ok === false && r.reason === 'not-found');
    assert.equal(r.ok === false && r.message, NOT_FOUND);
    assert.equal(w.count('personalSign'), 2); assert.equal(w.count('signTypedData'), 0);
    restoreCases.push({ case: 'device, no record, not found', message: NOT_FOUND });
    ok('restore');
  }
  // 7. no record: another key's wallet finds nothing (its blind is another)
  {
    const r = await restoreEvmK256Device({ wallet: new RecordingWallet(B), network: NET, accountIndex: 1, finds });
    assert.ok(r.ok === false && r.message === NOT_FOUND);
    ok('restore');
  }
  // 8. a malformed request: refused before the wallet is asked
  {
    const w = new RecordingWallet(A);
    await refusedAsync('restore', () => restoreEvmK256Device({ wallet: w, network: NET, accountIndex: 0 } as any), /needs the network, the account index and finds/, 'a restore without a record or finds');
    assert.equal(w.requests.length, 0);
  }

  // grantees
  const issuer = rnd();
  const g = await EvmK256Grantee.enrol(A, NET, issuer, LABEL, 1n);
  const grec = g.toRecord();
  const { blind: _gb, readSeed: _rs, ...glost } = grec;
  const grequest = granteeBlindMessageBytes({ scheme: 'evm_k256', network: NET, identity: A.addressBytes, issuingAccount: issuer });
  const ids = new Set([hex(g.grantId(issuer))]);
  const gfinds = (x: EvmK256Grantee) => ids.has(hex(x.grantId(issuer)));
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Grantee({ wallet: w, label: LABEL, slot: 1n, record: grec });
    assert.ok(r.ok === true && r.source === 'cache' && eq(r.value.grantId(issuer), g.grantId(issuer)) && eq(r.value.readKey(issuer).secretKey, g.readKey(issuer).secretKey));
    assert.equal(signs(w).length, 0);
    restoreCases.push({ case: 'grantee, cached', source: 'cache', signatures: 0 });
    ok('restore');
  }
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Grantee({ wallet: w, label: LABEL, slot: 1n, record: glost as EvmK256GranteeRecord });
    assert.ok(r.ok === true && r.source === 'stored-format' && eq(r.value.blind, g.blind) && eq(r.value.readKey(issuer).secretKey, g.readKey(issuer).secretKey));
    assert.ok(signs(w).length === 2 && signs(w).every((x) => x.method === 'personalSign' && eq(x.message, grequest)), 'the grantee request of the record');
    assert.deepEqual(r.ok === true && r.value.toRecord(), grec, 'the restored grantee writes the same record, cache included');
    restoreCases.push({ case: 'grantee, cache lost', source: 'stored-format', signatures: 2 });
    ok('restore');
  }
  {
    const w = new RecordingWallet(A);
    const r = await restoreEvmK256Grantee({ wallet: w, label: LABEL, slot: 1n, network: NET, issuingAccount: issuer, finds: gfinds });
    assert.ok(r.ok === true && r.source === 'search' && eq(r.value.grantId(issuer), g.grantId(issuer)));
    ok('restore');
  }
  const NO_GRANT = 'No grant was found in the formats this wallet can sign (EIP-712 V1). Ask the issuing account\'s owner for a new grant to this wallet.';
  {
    const r = await restoreEvmK256Grantee({ wallet: new RecordingWallet(A), label: LABEL, slot: 0n, network: NET, issuingAccount: issuer, finds: gfinds });
    assert.ok(r.ok === false && r.reason === 'not-found' && r.message === NO_GRANT, r.ok === false ? r.message : '');
    restoreCases.push({ case: 'grantee, no record, not found', message: NO_GRANT });
    ok('restore');
  }
  {
    const w = new RecordingWallet(B);
    await refusedAsync('restore', () => restoreEvmK256Grantee({ wallet: w, label: LABEL, slot: 1n, record: glost as EvmK256GranteeRecord }), namedSigner(A, B), 'another key\'s wallet against a grantee record');
  }
  // the restored device writes the record it was restored from (the cache back)
  {
    const r = await restoreEvmK256Device({ wallet: new RecordingWallet(A), record: lost as EvmK256RosterRecord });
    assert.deepEqual(r.ok === true && r.value.toRecord(), rec);
    ok('restore');
  }
  report.restore = restoreCases;
  console.log(`  ✓ restore: ${tally.restore.pass} cases (device and grantee: cache, cache lost, no record found and not found with the restore message, another key's wallet); ${tally.restore.refused} refused`);
}

// ── Every wallet request of this suite ───────────────────────────────────────

{
  const counts = { address: 0, personalSign: 0, signTypedData: 0 };
  const blindRequests = { device: 0, grantee: 0 };
  for (const { r } of ALL_REQUESTS) {
    counts[r.method]++;
    if (r.method === 'signTypedData') {
      assert.doesNotThrow(() => checkEip712V1TypedData(r.typedData), 'every typed data a wallet was asked to sign is V1');
      assert.deepEqual(r.typedData.domain, eip712V1Domain());
    } else if (r.method === 'personalSign') {
      // each request must be, byte for byte, the device or grantee blind
      // request its own lines name
      const text = new TextDecoder().decode(r.message);
      const device = /^Midnight Passport account privacy key \(v1\)\nNetwork: ([a-z0-9-]+)\nWallet: Ethereum address (0x[0-9a-fA-F]{40})\nAccount index: (\d+)\n/.exec(text);
      const grantee = /^Midnight Passport grantee privacy key \(v1\)\nRole: grantee\nNetwork: ([a-z0-9-]+)\nWallet: Ethereum address (0x[0-9a-fA-F]{40})\nIssuing account: ([0-9a-f]{64})\n/.exec(text);
      const unhexAddress = (a: string) => new Uint8Array(Buffer.from(a.slice(2), 'hex'));
      const rebuilt = device
        ? blindMessageBytes({ scheme: 'evm_k256', network: device[1], identity: unhexAddress(device[2]), accountIndex: BigInt(device[3]) })
        : grantee
          ? granteeBlindMessageBytes({ scheme: 'evm_k256', network: grantee[1], identity: unhexAddress(grantee[2]), issuingAccount: new Uint8Array(Buffer.from(grantee[3], 'hex')) })
          : undefined;
      assert.ok(rebuilt && eq(rebuilt, r.message), `every personal_sign request is a blind request: ${text.slice(0, 60)}`);
      blindRequests[device ? 'device' : 'grantee']++;
    }
  }
  assert.ok(counts.personalSign > 0 && counts.signTypedData > 0);
  assert.ok(blindRequests.device > 0 && blindRequests.grantee > 0);
  report.requests = { ...counts, blindRequests };
  ok('requests', counts.personalSign + counts.signTypedData);
  console.log(`  ✓ requests: ${counts.signTypedData} eth_signTypedData_v4 requests, all V1 typed data; ${counts.personalSign} personal_sign requests, all blind requests (${blindRequests.device} device, ${blindRequests.grantee} grantee); ${counts.address} address reads; no other method`);
}

if (process.env.EVIDENCE_DIR) {
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(path.join(process.env.EVIDENCE_DIR, 'evm-k256-client-offline.json'), JSON.stringify({ tally, ...report }, null, 1) + '\n');
}
console.log('\n◆ evm-k256-client-offline: PASS');
