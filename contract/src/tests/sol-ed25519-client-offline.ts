// Arm `sol_ed25519`, offline: the client's format choice, its wrong-signer
// refusal and its blinds per format and role, with software keys behind
// mocked wallets (no node, no proof server).
//
//   1. Formats per wallet: Phantom raw, never off-chain (even when it
//      advertises the off-chain feature); Backpack, Solflare and any other
//      wallet-standard wallet off-chain when they advertise
//      `solana:signOffchainMessage` with version 1, raw when they offer
//      `signMessage`; Ledger and Trezor off-chain only. Every request a
//      mocked wallet receives is recorded: no wallet is asked for a format it
//      cannot sign, at enrolment, at approval or at restore, and the adapters
//      refuse such bytes before calling the wallet.
//   2. The signer check: a signature that does not come from the expected key
//      over the exact bytes asked is refused before proving, at every place a
//      signature comes back (device and grantee approvals, both signatures of
//      the device and grantee blind requests); the refusal names another key
//      only when the signature verifies under it; a refused call sends no
//      transaction.
//   3. Blind requests: raw = blind.ts's request bytes unchanged, off-chain =
//      the off-chain v1 head naming the key, then the same bytes, for both
//      roles; two sessions give equal blinds in each format and role (and
//      equal OpenSSL's); the formats, roles, networks and indexes give
//      different blinds; the record carries the format and caches the blind;
//      a non-deterministic wallet is refused at enrolment, before any
//      transaction.
//   4. Restore: the cache; the stored format; every format the wallet can
//      sign when nothing is stored, with the messages of a device enrolled
//      through another format, for both roles.
//
// Writes $EVIDENCE_DIR/sol-ed25519-client-offline.json when EVIDENCE_DIR is set.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { createHash, createPrivateKey, randomBytes, sign as osslSign } from 'node:crypto';
import { ed25519 } from '@noble/curves/ed25519.js';

import { pureCircuits } from '../wallet/contract.js';
import { base58Encode, grantOriginHash, padTag, solDescriptor } from '../wallet/descriptors.js';
import { SignerMismatchError, blindFormats, blindFormatName, blindMessageBytes, granteeBlindMessageBytes } from '../wallet/blind.js';
import {
  ED25519_L, SolEd25519Device, SolEd25519Grantee, addDeviceWithSolEd25519, authoriseSolDevice, authoriseSolGrantee, checkSolSignature,
  deriveSolBlind, deriveSolGranteeBlind, parseSolRosterEntry, restoreSolBlind, restoreSolGranteeBlind, solBlindSignedBytes, solDeviceFinds,
  solGranteeBlindSignedBytes, solKeyHints, solRosterEntry, solSignerFormats, solSoftwareSigner, type SolEd25519LifecycleSurface, type SolSigner,
} from '../wallet/signer-sol-ed25519.js';
import {
  SOL_FORMATS, SOL_HEAD_LENGTH, SOL_PARSE_BOUND, assertSolBlindRequest, labelBytes, solBlindSignedMessage, solFormatOfSigned, solMessageHead,
  type SolFormat,
} from '../wallet/sol-ed25519-message.js';
import {
  SOL_SIGN_MESSAGE_FEATURE, SOL_SIGN_OFFCHAIN_MESSAGE_FEATURE, solHardwareSigner, solStandardSigner, solWalletFamily, solWalletFormats,
  type SolStandardWallet,
} from '../wallet/sol-ed25519-wallet.js';
import { READABLE_ARMS } from '../wallet/descriptors.js';

// ── tiny harness (fail-closed: every case must PASS) ─────────────────────────

interface Case { group: string; name: string; verdict: 'PASS' | 'FAIL'; detail?: string }
const cases: Case[] = [];
const ok = (group: string, name: string, cond: boolean, detail?: string) => {
  cases.push({ group, name, verdict: cond ? 'PASS' : 'FAIL', ...(detail ? { detail } : {}) });
  if (!cond) console.log(`  ✗ ${group}: ${name}${detail ? ` — ${detail}` : ''}`);
};
/** `fn` must throw, with a message matching `re`. */
const refused = async (group: string, name: string, re: RegExp, fn: () => unknown) => {
  try { await fn(); ok(group, name, false, 'accepted (expected a refusal)'); } catch (e: any) { const m = String(e?.message ?? e); ok(group, name, re.test(m), m.slice(0, 220)); }
};
/** `fn` must throw a SignerMismatchError; `named` is the key it must name
 *  (undefined: the signer unknown). */
const mismatch = async (group: string, name: string, named: Uint8Array | undefined, fn: () => unknown) => {
  try { await fn(); ok(group, name, false, 'accepted (expected the signer check to refuse it)'); } catch (e: any) {
    const good = e instanceof SignerMismatchError && /^signer: refused before proving/.test(e.message)
      && (named === undefined ? e.signer === undefined && /the signer is unknown/.test(e.message) : e.signer !== undefined && eq(e.signer, named) && e.message.includes(base58Encode(named)));
    ok(group, name, good, String(e?.message ?? e).slice(0, 220));
  }
};

const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const eq = (a: Uint8Array, b: Uint8Array) => a.length === b.length && a.every((v, i) => v === b[i]);
const cat = (...p: Uint8Array[]) => { const o = new Uint8Array(p.reduce((t, x) => t + x.length, 0)); let i = 0; for (const x of p) { o.set(x, i); i += x.length; } return o; };
const enc = new TextEncoder();
const dec = new TextDecoder();
const sha256 = (b: Uint8Array) => new Uint8Array(createHash('sha256').update(b).digest());
/** Deterministic test seeds: SHA-256 of a label. */
const seedOf = (label: string) => sha256(enc.encode(`sol-ed25519-client-offline/${label}`));
const rnd = (n: number) => new Uint8Array(randomBytes(n));
const keyOf = (seed: Uint8Array) => ed25519.getPublicKey(seed);
const PKCS8_PREFIX = Buffer.from('302e020100300506032b657004220420', 'hex');
const osslSignBytes = (seed: Uint8Array, m: Uint8Array) => new Uint8Array(osslSign(null, Buffer.from(m), createPrivateKey({ key: Buffer.concat([PKCS8_PREFIX, Buffer.from(seed)]), format: 'der', type: 'pkcs8' })));
const BLIND_TAG = padTag('midnight:account:blind:sol:v1');
const SITE = 'Client test';
const NETWORK = 'undeployed';

// ── mocked wallets ──────────────────────────────────────────────────────────

interface Call { method: 'signMessage' | 'signOffchainMessage' | 'device'; bytes: Uint8Array }
/** A wallet-standard wallet over a software key, recording every request.
 *  `answer` signs instead of the account's key (a wallet that answers with
 *  another key than the one it reports); `offchain` is the advertised
 *  off-chain feature's message versions (absent: no feature); `envelope`
 *  'other' makes the wallet report another off-chain message than the one
 *  asked. */
function standardWallet(o: { name: string; seed: Uint8Array; offchain?: number[]; signMessage?: boolean; answer?: Uint8Array; envelope?: 'same' | 'other'; signed?: 'same' | 'other' }) {
  const calls: Call[] = [];
  const publicKey = keyOf(o.seed);
  const account = { address: base58Encode(publicKey), publicKey };
  const signWith = o.answer ?? o.seed;
  const features: Record<string, unknown> = { 'standard:connect': { version: '1.0.0', connect: async () => ({ accounts: [account] }) } };
  if (o.signMessage !== false) {
    features[SOL_SIGN_MESSAGE_FEATURE] = {
      version: '1.0.0',
      signMessage: async (...inputs: { account: unknown; message: Uint8Array }[]) => inputs.map(({ message }) => {
        calls.push({ method: 'signMessage', bytes: new Uint8Array(message) });
        const signedMessage = o.signed === 'other' ? cat(message, Uint8Array.of(0x20)) : new Uint8Array(message);
        return { signedMessage, signature: ed25519.sign(message, signWith) };
      }),
    };
  }
  if (o.offchain) {
    features[SOL_SIGN_OFFCHAIN_MESSAGE_FEATURE] = {
      version: '1.0.0', supportedMessageVersions: o.offchain,
      signOffchainMessage: async (...inputs: { messageVersion: number; account: { publicKey: Uint8Array }; message: string; requiredSigners: Uint8Array[] }[]) => inputs.map((i) => {
        // the wallet builds the v1 envelope of the text for the required signer
        if (i.messageVersion !== 1 || typeof i.message !== 'string') throw new Error('mock: unsupported request');
        const env = cat(solMessageHead('offchain', i.requiredSigners[0]), enc.encode(i.message));
        calls.push({ method: 'signOffchainMessage', bytes: env });
        return { signedOffchainMessage: o.envelope === 'other' ? cat(env, Uint8Array.of(0x20)) : env, signature: ed25519.sign(env, signWith) };
      }),
    };
  }
  const wallet: SolStandardWallet = { name: o.name, features };
  return { wallet, account, calls, publicKey };
}
/** A hardware wallet over a software key (off-chain only), recording every
 *  request; Ledger's transport takes the envelope, Trezor's the text. */
function hardwareWallet(family: 'ledger' | 'trezor', seed: Uint8Array) {
  const calls: Call[] = [];
  const publicKey = keyOf(seed);
  const signer = solHardwareSigner({
    family, publicKey,
    signOffchain: (envelope, text) => {
      const signed = family === 'ledger' ? envelope : cat(solMessageHead('offchain', publicKey), text);
      calls.push({ method: 'device', bytes: signed });
      return { signature: ed25519.sign(signed, seed), signed };
    },
  });
  return { signer, calls, publicKey };
}
const methods = (calls: Call[]) => calls.map((c) => c.method).join(',');
/** A signer whose signatures come from another key (an impostor answering
 *  for `seed`'s wallet), or whose n-th signature does. */
function foreignSigner(seed: Uint8Array, other: Uint8Array, opts: { from?: number; others?: Uint8Array[] } = {}): SolSigner & { count: () => number } {
  let n = 0;
  return {
    publicKey: keyOf(seed), formats: SOL_FORMATS,
    ...(opts.others ? { others: () => opts.others! } : {}),
    sign: (m: Uint8Array) => { n++; return ed25519.sign(m, n >= (opts.from ?? 1) ? other : seed); },
    count: () => n,
  };
}
/** An account surface whose live entries are `entries` at epoch 0, and whose
 *  calls are recorded (none may happen after a refusal). */
function accountSurface(address: Uint8Array, entries: Uint8Array[]) {
  const set = new Set(entries.map(hex));
  const txs: string[] = [];
  const surface: SolEd25519LifecycleSurface = {
    addressBytes: address,
    ledgerState: async () => ({ auth_nonce: 0n, device_epoch: 0n, devices: { member: (e: Uint8Array) => set.has(hex(e)) } }),
    callTx: new Proxy({}, { get: (_t, name) => async () => { txs.push(String(name)); return { public: { txId: `tx-${txs.length}` } }; } }) as any,
  };
  return { surface, txs };
}

// ── 1. Formats per wallet (FR-015) ──────────────────────────────────────────
{
  const G = '1 formats per wallet';
  ok(G, "SOL_FORMATS is the registry's formats of sol_ed25519 (blindFormats), in its order: raw, offchain",
    JSON.stringify(SOL_FORMATS) === JSON.stringify(blindFormats('sol_ed25519')) && JSON.stringify(SOL_FORMATS) === JSON.stringify(Object.keys(READABLE_ARMS.sol_ed25519.formats))
    && JSON.stringify(SOL_FORMATS) === '["raw","offchain"]', JSON.stringify(SOL_FORMATS));
  ok(G, 'the names shown: raw, off-chain', blindFormatName('sol_ed25519', 'raw') === 'raw' && blindFormatName('sol_ed25519', 'offchain') === 'off-chain');
  ok(G, 'families by wallet-standard name', solWalletFamily('Phantom') === 'phantom' && solWalletFamily('Backpack') === 'backpack' && solWalletFamily('Solflare') === 'solflare'
    && solWalletFamily('Some Wallet') === 'other' && solWalletFamily(undefined) === 'other');
  const sm = { [SOL_SIGN_MESSAGE_FEATURE]: { signMessage: () => [] } };
  const off = (v: number[]) => ({ [SOL_SIGN_OFFCHAIN_MESSAGE_FEATURE]: { supportedMessageVersions: v, signOffchainMessage: () => [] } });
  const table: [string, Parameters<typeof solWalletFormats>[0], SolFormat[]][] = [
    ['Phantom (signMessage)', { family: 'phantom', features: sm }, ['raw']],
    ['Phantom advertising the off-chain feature v1: still raw only', { family: 'phantom', features: { ...sm, ...off([1]) } }, ['raw']],
    ['Backpack with the off-chain feature v1', { family: 'backpack', features: { ...sm, ...off([0, 1]) } }, ['offchain', 'raw']],
    ['Backpack without it', { family: 'backpack', features: sm }, ['raw']],
    ['Solflare with the off-chain feature v1', { family: 'solflare', features: { ...sm, ...off([1]) } }, ['offchain', 'raw']],
    ['Solflare whose feature lacks version 1', { family: 'solflare', features: { ...sm, ...off([0]) } }, ['raw']],
    ['another wallet with signMessage only', { family: 'other', features: sm }, ['raw']],
    ['another wallet with the off-chain feature only', { family: 'other', features: off([1]) }, ['offchain']],
    ['another wallet with neither', { family: 'other', features: {} }, []],
    ['Ledger', { family: 'ledger' }, ['offchain']],
    ['Trezor', { family: 'trezor' }, ['offchain']],
  ];
  for (const [name, p, want] of table) ok(G, `${name}: ${JSON.stringify(want)}`, JSON.stringify(solWalletFormats(p)) === JSON.stringify(want), JSON.stringify(solWalletFormats(p)));
  await refused(G, 'an unknown family is an error', /unknown wallet family/, () => solWalletFormats({ family: 'metamask' as any }));

  // Enrolment, approvals and restore through mocked wallets: each wallet is
  // asked only for what it can sign.
  const s = seedOf('formats');
  const phantom = standardWallet({ name: 'Phantom', seed: s, offchain: [1] });
  const backpack = standardWallet({ name: 'Backpack', seed: s, offchain: [1] });
  const backpackRaw = standardWallet({ name: 'Backpack', seed: s });
  const solflare = standardWallet({ name: 'Solflare', seed: s, offchain: [1] });
  const none = standardWallet({ name: 'Some Wallet', seed: s, signMessage: false });
  const offOnly = standardWallet({ name: 'Some Wallet', seed: s, offchain: [1], signMessage: false });
  const sP = solStandardSigner(phantom.wallet, phantom.account), sB = solStandardSigner(backpack.wallet, backpack.account);
  const sBR = solStandardSigner(backpackRaw.wallet, backpackRaw.account), sS = solStandardSigner(solflare.wallet, solflare.account);
  const sN = solStandardSigner(none.wallet, none.account), sO = solStandardSigner(offOnly.wallet, offOnly.account);
  const req = { network: NETWORK, accountIndex: 0 };
  const rP = await deriveSolBlind(sP, req), rB = await deriveSolBlind(sB, req), rBR = await deriveSolBlind(sBR, req), rS = await deriveSolBlind(sS, req), rO = await deriveSolBlind(sO, req);
  ok(G, 'enrolment: Phantom (advertising the feature) signs the raw request twice through signMessage, never off-chain', rP.format === 'raw' && methods(phantom.calls) === 'signMessage,signMessage', methods(phantom.calls));
  ok(G, 'enrolment: Backpack with the feature signs the off-chain request twice through signOffchainMessage', rB.format === 'offchain' && methods(backpack.calls) === 'signOffchainMessage,signOffchainMessage', methods(backpack.calls));
  ok(G, 'enrolment: Backpack without the feature signs raw', rBR.format === 'raw' && methods(backpackRaw.calls) === 'signMessage,signMessage');
  ok(G, 'enrolment: Solflare with the feature signs off-chain', rS.format === 'offchain' && methods(solflare.calls) === 'signOffchainMessage,signOffchainMessage');
  ok(G, 'enrolment: a wallet with the off-chain feature only signs off-chain', rO.format === 'offchain' && methods(offOnly.calls) === 'signOffchainMessage,signOffchainMessage');
  ok(G, 'the wallet-built envelope is the client\'s off-chain request (head naming the key, then the request text)',
    eq(backpack.calls[0].bytes, solBlindSignedBytes(keyOf(s), req, 'offchain')) && eq(phantom.calls[0].bytes, solBlindSignedBytes(keyOf(s), req, 'raw')));
  ok(G, 'one key, two formats, two blinds; one format, one blind across wallets', !eq(rP.blind, rB.blind) && eq(rP.blind, rBR.blind) && eq(rB.blind, rS.blind) && eq(rB.blind, rO.blind));
  await refused(G, 'a wallet that signs neither format is refused before it is asked', /lists no format/, () => deriveSolBlind(sN, req));
  ok(G, '... and was not asked', none.calls.length === 0);
  await refused(G, 'Phantom is never asked for the off-chain request', /cannot sign the offchain format/, () => deriveSolBlind(sP, { ...req, format: 'offchain' }));
  await refused(G, "Phantom's adapter refuses off-chain bytes without asking it", /cannot sign the offchain format; not asked/, () => sP.sign(solBlindSignedBytes(keyOf(s), req, 'offchain')));
  await refused(G, 'a Phantom device cannot be made to sign off-chain approvals', /cannot sign the offchain format/, () => SolEd25519Device.fromSigner(sP, rP, 'offchain'));
  ok(G, 'Phantom was asked twice in all (the enrolment)', phantom.calls.length === 2);
  // approvals in the device's format
  const ctx = { contractAddress: seedOf('account'), authNonce: 3n };
  const dP = SolEd25519Device.fromSigner(sP, rP), dB = SolEd25519Device.fromSigner(sB, rB);
  const aP = await authoriseSolDevice(dP, ctx, SITE, { op: 'rotate_enc_key', newKey: seedOf('k') }, 0n);
  const aB = await authoriseSolDevice(dB, ctx, SITE, { op: 'rotate_enc_key', newKey: seedOf('k') }, 0n);
  ok(G, 'a Phantom approval is raw (signMessage of the raw head and the text), flag false', aP.offchain === false && phantom.calls[2]?.method === 'signMessage' && eq(phantom.calls[2].bytes, aP.message));
  ok(G, 'a Backpack approval is off-chain (signOffchainMessage of the approval text), flag true', aB.offchain === true && backpack.calls[2]?.method === 'signOffchainMessage'
    && eq(backpack.calls[2].bytes, aB.message) && dec.decode(aB.message.subarray(SOL_HEAD_LENGTH)) === aB.text);
  // restore without a record: every format the wallet can sign, none other
  const finds = async () => false;
  const before = { p: phantom.calls.length, b: backpack.calls.length };
  await restoreSolBlind(sP, { network: NETWORK, accountIndex: 0, finds });
  await restoreSolBlind(sB, { network: NETWORK, accountIndex: 0, finds });
  ok(G, "restore without a record: Phantom is asked raw only, Backpack both formats in the arm's order (raw, then off-chain)", methods(phantom.calls.slice(before.p)) === 'signMessage,signMessage'
    && methods(backpack.calls.slice(before.b)) === 'signMessage,signMessage,signOffchainMessage,signOffchainMessage', methods(backpack.calls.slice(before.b)));
  // hardware
  const ledger = hardwareWallet('ledger', s), trezor = hardwareWallet('trezor', s);
  const rL = await deriveSolBlind(ledger.signer, req), rT = await deriveSolBlind(trezor.signer, req);
  ok(G, 'Ledger and Trezor enrol off-chain, with the same blind as Backpack (one key, one format)', rL.format === 'offchain' && rT.format === 'offchain' && eq(rL.blind, rB.blind) && eq(rT.blind, rB.blind)
    && methods(ledger.calls) === 'device,device' && methods(trezor.calls) === 'device,device');
  await refused(G, 'a hardware device is never asked for the raw request', /cannot sign the raw format/, () => deriveSolBlind(ledger.signer, { ...req, format: 'raw' }));
  await refused(G, "a hardware adapter refuses raw bytes without asking the device", /cannot sign the raw format; not asked/, () => trezor.signer.sign(solBlindSignedBytes(keyOf(s), req, 'raw')));
  ok(G, 'the devices were asked twice each in all', ledger.calls.length === 2 && trezor.calls.length === 2);
  const lying = solHardwareSigner({ family: 'trezor', publicKey: keyOf(s), signOffchain: (envelope) => ({ signature: ed25519.sign(envelope, s), signed: cat(envelope, Uint8Array.of(0x20)) }) });
  await refused(G, 'a device that reports another off-chain message than the one asked is refused', /another off-chain message than the one asked/, () => deriveSolBlind(lying, req));
  // a wallet that reports other signed bytes than asked
  const liarOff = standardWallet({ name: 'Solflare', seed: s, offchain: [1], envelope: 'other' });
  await refused(G, 'a wallet that reports another off-chain message than the one asked is refused', /another off-chain message than the one asked/, () => deriveSolBlind(solStandardSigner(liarOff.wallet, liarOff.account), req));
  const liarRaw = standardWallet({ name: 'Phantom', seed: s, signed: 'other' });
  await refused(G, 'a wallet that reports other signed bytes than asked is refused', /signed other bytes than asked/, () => deriveSolBlind(solStandardSigner(liarRaw.wallet, liarRaw.account), req));
  await refused(G, 'an account whose address is not its key is refused', /address and key disagree/, () => solStandardSigner(phantom.wallet, { address: base58Encode(keyOf(seedOf('x'))), publicKey: keyOf(s) }));
  await refused(G, 'a signer that lists a format twice is refused', /a format twice/, () => solSignerFormats({ publicKey: keyOf(s), sign: () => new Uint8Array(64), formats: ['raw', 'raw'] }));
  await refused(G, 'a signer that lists an unknown format is refused', /has no format/, () => solSignerFormats({ publicKey: keyOf(s), sign: () => new Uint8Array(64), formats: ['raw', 'eip712-v1' as any] }));
}

// ── 2. The signer check (FR-016) ────────────────────────────────────────────
{
  const G = '2 the signer check';
  const a = seedOf('signer A'), b = seedOf('signer B'), c = seedOf('signer C');
  const A = keyOf(a), B = keyOf(b), C = keyOf(c);
  const req = { network: NETWORK, accountIndex: 0 };
  const recA = await deriveSolBlind(solSoftwareSigner(a), req);
  const ctx = { contractAddress: seedOf('account 2'), authNonce: 9n };
  const op = { op: 'rotate_enc_key' as const, newKey: seedOf('k2') };
  for (const format of ['raw', 'offchain'] as const) {
    const dev = (s: SolSigner) => new SolEd25519Device({ publicKey: A, blind: recA.blind, signer: s, format });
    await mismatch(G, `${format} device approval signed by another key B, B connected: refused, B named`, B, () => authoriseSolDevice(dev(foreignSigner(a, b, { others: [B] })), ctx, SITE, op, 0n));
    await mismatch(G, `${format} device approval signed by B, B not connected: refused, the signer unknown`, undefined, () => authoriseSolDevice(dev(foreignSigner(a, b, { others: [C] })), ctx, SITE, op, 0n));
    await mismatch(G, `${format} device approval signed by B, only A itself and malformed keys offered: unknown`, undefined,
      () => authoriseSolDevice(dev(foreignSigner(a, b, { others: [A, new Uint8Array(31), new Uint8Array(32)] })), ctx, SITE, op, 0n));
    const gctx = { contractAddress: seedOf('issuer'), label: 'Example dApp', slot: 1n, issuedAt: 5n, grantNonce: 2n };
    const G0 = new SolEd25519Grantee(dev(foreignSigner(a, b, { others: [C, B] })), 'Example dApp');
    await mismatch(G, `${format} grantee approval signed by B: refused, B named`, B, () => authoriseSolGrantee(G0.device, gctx, SITE,
      { op: 'withdraw_unshielded_with_grant', amount: { color: new Uint8Array(32), amount: 5n, decimals: 0, symbol: 'TOK' }, recipient: seedOf('r') }));
    await mismatch(G, `${format} device blind: the first signature from B, refused, B named`, B, () => deriveSolBlind(foreignSigner(a, b, { others: [B] }), { ...req, format }));
    const second = foreignSigner(a, b, { from: 2, others: [B] });
    await mismatch(G, `${format} device blind: the second signature from B, refused at the second, B named`, B, () => deriveSolBlind(second, { ...req, format }));
    ok(G, `${format} device blind: the wallet was asked exactly twice`, second.count() === 2);
    const issuing = seedOf('issuing');
    await mismatch(G, `${format} grantee blind: the first signature from B`, B, () => deriveSolGranteeBlind(foreignSigner(a, b, { others: [B] }), { network: NETWORK, issuingAccount: issuing, format }));
    await mismatch(G, `${format} grantee blind: the second signature from B`, undefined, () => deriveSolGranteeBlind(foreignSigner(a, b, { from: 2 }), { network: NETWORK, issuingAccount: issuing, format }));
  }
  // a malformed signature is refused for what it is, under any key
  const bad: SolSigner = { publicKey: A, formats: SOL_FORMATS, sign: (m) => { const s = ed25519.sign(m, a); const o = Uint8Array.from(s); const L = ED25519_L; let v = 0n; for (let i = 63; i >= 32; i--) v = (v << 8n) | BigInt(o[i]); v += L; for (let i = 32; i < 64; i++) { o[i] = Number(v & 0xffn); v >>= 8n; } return o; } };
  await refused(G, 'S + L (a malleated twin) is refused as not below L, not as another signer', /S is not below L/, () => deriveSolBlind(bad, req));
  // the Backpack-for-Phantom shape: a "Phantom" entry reporting Phantom's
  // key while another extension signs with its own
  const p = seedOf('phantom'), k = seedOf('backpack');
  const twin = standardWallet({ name: 'Phantom', seed: p, answer: k });
  const sTwin = solStandardSigner(twin.wallet, twin.account, { others: () => [keyOf(k)] });
  await mismatch(G, "a wallet entry reporting Phantom's key, answered with Backpack's: enrolment refused, Backpack's key named", keyOf(k), () => deriveSolBlind(sTwin, req));
  const sTwin2 = solStandardSigner(twin.wallet, twin.account);
  await mismatch(G, '... and without Backpack connected: the signer unknown', undefined, () => deriveSolBlind(sTwin2, req));
  const recP = await deriveSolBlind(solSoftwareSigner(p, ['raw']), req);
  await mismatch(G, "... and an approval through it: refused, Backpack's key named", keyOf(k),
    () => authoriseSolDevice(new SolEd25519Device({ publicKey: keyOf(p), blind: recP.blind, signer: sTwin }), ctx, SITE, op, 0n));
  // before proving: no transaction follows a refused signature
  const owner = SolEd25519Device.fromSigner(foreignSigner(a, b, { from: 1 }) as SolSigner, recA);
  const { surface, txs } = accountSurface(ctx.contractAddress, [owner.entryAt(ctx.contractAddress, 0n, 0n)]);
  await mismatch(G, 'add_device approved by a wallet answering with another key: refused', undefined,
    () => addDeviceWithSolEd25519(surface, owner, SITE, solDescriptor(C, seedOf('blind C'))));
  ok(G, '... before any transaction (none sent)', txs.length === 0, txs.join(','));
  const honest = SolEd25519Device.fromSigner(solSoftwareSigner(a), recA);
  const r = await addDeviceWithSolEd25519(surface, honest, SITE, solDescriptor(C, seedOf('blind C')));
  ok(G, 'control: the honest wallet passes the check and its call is sent', txs.length === 1 && txs[0] === 'add_device_with_sol_ed25519' && typeof r.txId === 'string');
  // the check itself
  const m = solBlindSignedBytes(A, req, 'raw'), sig = ed25519.sign(m, a);
  let passed = false;
  try { checkSolSignature(m, sig, A, [B]); passed = true; } catch { passed = false; }
  ok(G, 'checkSolSignature passes the right key over the exact bytes', passed);
  await mismatch(G, 'checkSolSignature over one changed byte: unknown, B not named on its word', undefined, () => checkSolSignature(cat(m.subarray(0, 10), Uint8Array.of(m[10] ^ 1), m.subarray(11)), sig, A, [B]));
}

// ── 3. Blind requests per format and role (FR-013, SC-010) ──────────────────
{
  const G = '3 blind requests';
  const s = seedOf('blinds'), K = keyOf(s);
  const issuing = seedOf('issuing account');
  const dreq = { network: NETWORK, accountIndex: 0 }, greq = { network: NETWORK, issuingAccount: issuing };
  const rawD = blindMessageBytes({ scheme: 'sol_ed25519', network: NETWORK, identity: K, accountIndex: 0 });
  const rawG = granteeBlindMessageBytes({ scheme: 'sol_ed25519', network: NETWORK, identity: K, issuingAccount: issuing });
  ok(G, "raw device request = blind.ts's request bytes, unchanged", eq(solBlindSignedBytes(K, dreq, 'raw'), rawD));
  ok(G, "raw grantee request = blind.ts's grantee request bytes, unchanged", eq(solGranteeBlindSignedBytes(K, greq, 'raw'), rawG));
  ok(G, 'off-chain device request = ff "solana offchain" 01 01, the key, then the same bytes', eq(solBlindSignedBytes(K, dreq, 'offchain'), cat(Uint8Array.of(0xff, ...enc.encode('solana offchain'), 1, 1), K, rawD)));
  ok(G, 'off-chain grantee request = the same head, then the same bytes', eq(solGranteeBlindSignedBytes(K, greq, 'offchain'), cat(Uint8Array.of(0xff, ...enc.encode('solana offchain'), 1, 1), K, rawG)));
  ok(G, 'raw requests start "Midn" and stay below the parse bound; the off-chain ones start with 0xff; each is classified as its format',
    [rawD, rawG].every((b) => dec.decode(b.subarray(0, 4)) === 'Midn' && b.length < SOL_PARSE_BOUND && solFormatOfSigned(b) === 'raw')
    && [solBlindSignedBytes(K, dreq, 'offchain'), solGranteeBlindSignedBytes(K, greq, 'offchain')].every((b) => b[0] === 0xff && solFormatOfSigned(b) === 'offchain'));
  await refused(G, 'an approval text is not a blind request', /not a blind request/, () => assertSolBlindRequest(enc.encode('Midnight Passport approval (sol v1)\nOperation: x')));
  await refused(G, 'binary bytes are not a blind request', /printable ASCII/, () => solBlindSignedMessage('raw', K, Uint8Array.of(0xff, 0x4d)));
  // two sessions per format and role; independent oracle: OpenSSL's signature
  const blinds: Record<string, string> = {};
  for (const format of ['raw', 'offchain'] as const) {
    const s1 = await deriveSolBlind(solSoftwareSigner(s), { ...dreq, format });
    const s2 = await deriveSolBlind(solSoftwareSigner(new Uint8Array(s)), { ...dreq, format });
    const oracle = sha256(cat(BLIND_TAG, osslSignBytes(s, solBlindSignedBytes(K, dreq, format))));
    ok(G, `device, ${format}: two sessions give the same blind, OpenSSL's, and the record names the format`, eq(s1.blind, s2.blind) && eq(s1.blind, oracle) && s1.format === format && s2.format === format);
    const g1 = await deriveSolGranteeBlind(solSoftwareSigner(s), { ...greq, format });
    const g2 = await deriveSolGranteeBlind(solSoftwareSigner(new Uint8Array(s)), { ...greq, format });
    const goracle = sha256(cat(BLIND_TAG, osslSignBytes(s, solGranteeBlindSignedBytes(K, greq, format))));
    ok(G, `grantee, ${format}: two sessions give the same blind, OpenSSL's, and the record names the format`, eq(g1.blind, g2.blind) && eq(g1.blind, goracle) && g1.format === format && eq(g1.issuingAccount, issuing));
    blinds[`device-${format}`] = hex(s1.blind); blinds[`grantee-${format}`] = hex(g1.blind);
    const other = await deriveSolBlind(solSoftwareSigner(s), { network: NETWORK, accountIndex: 1, format });
    const otherNet = await deriveSolBlind(solSoftwareSigner(s), { network: 'preview', accountIndex: 0, format });
    ok(G, `device, ${format}: another account index or network gives another blind`, !eq(other.blind, s1.blind) && !eq(otherNet.blind, s1.blind));
  }
  ok(G, 'four different blinds: device and grantee, raw and off-chain', new Set(Object.values(blinds)).size === 4, JSON.stringify(blinds));
  ok(G, 'the default format is the signer\'s first: raw for a software signer, off-chain for one that lists off-chain first',
    (await deriveSolBlind(solSoftwareSigner(s), dreq)).format === 'raw' && (await deriveSolBlind(solSoftwareSigner(s, ['offchain', 'raw']), dreq)).format === 'offchain');
  // the record: format required, blind as the cache
  const rec = await deriveSolBlind(solSoftwareSigner(s), { ...dreq, format: 'offchain' });
  const acct = seedOf('the account');
  const j = solRosterEntry(rec, acct), back = parseSolRosterEntry(JSON.parse(JSON.stringify(j)));
  ok(G, 'roster entry round trip with the format and the cached blind', j.format === 'offchain' && back.format === 'offchain' && eq(back.blind!, rec.blind) && eq(back.key, K) && eq(back.account!, acct));
  const jn = solRosterEntry(rec, acct, { cacheBlind: false }), backN = parseSolRosterEntry(JSON.parse(JSON.stringify(jn)));
  ok(G, 'roster entry without the cache: the format and index kept, no blind stored', jn.blind === undefined && backN.blind === undefined && backN.format === 'offchain' && backN.accountIndex === 0n);
  await refused(G, 'a roster entry without a format is refused', /has no format/, () => parseSolRosterEntry({ ...j, format: undefined as any }));
  await refused(G, 'a roster entry with another arm\'s format is refused', /has no format/, () => parseSolRosterEntry({ ...j, format: 'eip712-v1' }));
  await refused(G, 'a roster entry with a format that is an Object.prototype key is refused', /has no format/, () => parseSolRosterEntry({ ...j, format: 'toString' }));
  await refused(G, 'a device from a record without its blind is refused (restore it first)', /restore it first/, () => SolEd25519Device.fromSigner(solSoftwareSigner(s), backN as any));
  const dev = SolEd25519Device.fromSigner(solSoftwareSigner(s), rec);
  const devRaw = SolEd25519Device.fromSigner(solSoftwareSigner(s, ['raw']), rec);
  ok(G, "a device signs approvals in its record's format when its wallet can, else in the wallet's first format", dev.format === 'offchain' && devRaw.format === 'raw' && eq(devRaw.blind, rec.blind));
  // non-deterministic wallets are refused at enrolment, before any transaction
  const L = ED25519_L;
  const hedgedOf = (seed: Uint8Array): SolSigner => {
    const h = createHash('sha512').update(seed).digest().subarray(0, 32); h[0] &= 248; h[31] &= 127; h[31] |= 64;
    let x = 0n; for (let i = 31; i >= 0; i--) x = (x << 8n) | BigInt(h[i]); const a = x % L;
    const le = (v: bigint) => { const o = new Uint8Array(32); for (let i = 0; i < 32; i++) { o[i] = Number(v & 0xffn); v >>= 8n; } return o; };
    return { publicKey: keyOf(seed), formats: SOL_FORMATS, sign: (m) => {
      let r = 0n; for (const v of rnd(64)) r = (r << 8n) | BigInt(v); r %= L;
      const R = ed25519.Point.BASE.multiply(r).toBytes();
      const kh = createHash('sha512').update(cat(R, keyOf(seed), m)).digest(); let k = 0n; for (let i = 63; i >= 0; i--) k = (k << 8n) | BigInt(kh[i]);
      return cat(R, le((r + (k % L) * a) % L));
    } };
  };
  const hedged = hedgedOf(seedOf('hedged'));
  const owner = SolEd25519Device.fromSigner(solSoftwareSigner(s), await deriveSolBlind(solSoftwareSigner(s), dreq));
  const { surface, txs } = accountSurface(acct, [owner.entryAt(acct, 0n, 0n)]);
  for (const format of ['raw', 'offchain'] as const) {
    await refused(G, `a non-deterministic wallet (valid, different signatures) is refused at enrolment, ${format}`, /not deterministic/, async () => {
      const r = await deriveSolBlind(hedged, { ...dreq, format });
      await addDeviceWithSolEd25519(surface, owner, SITE, solDescriptor(hedged.publicKey, r.blind));
    });
    await refused(G, `... and as a grantee, ${format}`, /not deterministic/, () => deriveSolGranteeBlind(hedged, { ...greq, format }));
  }
  ok(G, '... before any transaction (no add_device sent)', txs.length === 0, txs.join(','));
}

// ── 4. Restore (US4) ─────────────────────────────────────────────────────────
{
  const G = '4 restore';
  const s = seedOf('restore'), K = keyOf(s);
  const acct = seedOf('restore account');
  const req = { network: NETWORK, accountIndex: 0 };
  // a device enrolled through Phantom (raw), a live entry at counter 2
  const phantomW = standardWallet({ name: 'Phantom', seed: s });
  const phantom = solStandardSigner(phantomW.wallet, phantomW.account);
  const enrolled = await deriveSolBlind(phantom, req);
  const entry = (blind: Uint8Array, k = 2n) => new SolEd25519Device({ publicKey: K, blind }).entryAt(acct, 0n, k);
  const { surface } = accountSurface(acct, [entry(enrolled.blind)]);
  const finds = solDeviceFinds(surface, K, 16n);
  const ledger = hardwareWallet('ledger', s);
  const backpackW = standardWallet({ name: 'Backpack', seed: s, offchain: [1] });
  const backpack = solStandardSigner(backpackW.wallet, backpackW.account);
  const n0 = phantomW.calls.length;
  const cached = await restoreSolBlind(phantom, { ...req, stored: { format: 'raw', blind: enrolled.blind }, finds });
  ok(G, 'with the cached blind: used as it is, the wallet not asked', cached.ok === true && cached.source === 'cache' && eq(cached.matches[0].blind, enrolled.blind) && phantomW.calls.length === n0);
  const stored = await restoreSolBlind(phantom, { ...req, stored: { format: 'raw' }, finds });
  ok(G, 'with the stored format and no cache: derived again in it, the same blind, raw asked only', stored.ok === true && stored.source === 'stored-format'
    && eq(stored.matches[0].blind, enrolled.blind) && methods(phantomW.calls.slice(n0)) === 'signMessage,signMessage');
  const want1 = "This device's privacy key was derived in the raw format, which this wallet cannot sign, so it cannot be derived again here. Use a wallet that signs the raw format, or add this wallet as a new device from another device of the account, or through the account's recovery.";
  const l1 = await restoreSolBlind(ledger.signer, { ...req, stored: { format: 'raw' }, finds });
  ok(G, 'a Ledger with the same seed and the stored record (raw): the format needed named, nothing derived, the device not asked (US4 scenario 2)',
    l1.ok === false && l1.reason === 'format-unavailable' && l1.message === want1 && ledger.calls.length === 0, l1.ok === false ? l1.message : 'ok');
  const want2 = "No account was found in the formats this wallet can sign (off-chain). The device may have been enrolled through another format (raw). Add this wallet as a new device from another device of the account, or through the account's recovery.";
  const l2 = await restoreSolBlind(ledger.signer, { ...req, finds });
  ok(G, 'the same Ledger without a record: off-chain tried, not found, the other format named, the remedy given (US4 scenario 2)',
    l2.ok === false && l2.reason === 'not-found' && l2.message === want2 && JSON.stringify(l2.tried) === '["offchain"]' && JSON.stringify(l2.untried) === '["raw"]'
    && methods(ledger.calls) === 'device,device', l2.ok === false ? l2.message : 'ok');
  const nb = backpackW.calls.length;
  const b1 = await restoreSolBlind(backpack, { ...req, finds });
  ok(G, 'Backpack (both formats) without a record: both formats tried, the raw device found', b1.ok === true && b1.source === 'search' && b1.matches.length === 1
    && b1.matches[0].format === 'raw' && eq(b1.matches[0].blind, enrolled.blind) && methods(backpackW.calls.slice(nb)) === 'signMessage,signMessage,signOffchainMessage,signOffchainMessage',
    methods(backpackW.calls.slice(nb)));
  const offRec = await deriveSolBlind(backpack, req);
  const both = accountSurface(acct, [entry(enrolled.blind), entry(offRec.blind, 0n)]);
  const b2 = await restoreSolBlind(backpack, { ...req, finds: solDeviceFinds(both.surface, K, 16n) });
  ok(G, 'a key enrolled in both formats: both devices found', b2.ok === true && b2.matches.length === 2 && b2.matches.map((m) => m.format).join(',') === 'raw,offchain',
    b2.ok === true ? b2.matches.map((m) => m.format).join(',') : b2.message);
  const nb2 = backpackW.calls.length;
  const b3 = await restoreSolBlind(backpack, { ...req, stored: { format: 'offchain' }, finds });
  ok(G, 'a stored off-chain record on a wallet of both formats: off-chain only, never the other format', b3.ok === true && b3.source === 'stored-format'
    && eq(b3.matches[0].blind, offRec.blind) && methods(backpackW.calls.slice(nb2)) === 'signOffchainMessage,signOffchainMessage');
  const none = standardWallet({ name: 'Some Wallet', seed: s, signMessage: false });
  const sNone: SolSigner = { ...solStandardSigner(none.wallet, none.account), formats: [] };
  await refused(G, 'a wallet that signs no format: nothing asked', /lists no format/, () => restoreSolBlind(sNone, { ...req, finds }));
  await refused(G, 'a stored record with another arm\'s format is refused before the wallet is asked', /has no format/, () => restoreSolBlind(phantom, { ...req, stored: { format: 'eip712-v1' }, finds }));
  // grantee role
  const issuing = seedOf('restore issuer');
  const g = await deriveSolGranteeBlind(phantom, { network: NETWORK, issuingAccount: issuing });
  const grantId = (blind: Uint8Array) => { const pk = new SolEd25519Device({ publicKey: K, blind }).pk, h = solKeyHints(pk);
    return pureCircuits.derive_grant_id_with_sol_ed25519({ bytes: issuing }, pk, h.pk_bytes, h.pk_x, blind, grantOriginHash(labelBytes('Example dApp')), 1n); };
  const live = new Set([hex(grantId(g.blind))]);
  const gfinds = async (blind: Uint8Array) => live.has(hex(grantId(blind)));
  const g1 = await restoreSolGranteeBlind(phantom, { network: NETWORK, issuingAccount: issuing, finds: gfinds });
  ok(G, 'grantee without a record: the grant found in the raw format', g1.ok === true && g1.matches[0].format === 'raw' && eq(g1.matches[0].blind, g.blind));
  const want3 = "No grant was found in the formats this wallet can sign (off-chain). The grant may have been issued through another format (raw). Ask the issuing account's owner for a new grant to this wallet.";
  const g2 = await restoreSolGranteeBlind(ledger.signer, { network: NETWORK, issuingAccount: issuing, finds: gfinds });
  ok(G, "grantee on the Ledger without a record: the grantee's message (another format named, a new grant)", g2.ok === false && g2.message === want3, g2.ok === false ? g2.message : 'ok');
  const g3 = await restoreSolGranteeBlind(ledger.signer, { network: NETWORK, issuingAccount: issuing, stored: { format: 'raw' }, finds: gfinds });
  ok(G, "grantee on the Ledger with the stored record: the format needed named", g3.ok === false && g3.reason === 'format-unavailable'
    && /^This grant's privacy key was derived in the raw format, which this wallet cannot sign/.test(g3.message));
}

// ── report ───────────────────────────────────────────────────────────────────
const failed = cases.filter((c) => c.verdict !== 'PASS');
for (const g of [...new Set(cases.map((c) => c.group))]) {
  const cs = cases.filter((c) => c.group === g);
  console.log(`  ${cs.every((c) => c.verdict === 'PASS') ? '✓' : '✗'} ${g}: ${cs.filter((c) => c.verdict === 'PASS').length}/${cs.length}`);
}
const verdict = failed.length ? 'FAIL' : 'PASS';
if (process.env.EVIDENCE_DIR) {
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(path.join(process.env.EVIDENCE_DIR, 'sol-ed25519-client-offline.json'),
    JSON.stringify({ suite: 'sol-ed25519-client-offline', ranAt: new Date().toISOString(), node: process.version, cases, verdict }, null, 2) + '\n');
}
console.log(`\n◆ sol-ed25519-client-offline: ${verdict} (${cases.length} cases, ${failed.length} failed)`);
process.exit(verdict === 'PASS' ? 0 : 1);
