// Arm `sol_ed25519`: the client facade (spec FR-S01 to FR-S03, FR-012,
// FR-013, FR-017; Q19: an arm-owned facade instead of account.ts edits).
//
// THE DEVICE IS A SOLANA WALLET'S PUBLIC KEY: the 32-byte RFC 8032 encoding
// the wallet exports (its base58 address). The contract takes it as a
// Curve25519Point and relates it in-circuit to those 32 bytes
// (`encode_public_key_with_sol_ed25519`), so this module decodes the bytes
// STRICTLY first: canonical y < p, on the curve, in the prime-order subgroup,
// not the identity (descriptors.ts `parseSolanaPublicKey`).
//
// THE BLIND (spec FR-013, Q13, Q16). Entries and grant ids bind a per-account
// secret that the wallet re-derives: the wallet signs the readable request
// message of blind.ts (raw bytes, Solana `signMessage`), twice; both
// signatures must verify and be identical (RFC 8032 signing is
// deterministic, so a wallet that is not, for example an MPC or a hedged
// signer, would lose its accounts on restore and is refused at enrolment);
// blind = SHA-256(pad32("midnight:account:blind:sol:v1") || signature). The
// client keeps (network, account index, key, blind) per device in its roster.
//
// Platform-neutral: no node:crypto, so the same code runs in a browser page.

import { ed25519 } from '@noble/curves/ed25519.js';
import { curve25519FromProjective, isValidCurve25519Point, type Curve25519Point } from '@midnight-ntwrk/compact-runtime';

import { pureCircuits } from './contract.js';
import { base58Encode, parseSolanaPublicKey, solDescriptor, type SolDescriptor } from './descriptors.js';
import { blindMessage, blindMessageBytes, canonicalEd25519Signature, deriveBlind } from './blind.js';
import {
  assertSafeSolMessage, digitsOf, labelBytes, nibblesOf, solFrameNibbles, solAmountShow, solCoinShow, solDeviceHexValues, solDeviceMessageText,
  solGranteeArg, solGranteeHexValues, solGranteeShow, solGrantShow, solGranteeMessageText, solScopeShow, solShow, solTargetArg,
  solTargetShow, type SolAmount, type SolDeviceOperation, type SolGranteeOperation,
} from './sol-ed25519-message.js';
import type { GrantOpening } from './signer.js';

export type { Curve25519Point };

/** The arm's name: the circuit suffix (`<operation>_with_sol_ed25519`). */
export const SOL_ED25519 = 'sol_ed25519' as const;

/** The order L of the prime-order subgroup (RFC 8032). */
export const ED25519_L: bigint = ed25519.Point.Fn.ORDER;

const equalBytes = (a: Uint8Array, b: Uint8Array): boolean => a.length === b.length && a.every((v, i) => v === b[i]);
const toHex = (b: Uint8Array): string => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
const fromHex = (s: string, n: number, what: string): Uint8Array => {
  if (!new RegExp(`^[0-9a-f]{${2 * n}}$`).test(s)) throw new Error(`sol_ed25519: ${what} is ${n} bytes of lower-case hex`);
  return Uint8Array.from(s.match(/../g)!, (h) => parseInt(h, 16));
};
const bigLE = (b: Uint8Array): bigint => { let v = 0n; for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]); return v; };

// ── Keys and signatures: strict decoding (the arm's acceptance policy) ─────

/** The circuit's Curve25519Point for a Solana public key (base58 text or the
 *  32 bytes), decoded strictly: refuses non-canonical encodings, points off
 *  the curve, the identity, and small-order and mixed-order points. */
export function solPublicKeyPoint(key: Uint8Array | string): Curve25519Point {
  const bytes = parseSolanaPublicKey(key);
  const point = curve25519FromProjective(ed25519.Point.fromBytes(bytes, false));
  if (!isValidCurve25519Point(point)) throw new Error('sol_ed25519: the key is not a valid Curve25519Point');
  return { x: point.x, y: point.y };
}

/** The 32-byte RFC 8032 encoding of a Curve25519Point (what the circuit's
 *  `encode_public_key_with_sol_ed25519` computes). */
export function solPublicKeyBytes(pk: Curve25519Point): Uint8Array {
  return ed25519.Point.fromAffine({ x: pk.x, y: pk.y }).toBytes();
}

/** An Ed25519 signature as the circuit takes it (the standard library's
 *  Ed25519Signature): R decoded, s below L, never reduced. */
export interface SolSignatureArg { r: Curve25519Point; s: bigint }

/** Decodes a 64-byte RFC 8032 signature strictly: R a canonical encoding of a
 *  prime-order point other than the identity (the arm's `R != O` rule), S
 *  below L (an S + L twin is refused, never reduced). */
export function decodeSolSignature(signature: Uint8Array): SolSignatureArg {
  if (signature.length !== 64) throw new Error('sol_ed25519: a signature is 64 bytes');
  const rBytes = signature.subarray(0, 32);
  let R;
  try { R = ed25519.Point.fromBytes(rBytes, false); } catch (e: any) {
    throw new Error(`sol_ed25519: the signature's R does not decode (strict RFC 8032): ${e?.message ?? e}`);
  }
  if (!equalBytes(R.toBytes(), rBytes)) throw new Error("sol_ed25519: the signature's R is not canonical");
  if (R.is0()) throw new Error("sol_ed25519: the signature's R is the identity");
  if (R.isSmallOrder()) throw new Error("sol_ed25519: the signature's R has small order");
  if (!R.isTorsionFree()) throw new Error("sol_ed25519: the signature's R is not in the prime-order subgroup");
  const s = bigLE(signature.subarray(32, 64));
  if (s >= ED25519_L) throw new Error("sol_ed25519: the signature's S is not below L (refused, never reduced)");
  const r = curve25519FromProjective(R);
  return { r: { x: r.x, y: r.y }, s };
}

/**
 * The client's pre-check (the arm document's acceptance policy, FR-012):
 * strict decoding of A and of the signature, then cofactorless RFC 8032
 * verification without ZIP-215 relaxations. Throws with a reason; a wallet
 * that signed other bytes, with another key, or in a wrapped format (a
 * Ledger's off-chain envelope) fails here before any proof.
 */
export function verifySolSignature(message: Uint8Array, signature: Uint8Array, key: Uint8Array | string): SolSignatureArg {
  const A = parseSolanaPublicKey(key);
  const sig = decodeSolSignature(signature);
  if (!ed25519.verify(signature, message, A, { zip215: false })) {
    throw new Error('sol_ed25519: the signature does not verify for this key and message');
  }
  return sig;
}

// ── Signers ─────────────────────────────────────────────────────────────────

/** Signs raw bytes and returns the 64-byte signature. Phantom:
 *  `async (m) => (await provider.signMessage(m, 'utf8')).signature`. */
export type SolSignFn = (message: Uint8Array) => Promise<Uint8Array> | Uint8Array;

export interface SolSigner { publicKey: Uint8Array; sign: SolSignFn }

/** A software signer from a 32-byte RFC 8032 seed (the scheme a Solana
 *  wallet uses). Test keys only. */
export function solSoftwareSigner(seed: Uint8Array): SolSigner {
  if (seed.length !== 32) throw new Error('sol_ed25519: a seed is 32 bytes');
  const s = new Uint8Array(seed);
  return { publicKey: ed25519.getPublicKey(s), sign: (m) => ed25519.sign(m, s) };
}

/** The point and 32-byte key of a seed through the CONTRACT's own pure
 *  circuit (spec Q8: SHA-512, clamp, reduce mod L, multiply). */
export function solPublicKeyFromSeed(seed: Uint8Array): { pk: Curve25519Point; key: Uint8Array } {
  if (seed.length !== 32) throw new Error('sol_ed25519: a seed is 32 bytes');
  const [pk, key] = pureCircuits.compute_public_key_with_sol_ed25519(seed);
  return { pk, key };
}

// ── The blind (FR-013) ──────────────────────────────────────────────────────

export interface SolBlindRequest {
  /** The Midnight network name the account lives on ("undeployed", "preview", ...). */
  network: string;
  /** 0 for the wallet's first Passport account on this network, then 1, 2, ... */
  accountIndex: bigint | number;
}

export interface SolBlindRecord {
  scheme: 'sol_ed25519';
  network: string;
  accountIndex: bigint;
  key: Uint8Array;
  blind: Uint8Array;
}

/** The request message's text and bytes for a key (blind.ts, v1). */
export function solBlindMessage(key: Uint8Array | string, req: SolBlindRequest): { text: string; bytes: Uint8Array } {
  const identity = parseSolanaPublicKey(key);
  const r = { scheme: 'sol_ed25519' as const, network: req.network, identity, accountIndex: req.accountIndex };
  return { text: blindMessage(r), bytes: blindMessageBytes(r) };
}

/**
 * Enrolment and restore: the wallet signs the request message twice; each
 * signature must pass the pre-check, and the two must be byte-identical
 * (the sign-twice check). The blind is SHA-256 of the blind tag and the raw
 * 64-byte signature, computed here and checked against the contract's own
 * `derive_blind_with_sol_ed25519`.
 */
export async function deriveSolBlind(signer: SolSigner, req: SolBlindRequest): Promise<SolBlindRecord> {
  const key = parseSolanaPublicKey(signer.publicKey);
  const { bytes } = solBlindMessage(key, req);
  const first = new Uint8Array(await signer.sign(new Uint8Array(bytes)));
  verifySolSignature(bytes, first, key);
  const second = new Uint8Array(await signer.sign(new Uint8Array(bytes)));
  verifySolSignature(bytes, second, key);
  const a = canonicalEd25519Signature(first);
  const b = canonicalEd25519Signature(second);
  if (!equalBytes(a, b)) {
    throw new Error('sol_ed25519: the wallet signed the same message twice with different signatures (not deterministic); refused, it could not restore its accounts');
  }
  const blind = deriveBlind('sol_ed25519', a);
  const viaContract: Uint8Array = pureCircuits.derive_blind_with_sol_ed25519(a);
  if (!equalBytes(blind, viaContract)) throw new Error('sol_ed25519: blind differs from the contract derivation');
  return { scheme: 'sol_ed25519', network: req.network, accountIndex: BigInt(req.accountIndex), key, blind };
}

// ── The device ──────────────────────────────────────────────────────────────

export interface SolDeviceOptions {
  /** The wallet's public key: the 32 bytes or its base58 address. */
  publicKey: Uint8Array | string;
  /** The account's blind (deriveSolBlind). */
  blind: Uint8Array;
  /** The wallet's signMessage; absent for a key known by its public half only. */
  sign?: SolSignFn;
}

export class SolEd25519Device {
  readonly arm = SOL_ED25519;
  /** The 32-byte RFC 8032 key (what the wallet exports and the entry binds). */
  readonly key: Uint8Array;
  /** The circuit's point for the key. */
  readonly pk: Curve25519Point;
  readonly blind: Uint8Array;
  private readonly signFn?: SolSignFn;

  constructor(opts: SolDeviceOptions) {
    this.key = parseSolanaPublicKey(opts.publicKey);
    this.pk = solPublicKeyPoint(this.key);
    if (!(opts.blind instanceof Uint8Array) || opts.blind.length !== 32) throw new Error('sol_ed25519: a blind is 32 bytes');
    this.blind = new Uint8Array(opts.blind);
    this.signFn = opts.sign;
  }

  /** A device from a software signer and its blind record. */
  static fromSigner(signer: SolSigner, record: SolBlindRecord): SolEd25519Device {
    if (!equalBytes(parseSolanaPublicKey(signer.publicKey), record.key)) throw new Error('sol_ed25519: the blind record is for another key');
    return new SolEd25519Device({ publicKey: record.key, blind: record.blind, sign: signer.sign });
  }

  /** The base58 address a Solana wallet shows. */
  get address(): string { return base58Encode(this.key); }

  /** The readable descriptor another readable arm shows for this device. */
  descriptor(): SolDescriptor { return solDescriptor(this.key, this.blind); }

  entryAt(contractAddress: Uint8Array, epoch: bigint, counter: bigint): Uint8Array {
    return pureCircuits.derive_device_entry_with_sol_ed25519({ bytes: contractAddress }, this.pk, this.blind, epoch, counter);
  }

  bootCommitment(salt: Uint8Array): Uint8Array {
    return pureCircuits.derive_boot_commitment_with_sol_ed25519(salt, this.pk, this.blind);
  }

  grantId(contractAddress: Uint8Array, originHash: Uint8Array, slot: bigint): Uint8Array {
    return pureCircuits.derive_grant_id_with_sol_ed25519({ bytes: contractAddress }, this.pk, this.blind, originHash, slot);
  }

  /** `activate_initial_device_with_sol_ed25519(pk, salt, blind)`. */
  activationArgs(salt: Uint8Array): [Curve25519Point, Uint8Array, Uint8Array] {
    if (salt.length !== 32) throw new Error('sol_ed25519: a salt is 32 bytes');
    return [this.pk, new Uint8Array(salt), this.blind];
  }

  /** Asks the wallet to sign raw bytes and runs the pre-check on the result. */
  async signBytes(message: Uint8Array): Promise<{ signature: Uint8Array; sig: SolSignatureArg }> {
    if (!this.signFn) throw new Error('sol_ed25519: this device has no signer');
    const signature = new Uint8Array(await this.signFn(new Uint8Array(message)));
    return { signature, sig: verifySolSignature(message, signature, this.key) };
  }
}

// ── The roster (FR-013: key, blind and account index per device) ──────────

export interface SolRosterEntryJson {
  scheme: 'sol_ed25519';
  network: string;
  accountIndex: string;
  key: string;
  blind: string;
  /** The account's contract address, once deployed (hex). */
  account?: string;
}

/** Serialises a blind record (plus the account, once known) for storage. */
export function solRosterEntry(record: SolBlindRecord, account?: Uint8Array): SolRosterEntryJson {
  return {
    scheme: 'sol_ed25519', network: record.network, accountIndex: record.accountIndex.toString(),
    key: toHex(record.key), blind: toHex(record.blind), ...(account ? { account: toHex(account) } : {}),
  };
}

/** Parses a stored roster entry strictly. */
export function parseSolRosterEntry(json: SolRosterEntryJson): SolBlindRecord & { account?: Uint8Array } {
  if (json?.scheme !== 'sol_ed25519') throw new Error('sol_ed25519: not a sol_ed25519 roster entry');
  if (!/^(0|[1-9][0-9]{0,9})$/.test(json.accountIndex) || BigInt(json.accountIndex) > 0xffffffffn) throw new Error('sol_ed25519: bad account index');
  const record: SolBlindRecord & { account?: Uint8Array } = {
    scheme: 'sol_ed25519', network: json.network, accountIndex: BigInt(json.accountIndex),
    key: parseSolanaPublicKey(fromHex(json.key, 32, 'key')), blind: fromHex(json.blind, 32, 'blind'),
  };
  solBlindMessage(record.key, record);
  if (json.account !== undefined) record.account = fromHex(json.account, 32, 'account');
  return record;
}

// ── Authorisations (registered in signer.ts; the seam's arguments) ─────────
//
// A gated circuit's trailing arguments are the display inputs of its message
// (in the circuit's order), then the authorising material as one struct.

/** The authorising material a `sol_ed25519` device-gated circuit consumes. */
export interface SolEd25519Authorisation {
  arm: 'sol_ed25519';
  pk: Curve25519Point;
  blind: Uint8Array;
  /** The device's current use counter: the rolling-entry position (AUTH-9). */
  use_counter: bigint;
  sig: SolSignatureArg;
  /** The message's display inputs, in the circuit's argument order. */
  showArgs: unknown[];
  /** Exactly what the wallet showed and signed. Not a circuit argument. */
  message: Uint8Array;
  text: string;
}

/** The authorising material a `sol_ed25519` grantee twin consumes. */
export interface SolEd25519GrantAuthorisation {
  arm: 'sol_ed25519';
  pk: Curve25519Point;
  blind: Uint8Array;
  label: Uint8Array;
  sig: SolSignatureArg;
  showArgs: unknown[];
  message: Uint8Array;
  text: string;
}

/** The trailing circuit arguments of a device-gated call. */
export function solEd25519AuthArgs(a: SolEd25519Authorisation): unknown[] {
  return [...a.showArgs, { pk: a.pk, blind: a.blind, use_counter: a.use_counter, sig: a.sig }];
}

/** The trailing circuit arguments of a grantee twin: the grant openings
 *  (slot, scope salt, recipient kind and pin, max coin value, spent so far),
 *  the display inputs, then the authorising material. */
export function solEd25519GrantAuthArgs(o: GrantOpening, a: SolEd25519GrantAuthorisation): unknown[] {
  return [o.slot, o.scopeSalt, o.recipientKind, o.pinnedRecipient, o.maxCoinValue, o.spentPrev,
    ...a.showArgs, { pk: a.pk, blind: a.blind, label: a.label, sig: a.sig }];
}

// ── Messages through the contract's own circuits ──────────────────────────

export interface SolCallContext { contractAddress: Uint8Array; authNonce: bigint }
export interface SolGrantCallContext { contractAddress: Uint8Array; label: string; slot: bigint; issuedAt: bigint; grantNonce: bigint }

/** The message of a device-role operation as the CONTRACT renders it, and the
 *  display inputs (circuit order) it was rendered from. */
export function solDeviceMessageCircuit(key: Uint8Array, ctx: SolCallContext, site: string, o: SolDeviceOperation): { bytes: Uint8Array; showArgs: unknown[] } {
  const pc: any = pureCircuits;
  const self = { bytes: ctx.contractAddress };
  const show = solShow(site, ctx.authNonce);
  const frame = solFrameNibbles(ctx.contractAddress, key);
  const hex = nibblesOf(...solDeviceHexValues(o));
  const base = [self, key, ctx.authNonce];
  let shows: unknown[];
  let bytes: Uint8Array;
  switch (o.op) {
    case 'rotate_enc_key': shows = [show]; bytes = pc.sol_message_rotate_enc_key(...base, o.newKey, show, frame, hex); break;
    case 'append_inbox': shows = [show]; bytes = pc.sol_message_append_inbox(...base, o.entry, show, frame, hex); break;
    case 'withdraw_unshielded': {
      const a = solAmountShow(o.amount); shows = [a, show];
      bytes = pc.sol_message_withdraw_unshielded(...base, o.amount.color, o.amount.amount, { bytes: o.recipient }, a, show, frame, hex); break;
    }
    case 'withdraw_shielded': case 'withdraw_shielded_to_contract': {
      const a = solAmountShow(o.amount), c = solCoinShow(o.coin, o.amount.amount); shows = [a, c, show];
      const f = o.op === 'withdraw_shielded' ? pc.sol_message_withdraw_shielded : pc.sol_message_withdraw_shielded_to_contract;
      bytes = f(...base, { bytes: o.recipient }, o.amount.color, o.amount.amount, o.coin, a, c, show, frame, hex); break;
    }
    case 'add_device': {
      const ts = solTargetShow(o.target); shows = [ts, show];
      bytes = pc.sol_message_add_device(...base, solTargetArg(o.target), ts, show, frame, hex); break;
    }
    case 'remove_device': {
      if (o.literal) {
        const ts = solTargetShow({ tag: '' }); shows = [ts, show];
        bytes = pc.sol_message_remove_device(...base, true, solTargetArg({ tag: '' }), 0n, 0n, (o as Extract<SolDeviceOperation, { literal: true }>).entry, ts, show, frame, hex);
      } else {
        const d = o as Extract<SolDeviceOperation, { literal: false }>;
        const ts = solTargetShow(d.target, d.counter, d.epoch); shows = [ts, show];
        bytes = pc.sol_message_remove_device(...base, false, solTargetArg(d.target), d.counter, d.epoch, new Uint8Array(32), ts, show, frame, hex);
      }
      break;
    }
    case 'issue_grant': {
      const gs = solGranteeShow(o.grantee), ss = solScopeShow(o); shows = [gs, ss, show];
      bytes = pc.sol_message_issue_grant(...base, solGranteeArg(o.grantee), o.opWithdrawUnshielded, o.opWithdrawShielded,
        o.opWithdrawShieldedToContract, o.read, o.color, o.recipientKind, o.recipient, o.maxCoinValue, o.perCallCap, o.cap, o.expiresAt,
        o.rpIdHash, o.readPk, o.windowLen, o.windowCap, { is_some: o.caller !== null, value: { bytes: o.caller ?? new Uint8Array(32) } }, gs, ss, show, frame, hex);
      break;
    }
    case 'revoke_grant': {
      const gs = solGranteeShow(o.grantee); shows = [gs, show];
      bytes = pc.sol_message_revoke_grant(...base, solGranteeArg(o.grantee), gs, show, frame, hex); break;
    }
    case 'revoke_all_grants': shows = [show]; bytes = pc.sol_message_revoke_all_grants(...base, show, frame); break;
    case 'publish_recovery_session': {
      const d = digitsOf(o.phiLen, 3); shows = [d, show];
      bytes = pc.sol_message_publish_recovery_session(...base, o.recoveryPk, o.sessionNonce, ...o.phi, o.phiLen, o.wrap, d, show, frame, hex); break;
    }
    case 'recover_cancel': shows = [show]; bytes = pc.sol_message_recover_cancel(...base, show, frame); break;
  }
  const noHex = o.op === 'revoke_all_grants' || o.op === 'recover_cancel';
  return { bytes, showArgs: noHex ? [...shows, frame] : [...shows, frame, hex] };
}

/** The message of a grantee-role operation as the CONTRACT renders it. */
export function solGranteeMessageCircuit(key: Uint8Array, ctx: SolGrantCallContext, site: string, o: SolGranteeOperation): { bytes: Uint8Array; showArgs: unknown[] } {
  const pc: any = pureCircuits;
  const show = solShow(site, ctx.grantNonce), g = solGrantShow(ctx.label, ctx.slot, ctx.issuedAt);
  const frame = solFrameNibbles(ctx.contractAddress, key);
  const hex = nibblesOf(...solGranteeHexValues(o));
  const base = [{ bytes: ctx.contractAddress }, key, labelBytes(ctx.label), ctx.slot, ctx.issuedAt, ctx.grantNonce];
  const a = solAmountShow(o.amount);
  if (o.op === 'withdraw_unshielded_with_grant') {
    return { showArgs: [a, show, g, frame, hex], bytes: pc.sol_message_withdraw_unshielded_with_grant(...base, o.amount.color, o.amount.amount, { bytes: o.recipient }, a, show, g, frame, hex) };
  }
  const c = solCoinShow(o.coin, o.amount.amount);
  const f = o.op === 'withdraw_shielded_with_grant' ? pc.sol_message_withdraw_shielded_with_grant : pc.sol_message_withdraw_shielded_to_contract_with_grant;
  return { showArgs: [a, c, show, g, frame, hex], bytes: f(...base, { bytes: o.recipient }, o.amount.color, o.amount.amount, o.changeEntry, o.encPk, o.coin, a, c, show, g, frame, hex) };
}

const asText = (b: Uint8Array) => String.fromCharCode(...b);

/**
 * Authorises one device-gated call: renders the message with the contract's
 * circuit AND the independent renderer and refuses any difference; refuses a
 * message that could be read as a Solana transaction or off-chain message;
 * asks the wallet; runs the pre-check (strict R, s < L, R != O, the signature
 * verifies over exactly these bytes).
 */
export async function authoriseSolDevice(device: SolEd25519Device, ctx: SolCallContext, site: string, o: SolDeviceOperation, useCounter: bigint): Promise<SolEd25519Authorisation> {
  const { bytes, showArgs } = solDeviceMessageCircuit(device.key, ctx, site, o);
  const text = solDeviceMessageText({ site, account: ctx.contractAddress, key: device.key, nonce: ctx.authNonce }, o);
  if (asText(bytes) !== text) throw new Error('sol_ed25519: the contract and the renderer disagree on the message; refused');
  assertSafeSolMessage(bytes);
  const { sig } = await device.signBytes(bytes);
  return { arm: 'sol_ed25519', pk: device.pk, blind: device.blind, use_counter: useCounter, sig, showArgs, message: bytes, text };
}

/** The same for a grantee twin. */
export async function authoriseSolGrantee(device: SolEd25519Device, ctx: SolGrantCallContext, site: string, o: SolGranteeOperation): Promise<SolEd25519GrantAuthorisation> {
  const { bytes, showArgs } = solGranteeMessageCircuit(device.key, ctx, site, o);
  const text = solGranteeMessageText({ site, account: ctx.contractAddress, key: device.key, label: ctx.label, slot: ctx.slot, issuedAt: ctx.issuedAt, nonce: ctx.grantNonce }, o);
  if (asText(bytes) !== text) throw new Error('sol_ed25519: the contract and the renderer disagree on the message; refused');
  assertSafeSolMessage(bytes);
  const { sig } = await device.signBytes(bytes);
  return { arm: 'sol_ed25519', pk: device.pk, blind: device.blind, label: labelBytes(ctx.label), sig, showArgs, message: bytes, text };
}

// ── CustodyAccount helpers (S6S) ───────────────────────────────────────────
//
// CustodyAccount (account.ts) routes each `*WithAuth` call to
// `<operation>_with_sol_ed25519` through the registered authArgs branch, so
// the operands go first and this arm's display inputs and authorisation
// follow. What it cannot do for this arm is render the message and find the
// device's use counter; these helpers do (Q19: no account.ts edit).

/** The surface of a CustodyAccount these helpers use. */
export interface SolEd25519AccountSurface {
  addressBytes: Uint8Array;
  ledgerState(): Promise<{ auth_nonce: bigint; device_epoch: bigint; devices: { member(e: Uint8Array): boolean } }>;
}

/** The custody surface (S6S): CustodyAccount's `*WithAuth` calls and its
 *  coin store's `heldCoin` (the coin the held_coin witness will return). */
export interface SolEd25519CustodySurface extends SolEd25519AccountSurface {
  rotateEncKeyWithAuth(newKey: Uint8Array, a: SolEd25519Authorisation): Promise<{ txId: string }>;
  appendInboxWithAuth(entry: Uint8Array, a: SolEd25519Authorisation): Promise<{ txId: string }>;
  withdrawUnshieldedWithAuth(color: Uint8Array, amount: bigint, recipient: Uint8Array, a: SolEd25519Authorisation): Promise<{ txId: string }>;
  withdrawShieldedWithAuth(recipient: Uint8Array, color: Uint8Array, amount: bigint, a: SolEd25519Authorisation): Promise<{ txId: string; change: unknown }>;
  withdrawShieldedToContractWithAuth(recipient: Uint8Array, color: Uint8Array, amount: bigint, a: SolEd25519Authorisation): Promise<{ txId: string; sent: unknown; change: unknown }>;
  heldCoin(color: Uint8Array): Promise<{ nonce: Uint8Array; color: Uint8Array; value: bigint; mt_index: bigint }>;
}

/** How far the restore scan and the counter resolver look (one bound). */
export const SOL_ED25519_COUNTER_SCAN = 4096n;

/** The device's current use counter: the first counter whose entry is live
 *  at the current epoch (MIP-0013 S11 rescan). */
export async function resolveSolEd25519Counter(account: SolEd25519AccountSurface, device: SolEd25519Device, limit = SOL_ED25519_COUNTER_SCAN): Promise<bigint> {
  const l = await account.ledgerState();
  for (let k = 0n; k < limit; k++) {
    if (l.devices.member(device.entryAt(account.addressBytes, l.device_epoch, k))) return k;
  }
  throw new Error('sol_ed25519: no live entry for this device (rescan limit reached)');
}

/** Authorises the next device-gated call of `device` on `account`: the
 *  ledger's auth_nonce, the resolved counter, the message, the signature. */
export async function authoriseSolDeviceOn(account: SolEd25519AccountSurface, device: SolEd25519Device, site: string, o: SolDeviceOperation): Promise<SolEd25519Authorisation> {
  const l = await account.ledgerState();
  const counter = await resolveSolEd25519Counter(account, device);
  return authoriseSolDevice(device, { contractAddress: account.addressBytes, authNonce: l.auth_nonce }, site, o, counter);
}

/** The coin a shielded spend will consume, as the message shows it. Refuses
 *  a stored coin of another colour at the client (FR-010; the circuit
 *  asserts it too). */
export async function solSpentCoin(account: SolEd25519CustodySurface, color: Uint8Array) {
  const c = await account.heldCoin(color);
  if (!equalBytes(c.color, color)) throw new Error('sol_ed25519: the held coin is not of the withdrawn colour');
  return { nonce: c.nonce, color: c.color, value: c.value, mt_index: c.mt_index };
}

/** rotate_enc_key_with_sol_ed25519 through a CustodyAccount. */
export async function rotateEncKeyWithSolEd25519(account: SolEd25519CustodySurface, device: SolEd25519Device, site: string, newKey: Uint8Array) {
  const auth = await authoriseSolDeviceOn(account, device, site, { op: 'rotate_enc_key', newKey });
  return { auth, ...(await account.rotateEncKeyWithAuth(newKey, auth)) };
}

/** append_inbox_with_sol_ed25519: the 192-byte entry in full. */
export async function appendInboxWithSolEd25519(account: SolEd25519CustodySurface, device: SolEd25519Device, site: string, entry: Uint8Array) {
  const auth = await authoriseSolDeviceOn(account, device, site, { op: 'append_inbox', entry });
  return { auth, ...(await account.appendInboxWithAuth(entry, auth)) };
}

/** withdraw_unshielded_with_sol_ed25519 to a 32-byte user address. `amount`
 *  carries the site's decimals and symbol (shown as the site's claim). */
export async function withdrawUnshieldedWithSolEd25519(account: SolEd25519CustodySurface, device: SolEd25519Device, site: string, amount: SolAmount, recipient: Uint8Array) {
  const auth = await authoriseSolDeviceOn(account, device, site, { op: 'withdraw_unshielded', amount, recipient });
  return { auth, ...(await account.withdrawUnshieldedWithAuth(amount.color, amount.amount, recipient, auth)) };
}

/** withdraw_shielded_with_sol_ed25519 to a Zswap coin public key: the
 *  message shows the coin the store holds for the colour (nonce, value,
 *  Merkle index) and the change. */
export async function withdrawShieldedWithSolEd25519(account: SolEd25519CustodySurface, device: SolEd25519Device, site: string, amount: SolAmount, recipient: Uint8Array) {
  const coin = await solSpentCoin(account, amount.color);
  const auth = await authoriseSolDeviceOn(account, device, site, { op: 'withdraw_shielded', amount, recipient, coin });
  return { auth, coin, ...(await account.withdrawShieldedWithAuth(recipient, amount.color, amount.amount, auth)) };
}

/** withdraw_shielded_to_contract_with_sol_ed25519 (direct transfer, MIP-0012
 *  §6.6): the authorisation only, because the call must be composed with the
 *  recipient contract's claim in one transaction. */
export async function authoriseWithdrawShieldedToContractSol(account: SolEd25519CustodySurface, device: SolEd25519Device, site: string, amount: SolAmount, recipientContract: Uint8Array) {
  const coin = await solSpentCoin(account, amount.color);
  const auth = await authoriseSolDeviceOn(account, device, site, { op: 'withdraw_shielded_to_contract', amount, recipient: recipientContract, coin });
  return { auth, coin };
}
