// The `evm_k256` arm's client facade: an Ethereum
// account (MetaMask, or any EIP-712 wallet) as a Passport device or grantee.
//
// The device is its 20-byte Ethereum address, BLINDED:
// every entry, boot commitment and grant id binds the address together with a
// per-account secret, the blind, which the client derives from the wallet's
// own deterministic signature over a readable request message:
//
//   1. The client builds the request for (network, wallet address, account
//      index) with blind.ts `blindMessage` (the wallet shows it as text).
//   2. The wallet signs it TWICE with `personal_sign` (EIP-191). Both
//      signatures must have the same canonical form (low-S r || s): RFC 6979
//      makes an honest wallet deterministic, and a hedged or MPC wallet,
//      whose blind could never be re-derived, is refused here.
//   3. blind = SHA-256(pad32("midnight:account:blind:evm:v1") || r || s).
//   4. The device's public point is RECOVERED from that same signature (a
//      wallet never exposes it), and its address must be the wallet's own.
//
// The roster record (`EvmK256RosterRecord`) persists the address, point,
// blind, network and account index per device. A restored client re-derives
// blind_0, blind_1, ... from the wallet and finds its accounts by testing
// entries (`entryAt`) against each account's device set.
//
// As a GRANTEE the wallet derives its blind from a different request (blind.ts
// `granteeBlindMessage`): it names the role, the network, the wallet and
// the issuing account, and has no account index. The issuer must know a
// grantee's blind (it derives the grant id and is shown in the issuer's
// approvals), so a grantee never uses a device blind, and every issuer gets a
// blind of its own.
//
// A grantee also derives the X25519 key the account seals its records to
// when a grant allows reading (`read_pk`; the record stores SHA-256 of it in
// the clear). The key is fresh per issuing account and per grant, so two
// grants never share a published hash: its secret is
// SHA-256(read seed || account || site label || slot), clamped per RFC 7748,
// where the read seed is SHA-256(pad32("midnight:account:read:evm:v1")
// || r || s) over the same canonical signature as the grantee blind. The
// issuer learns the blind, never the signature, so it cannot derive the key.
//
// Every derivation goes through the contract's own exported pure circuits
// (`derive_*_with_evm_k256`), so the client and the circuit can never
// disagree. The readable EIP-712 approvals are built by the arm's codec
// (`evm-k256-codec.ts`).

import { secp256k1 } from '@noble/curves/secp256k1.js';
import { x25519 } from '@noble/curves/ed25519.js';
import { keccak_256 } from '@noble/hashes/sha3.js';
import { sha256 } from '@noble/hashes/sha2.js';

import { pureCircuits, type Secp256k1Point } from './contract.js';
import {
  blindMessageBytes,
  granteeBlindMessageBytes,
  canonicalEvmSignature,
  deriveBlind,
  sameCanonicalSignature,
} from './blind.js';
import { DESCRIPTOR_TAGS, checkDescriptor, evmAddressOf, evmChecksumAddress, grantOriginHash, padTag, parseEvmAddress, type Descriptor } from './descriptors.js';
import { typedDataDigest, evmK256Messages, type Eip712TypedData, type EvmK256DescriptorInput, type EvmK256GranteeInput, type IssueScope, type SiteAmount, type SpentCoin } from './evm-k256-codec.js';
import type { GrantOpening } from './signer.js';
import {
  evmK256KeyHint, evmK256SeamHint, evmK256GrantSeamHint, evmK256AmountHint, evmK256CoinHint,
  evmK256DescriptorHint, evmK256RemoveHint, evmK256GranteeHint, evmK256IssueHint,
  solArgs, EVM_K256_SOL_FILLER_ARGS,
  type EvmAddressHint, type EvmK256SeamHint, type EvmK256GrantSeamHint,
} from './evm-k256-hints.js';
export { solArgs, solKeyOf, EVM_K256_SOL_FILLER_ARGS, type EvmK256SolArgs } from './evm-k256-hints.js';

// ── Signatures ───────────────────────────────────────────────────────────────

export const SECP256K1_ORDER = secp256k1.Point.Fn.ORDER;

/** An ECDSA signature as the circuit ABI carries it (`Secp256k1EcdsaSignature`). */
export interface EvmEcdsaSignature { r: bigint; s: bigint }

/** A 65-byte wallet signature `r || s || v`, parsed. Both S forms are kept as
 *  given: the contract accepts both; the rolling entry makes a
 *  malleated twin single-use. */
export interface ParsedEvmSignature extends EvmEcdsaSignature { v: number; recovery: 0 | 1 }

const be32 = (v: bigint): Uint8Array => {
  const o = new Uint8Array(32);
  let x = v;
  for (let i = 31; i >= 0; i--) { o[i] = Number(x & 0xffn); x >>= 8n; }
  return o;
};
const beInt = (b: Uint8Array): bigint => { let v = 0n; for (const x of b) v = (v << 8n) | BigInt(x); return v; };
const hex = (b: Uint8Array): string => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
const unhex = (h: string): Uint8Array => {
  if (!/^([0-9a-f]{2})*$/i.test(h)) throw new Error('evm_k256: not a hex string');
  return new Uint8Array((h.match(/../g) ?? []).map((x) => parseInt(x, 16)));
};
const eq = (a: Uint8Array, b: Uint8Array): boolean => a.length === b.length && a.every((v, i) => v === b[i]);

/** Parses the wallet form `r || s || v` (65 bytes; v in {0, 1, 27, 28}).
 *  Refuses r or s outside [1, n). */
export function parseEvmSignature(sig: Uint8Array): ParsedEvmSignature {
  if (sig.length !== 65) throw new Error(`evm_k256: a wallet signature is 65 bytes (r || s || v), got ${sig.length}`);
  const r = beInt(sig.subarray(0, 32));
  const s = beInt(sig.subarray(32, 64));
  if (r === 0n || r >= SECP256K1_ORDER) throw new Error('evm_k256: signature r outside [1, n)');
  if (s === 0n || s >= SECP256K1_ORDER) throw new Error('evm_k256: signature s outside [1, n)');
  const v = sig[64];
  if (![0, 1, 27, 28].includes(v)) throw new Error(`evm_k256: signature v must be 0, 1, 27 or 28, got ${v}`);
  return { r, s, v, recovery: (v >= 27 ? v - 27 : v) as 0 | 1 };
}

/** The wallet form of a parsed signature. */
export function serialiseEvmSignature(sig: ParsedEvmSignature): Uint8Array {
  return new Uint8Array([...be32(sig.r), ...be32(sig.s), sig.v]);
}

/** The malleated twin (r, n - s): the same digest and key, the other S and
 *  recovery parity. The contract accepts it; used by the tests. */
export function highSTwin(sig: ParsedEvmSignature): ParsedEvmSignature {
  const recovery = (sig.recovery ^ 1) as 0 | 1;
  return { r: sig.r, s: SECP256K1_ORDER - sig.s, recovery, v: sig.v >= 27 ? 27 + recovery : recovery };
}

/** The point that produced `sig` over `digest` (the wallet never exposes it). */
export function recoverEvmPoint(digest: Uint8Array, sig: ParsedEvmSignature): Secp256k1Point {
  if (digest.length !== 32) throw new Error('evm_k256: a digest is 32 bytes');
  const p = new secp256k1.Signature(sig.r, sig.s, sig.recovery).recoverPublicKey(digest).toAffine();
  return { x: p.x, y: p.y, identity: false } as Secp256k1Point;
}

/** EIP-191 version 0x45 (`personal_sign`):
 *  keccak256("\x19Ethereum Signed Message:\n" || decimal length || message). */
export function personalMessageDigest(message: Uint8Array): Uint8Array {
  const prefix = new TextEncoder().encode(`\x19Ethereum Signed Message:\n${message.length}`);
  return keccak_256(new Uint8Array([...prefix, ...message]));
}

/** The 20-byte address of a point, `keccak256(x_be || y_be)[12..32]`: what
 *  the circuit's `evm_address` computes (the standard library's
 *  `secp256k1EthereumAddress` gives the same value). */
export function evmAddressOfPoint(pk: { x: bigint; y: bigint }): Uint8Array {
  return evmAddressOf(pk);
}

// ── Wallets ──────────────────────────────────────────────────────────────────

/** What the arm needs from an Ethereum wallet. A browser adapter maps these to
 *  `eth_accounts`, `personal_sign` and `eth_signTypedData_v4`. */
export interface EvmWallet {
  /** The wallet's 20-byte address. */
  address(): Promise<Uint8Array>;
  /** EIP-191 `personal_sign` over the raw message bytes: 65 bytes r || s || v. */
  personalSign(message: Uint8Array): Promise<Uint8Array>;
  /** EIP-712 `eth_signTypedData_v4` over typed data: 65 bytes r || s || v. */
  signTypedData(typedData: Eip712TypedData): Promise<Uint8Array>;
}

/**
 * A software wallet over a secp256k1 secret key, deterministic (RFC 6979) as
 * MetaMask is. For tests and the debug page only; real devices are wallets.
 * `hedged` adds fresh randomness to every signature, which is how the tests
 * stand in for a non-deterministic (MPC, hedged-nonce) wallet.
 */
export class SoftwareEvmWallet implements EvmWallet {
  readonly pk: Secp256k1Point;
  readonly addressBytes: Uint8Array;

  constructor(readonly sk: bigint, readonly hedged = false) {
    if (sk <= 0n || sk >= SECP256K1_ORDER) throw new Error('evm_k256: a secret key is in [1, n)');
    this.pk = pureCircuits.compute_public_point_with_evm_k256(sk);
    this.addressBytes = evmAddressOfPoint(this.pk);
  }

  static generate(): SoftwareEvmWallet {
    for (;;) {
      const b = new Uint8Array(32);
      globalThis.crypto.getRandomValues(b);
      const k = beInt(b);
      if (k > 0n && k < SECP256K1_ORDER) return new SoftwareEvmWallet(k);
    }
  }

  async address(): Promise<Uint8Array> { return new Uint8Array(this.addressBytes); }

  /** Signs a 32-byte digest: the wallet form r || s || v (v = 27 + parity).
   *  noble returns low-S, as MetaMask does. */
  signDigest(digest: Uint8Array): Uint8Array {
    const rec = secp256k1.sign(digest, be32(this.sk), {
      prehash: false, format: 'recovered', ...(this.hedged ? { extraEntropy: true } : {}),
    });
    // noble's recovered format: the recovery byte, then r || s.
    return new Uint8Array([...rec.subarray(1), 27 + rec[0]]);
  }

  async personalSign(message: Uint8Array): Promise<Uint8Array> {
    return this.signDigest(personalMessageDigest(message));
  }

  /** Signs the EIP-712 digest of `typedData` (the client codec's general
   *  encoder, as a wallet hashes it). */
  async signTypedData(typedData: Eip712TypedData): Promise<Uint8Array> {
    return this.signDigest(typedDataDigest(typedData));
  }
}

// ── The device ───────────────────────────────────────────────────────────────

/** The roster record a client persists per device. Test keys never
 *  appear here: a device is its wallet. */
export interface EvmK256RosterRecord {
  scheme: 'evm_k256';
  network: string;
  accountIndex: string;
  /** EIP-55 checksummed address. */
  address: string;
  /** The recovered public point, big-endian hex coordinates. */
  pk: { x: string; y: string };
  /** The blind, hex. A secret: it links this wallet to the account. */
  blind: string;
}

/** The authorising material an `evm_k256` device-gated circuit consumes
 *  (the trailing `EvmK256Auth` struct argument). The circuit derives the
 *  address from `pk`; `blind` and `use_counter` are ledger-pinned openings of
 *  the device's entry. */
export interface EvmK256Authorisation {
  arm: 'evm_k256';
  pk: Secp256k1Point;
  use_counter: bigint;
  blind: Uint8Array;
  sig: EvmEcdsaSignature;
  /** The seam's checked byte hints (evm-k256-hints.ts), from the signed typed data. */
  hint: EvmK256SeamHint;
  /** The operation's own hints, when the circuit takes them as its trailing
   *  argument (authArgs appends them). */
  op?: unknown;
}

/** The authorising material an `evm_k256` grantee twin consumes (the
 *  trailing `EvmK256GrantAuth` plus the site label, which grantAuthArgs
 *  places before the opening). The grantee's site label (32-byte
 *  zero-padded ASCII) travels with it; the circuit derives `origin_hash`
 *  from it, and the grant id from the address of `pk`, `blind`, that
 *  origin hash and the slot. */
export interface EvmK256GrantAuthorisation {
  arm: 'evm_k256';
  pk: Secp256k1Point;
  blind: Uint8Array;
  label: Uint8Array;
  sig: EvmEcdsaSignature;
  /** The grant seam's checked byte hints, from the signed typed data. */
  hint: EvmK256GrantSeamHint;
  /** The operation's own hints (grantAuthArgs appends them). */
  op?: unknown;
}

export interface EvmBlindEnrolment {
  message: Uint8Array;
  signatures: [Uint8Array, Uint8Array];
  canonical: Uint8Array;
  blind: Uint8Array;
  pk: Secp256k1Point;
  address: Uint8Array;
}

/**
 * Steps 1-4 of the header: request the blind signature twice, refuse a
 * non-deterministic wallet, derive the blind, recover the point and check
 * that it is the wallet's address.
 */
export async function enrolEvmBlind(
  wallet: EvmWallet, network: string, accountIndex: bigint | number,
): Promise<EvmBlindEnrolment> {
  const address = await wallet.address();
  if (address.length !== 20) throw new Error('blind: the wallet address is 20 bytes');
  return enrolWithRequest(wallet, address, blindMessageBytes({ scheme: 'evm_k256', network, identity: address, accountIndex }));
}

/**
 * The same steps for the wallet as a GRANTEE of `issuingAccount`: the
 * base's grantee request names the role, the network, the wallet and the
 * issuing account's address, and has no account index, so the blind the
 * issuer learns is never a device blind and is different for every issuer.
 */
export async function enrolEvmGranteeBlind(
  wallet: EvmWallet, network: string, issuingAccount: Uint8Array,
): Promise<EvmBlindEnrolment> {
  const address = await wallet.address();
  if (address.length !== 20) throw new Error('blind: the wallet address is 20 bytes');
  return enrolWithRequest(wallet, address, granteeBlindMessageBytes({ scheme: 'evm_k256', network, identity: address, issuingAccount }));
}

async function enrolWithRequest(wallet: EvmWallet, address: Uint8Array, message: Uint8Array): Promise<EvmBlindEnrolment> {
  const first = await wallet.personalSign(message);
  const second = await wallet.personalSign(message);
  if (!sameCanonicalSignature('evm_k256', first, second)) {
    throw new Error('blind: the wallet signed the privacy-key request twice with different signatures (not deterministic); this wallet cannot be a Passport device');
  }
  const canonical = canonicalEvmSignature(first);
  const pk = recoverEvmPoint(personalMessageDigest(message), parseEvmSignature(first));
  if (!eq(evmAddressOfPoint(pk), address)) {
    throw new Error('blind: the privacy-key signature does not recover to the wallet address');
  }
  return { message, signatures: [first, second], canonical, blind: deriveBlind('evm_k256', canonical), pk, address };
}

/**
 * An `evm_k256` device of one account: its wallet (when present), its
 * recovered point, its address and the account's blind.
 */
export class EvmK256Device {
  readonly arm = 'evm_k256' as const;
  readonly address: Uint8Array;

  constructor(
    readonly pk: Secp256k1Point,
    readonly blind: Uint8Array,
    readonly network: string,
    readonly accountIndex: bigint,
    readonly wallet?: EvmWallet,
  ) {
    if (blind.length !== 32) throw new Error('evm_k256: a blind is 32 bytes');
    if (pk.x === 0n && pk.y === 0n) throw new Error('evm_k256: the point at infinity is not a device key');
    secp256k1.Point.fromAffine({ x: pk.x, y: pk.y }).assertValidity();
    this.address = evmAddressOfPoint(pk);
  }

  /** Enrols `wallet` for the account at `accountIndex` on `network`. */
  static async enrol(wallet: EvmWallet, network: string, accountIndex: bigint | number): Promise<EvmK256Device> {
    const e = await enrolEvmBlind(wallet, network, accountIndex);
    return new EvmK256Device(e.pk, e.blind, network, BigInt(accountIndex), wallet);
  }

  /** The EIP-55 form a wallet shows. */
  get checksumAddress(): string { return evmChecksumAddress(this.address); }

  /** The device's rolling entry at an account, epoch and use counter. */
  entryAt(contractAddress: Uint8Array, epoch: bigint, counter: bigint): Uint8Array {
    return pureCircuits.derive_device_entry_with_evm_k256({ bytes: contractAddress }, this.address, this.blind, epoch, counter);
  }

  /** The boot commitment for an account deployed with `salt`. */
  bootCommitment(salt: Uint8Array): Uint8Array {
    return pureCircuits.derive_boot_commitment_with_evm_k256(salt, this.address, this.blind);
  }

  /** The grant id of this key as a grantee of `contractAddress`. */
  grantId(contractAddress: Uint8Array, originHash: Uint8Array, slot: bigint): Uint8Array {
    return pureCircuits.derive_grant_id_with_evm_k256({ bytes: contractAddress }, this.address, this.blind, originHash, slot);
  }

  /**
   * Signs `typedData` with the device's wallet (`eth_signTypedData_v4`) and
   * returns the circuit's authorising material. Refuses a signature that does
   * not recover to this device's point (a wallet that signed with another
   * account). The signature is passed on as the wallet produced it; the
   * contract accepts both S forms.
   */
  async authorise(typedData: Eip712TypedData, useCounter: bigint): Promise<EvmK256Authorisation> {
    if (!this.wallet) throw new Error('evm_k256: this device has no wallet');
    return this.authorisationFrom(typedData, await this.wallet.signTypedData(typedData), useCounter);
  }

  /** The authorising material of an existing wallet signature over `typedData`. */
  authorisationFrom(typedData: Eip712TypedData, signature: Uint8Array, useCounter: bigint): EvmK256Authorisation {
    const sig = parseEvmSignature(signature);
    const pk = recoverEvmPoint(typedDataDigest(typedData), sig);
    if (pk.x !== this.pk.x || pk.y !== this.pk.y) throw new Error('evm_k256: the signature does not recover to this device');
    const m = typedData.message as { account: string; authNonce: string };
    const hint = evmK256SeamHint(this.pk, unhex(m.account.replace(/^0x/, '')), typedDataDigest(typedData), BigInt(m.authNonce));
    return { arm: 'evm_k256', pk: this.pk, use_counter: useCounter, blind: this.blind, sig: { r: sig.r, s: sig.s }, hint };
  }

  /** The arguments of `activate_initial_device_with_evm_k256`. */
  activationArgs(salt: Uint8Array): [Secp256k1Point, Uint8Array, Uint8Array, EvmAddressHint] {
    return [this.pk, salt, this.blind, evmK256KeyHint(this.pk)];
  }

  /** The roster record to persist. */
  toRecord(): EvmK256RosterRecord {
    return {
      scheme: 'evm_k256', network: this.network, accountIndex: this.accountIndex.toString(),
      address: this.checksumAddress,
      pk: { x: this.pk.x.toString(16).padStart(64, '0'), y: this.pk.y.toString(16).padStart(64, '0') },
      blind: hex(this.blind),
    };
  }

  /** A device from its roster record; refuses a record whose address is not
   *  its point's. */
  static fromRecord(rec: EvmK256RosterRecord, wallet?: EvmWallet): EvmK256Device {
    if (rec.scheme !== 'evm_k256') throw new Error('evm_k256: not an evm_k256 roster record');
    const pk = { x: BigInt('0x' + rec.pk.x), y: BigInt('0x' + rec.pk.y), identity: false } as Secp256k1Point;
    const d = new EvmK256Device(pk, unhex(rec.blind), rec.network, BigInt(rec.accountIndex), wallet);
    if (!eq(d.address, parseEvmAddress(rec.address))) throw new Error('evm_k256: the roster address is not the point\'s address');
    return d;
  }
}

/** How far a client scans use counters for a device's live entry: the
 *  counter resolver and restore use the same bound. */
export const EVM_K256_COUNTER_SCAN = 4096n;

/**
 * Restore: the account indexes 0..maxIndex of `wallet` on `network`,
 * each with its blind re-derived from the wallet, tested against candidate
 * accounts' device sets at counters below maxCounter (default: the resolver's
 * bound). Returns every match. The wallet is asked for 2 x (maxIndex + 1)
 * `personal_sign` approvals (two per index: the sign-twice check).
 */
export async function restoreEvmDevices(
  wallet: EvmWallet,
  network: string,
  accounts: { address: Uint8Array; epoch: bigint; isMember: (entry: Uint8Array) => boolean }[],
  opts: { maxIndex?: number; maxCounter?: bigint } = {},
): Promise<{ accountIndex: bigint; account: Uint8Array; counter: bigint; device: EvmK256Device }[]> {
  const found: { accountIndex: bigint; account: Uint8Array; counter: bigint; device: EvmK256Device }[] = [];
  const maxIndex = opts.maxIndex ?? 4;
  const maxCounter = opts.maxCounter ?? EVM_K256_COUNTER_SCAN;
  for (let i = 0; i <= maxIndex; i++) {
    const device = await EvmK256Device.enrol(wallet, network, i);
    for (const a of accounts) {
      for (let k = 0n; k < maxCounter; k++) {
        if (a.isMember(device.entryAt(a.address, a.epoch, k))) {
          found.push({ accountIndex: BigInt(i), account: a.address, counter: k, device });
          break;
        }
      }
    }
  }
  return found;
}

// ── Calls (the arm-owned facade) ────────────────────────────────────────
//
// The account client (account.ts) routes authorised calls by the
// Authorisation's arm through the registered authArgs branch, so the
// `*WithAuth` methods of a CustodyAccount reach this arm's circuits unchanged.
// What it cannot do for this arm is build the readable message and find the
// device's use counter; these helpers do.

/** The surface of a CustodyAccount these helpers use. */
export interface EvmK256AccountSurface {
  addressBytes: Uint8Array;
  ledgerState(): Promise<{ auth_nonce: bigint; device_epoch: bigint; devices: { member(e: Uint8Array): boolean } }>;
  rotateEncKeyWithAuth(newKey: Uint8Array, a: EvmK256Authorisation): Promise<{ txId: string }>;
}

/** The device's current use counter: the first counter whose entry is live at
 *  the current epoch (MIP-0013 S11 rescan). */
export async function resolveEvmK256Counter(account: EvmK256AccountSurface, device: EvmK256Device, limit = EVM_K256_COUNTER_SCAN): Promise<bigint> {
  const l = await account.ledgerState();
  for (let k = 0n; k < limit; k++) {
    if (l.devices.member(device.entryAt(account.addressBytes, l.device_epoch, k))) return k;
  }
  throw new Error('evm_k256: no live entry for this device (rescan limit reached)');
}

/** rotate_enc_key_with_evm_k256: the RotateEncKey message, signed by the
 *  device's wallet, then the call. */
export async function rotateEncKeyWithEvmK256(account: EvmK256AccountSurface, device: EvmK256Device, newKey: Uint8Array) {
  const l = await account.ledgerState();
  const counter = await resolveEvmK256Counter(account, device);
  const typedData = evmK256Messages.rotateEncKey({ account: account.addressBytes, device: device.address, authNonce: l.auth_nonce }, newKey);
  const auth = await device.authorise(typedData, counter);
  return { typedData, auth, ...(await account.rotateEncKeyWithAuth(newKey, auth)) };
}

// ── Custody ────────────────────────────────────────────────────────────

/** The surface of a CustodyAccount the custody helpers use (CustodyAccount
 *  routes each `*WithAuth` call to `<operation>_with_evm_k256` through the
 *  registered authArgs branch). */
export interface EvmK256CustodySurface extends EvmK256AccountSurface {
  appendInboxWithAuth(entry: Uint8Array, a: EvmK256Authorisation): Promise<{ txId: string }>;
  withdrawUnshieldedWithAuth(color: Uint8Array, amount: bigint, recipient: Uint8Array, a: EvmK256Authorisation): Promise<{ txId: string }>;
  withdrawShieldedWithAuth(recipient: Uint8Array, color: Uint8Array, amount: bigint, a: EvmK256Authorisation): Promise<{ txId: string; change: unknown }>;
  withdrawShieldedToContractWithAuth(recipient: Uint8Array, color: Uint8Array, amount: bigint, a: EvmK256Authorisation): Promise<{ txId: string; sent: unknown; change: unknown }>;
  /** The coin the held_coin witness will return for `color` (the store). */
  heldCoin(color: Uint8Array): Promise<{ nonce: Uint8Array; color: Uint8Array; value: bigint; mt_index: bigint }>;
}

/** The device frame of the next call and the device's counter. */
async function deviceFrame(account: EvmK256AccountSurface, device: EvmK256Device) {
  const l = await account.ledgerState();
  const counter = await resolveEvmK256Counter(account, device);
  return { frame: { account: account.addressBytes, device: device.address, authNonce: l.auth_nonce }, counter };
}

/** The coin a shielded spend will consume, as the approval shows it.
 *  Refuses a stored coin of another colour at the client (the circuit
 *  asserts it too). */
async function spentCoin(account: EvmK256CustodySurface, color: Uint8Array) {
  const c = await account.heldCoin(color);
  if (!eq(c.color, color)) throw new Error('evm_k256: the held coin is not of the withdrawn colour');
  return { nonce: c.nonce, value: c.value, mtIndex: c.mt_index };
}

/** append_inbox_with_evm_k256: the AppendInbox message (the 192-byte
 *  entry in full), signed by the device's wallet, then the call. */
export async function appendInboxWithEvmK256(account: EvmK256CustodySurface, device: EvmK256Device, entry: Uint8Array) {
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.appendInbox(frame, entry);
  const auth = await device.authorise(typedData, counter);
  return { typedData, auth, ...(await account.appendInboxWithAuth(entry, auth)) };
}

/** withdraw_unshielded_with_evm_k256 to a 32-byte user address. */
export async function withdrawUnshieldedWithEvmK256(
  account: EvmK256CustodySurface, device: EvmK256Device, color: Uint8Array, amount: bigint, recipient: Uint8Array, site: SiteAmount,
) {
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.withdrawUnshielded(frame, color, amount, recipient, site);
  const auth = { ...(await device.authorise(typedData, counter)), op: evmK256AmountHint(amount, site) };
  return { typedData, auth, ...(await account.withdrawUnshieldedWithAuth(color, amount, recipient, auth)) };
}

/** withdraw_shielded_with_evm_k256 to a Zswap coin public key: the approval
 *  shows the coin the store holds for `color` (nonce, value, Merkle index)
 *  and the change. */
export async function withdrawShieldedWithEvmK256(
  account: EvmK256CustodySurface, device: EvmK256Device, recipient: Uint8Array, color: Uint8Array, amount: bigint, site: SiteAmount,
) {
  const { frame, counter } = await deviceFrame(account, device);
  const coin = await spentCoin(account, color);
  const typedData = evmK256Messages.withdrawShielded(frame, color, amount, recipient, coin, site);
  const auth = { ...(await device.authorise(typedData, counter)), op: evmK256CoinHint(amount, coin.value, coin.mtIndex, site) };
  return { typedData, auth, coin, ...(await account.withdrawShieldedWithAuth(recipient, color, amount, auth)) };
}

/** withdraw_shielded_to_contract_with_evm_k256 (direct transfer, MIP-0012
 *  §6.6): the typed data and authorisation only, because the call must be
 *  composed with the recipient contract's claim in one transaction (see
 *  `withdrawShieldedToContractWithAuth` for an uncomposed call). */
export async function authoriseWithdrawShieldedToContract(
  account: EvmK256CustodySurface, device: EvmK256Device, recipientContract: Uint8Array, color: Uint8Array, amount: bigint, site: SiteAmount,
) {
  const { frame, counter } = await deviceFrame(account, device);
  const coin = await spentCoin(account, color);
  const typedData = evmK256Messages.withdrawShieldedToContract(frame, color, amount, recipientContract, coin, site);
  return { typedData, coin, auth: { ...(await device.authorise(typedData, counter)), op: evmK256CoinHint(amount, coin.value, coin.mtIndex, site) } };
}

// ── Device lifecycle ───────────────────────────────────────────────────
//
// add_device_with_evm_k256 and remove_device_with_evm_k256 take the other
// key as a readable descriptor, not an entry: the circuit
// derives the entry from it with the target scheme's own recipe. Their ABI
// differs from upstream's add/remove_device(entry), so CustodyAccount's
// entry-typed helpers cannot reach them; these call the circuits directly.

const le32 = (v: bigint): Uint8Array => { const o = new Uint8Array(32); let x = v; for (let i = 0; i < 32; i++) { o[i] = Number(x & 0xffn); x >>= 8n; } return o; };
const ZERO32 = new Uint8Array(32);
const ZERO21 = new Uint8Array(21);

/** The circuit's `EvmK256Descriptor` for a readable descriptor: the target
 *  scheme's device tag and its fields (an EVM target's address and privacy
 *  salt; a Solana target's 32-byte key and privacy salt; JubJub, k256 and
 *  P-256 coordinates little-endian, as the recipes bind them; a k256
 *  envelope; a passkey's RP hash and exact origin). The other fields are
 *  zero: no recipe hashes them and no approval shows them. The descriptor is
 *  checked by the strict client decoders first. */
export function evmK256DescriptorInput(descriptor: Descriptor): EvmK256DescriptorInput {
  if (!descriptor || !Object.hasOwn(DESCRIPTOR_TAGS.device, (descriptor as { scheme?: string }).scheme ?? '')) {
    throw new Error('descriptor: not a registered device scheme');
  }
  const d = checkDescriptor(descriptor);
  const base = { tag: padTag(DESCRIPTOR_TAGS.device[d.scheme]), key: ZERO32, key2: ZERO32, address: new Uint8Array(20), envelope: 0n, rp_id_hash: ZERO32, origin: ZERO21 };
  switch (d.scheme) {
    case 'evm_k256': return { ...base, address: new Uint8Array(d.address), key2: new Uint8Array(d.blind) };
    case 'sol_ed25519': return { ...base, key: new Uint8Array(d.key), key2: new Uint8Array(d.blind) };
    case 'jubjub': return { ...base, key: le32(d.x), key2: le32(d.y) };
    case 'k256': return { ...base, key: le32(d.x), key2: le32(d.y), envelope: BigInt(d.envelope) };
    case 'p256': {
      if (!d.policy) throw new Error('descriptor: a passkey device needs its policy (RP hash and origin)');
      return { ...base, key: le32(d.x), key2: le32(d.y), rp_id_hash: new Uint8Array(d.policy.rpIdHash), origin: new Uint8Array(d.policy.origin) };
    }
  }
}

/** The descriptor the literal-entry form passes: unused by the circuit. */
export const EVM_K256_UNUSED_DESCRIPTOR: EvmK256DescriptorInput = {
  tag: padTag(DESCRIPTOR_TAGS.device.evm_k256), key: ZERO32, key2: ZERO32, address: new Uint8Array(20), envelope: 0n, rp_id_hash: ZERO32, origin: ZERO21,
};

/** The surface the device-lifecycle calls use: CustodyAccount's raw call-tx
 *  interface. */
export interface EvmK256LifecycleSurface extends EvmK256AccountSurface {
  callTx: Record<string, (...args: unknown[]) => Promise<any>>;
}

const txIdOf = (r: any): string => {
  const id = r?.public?.txId ?? r?.public?.transactionHash;
  if (!id) throw new Error('evm_k256: the call returned no transaction id');
  return id;
};
const authArg = (a: EvmK256Authorisation) => { const { arm, op, ...auth } = a; return auth; };

/** add_device_with_evm_k256: the AddDevice message ("Gives this key FULL
 *  control of this account" and the target's descriptor), signed, then the
 *  call; the circuit enrols the target at the current epoch and counter 0. */
export async function addDeviceWithEvmK256(account: EvmK256LifecycleSurface, device: EvmK256Device, target: Descriptor) {
  const { frame, counter } = await deviceFrame(account, device);
  const input = evmK256DescriptorInput(target);
  const typedData = evmK256Messages.addDevice(frame, input);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.add_device_with_evm_k256(input, ...solArgs(input), authArg(auth), evmK256DescriptorHint(input));
  return { typedData, auth, input, txId: txIdOf(r) };
}

/** remove_device_with_evm_k256, descriptor form: the target's entry at
 *  (targetEpoch, targetCounter); the epoch may be a future one (removal only
 *  reduces authority). */
export async function removeDeviceWithEvmK256(
  account: EvmK256LifecycleSurface, device: EvmK256Device, target: Descriptor, targetEpoch: bigint, targetCounter: bigint,
) {
  const { frame, counter } = await deviceFrame(account, device);
  const input = evmK256DescriptorInput(target);
  const typedData = evmK256Messages.removeDevice(frame, input, targetEpoch, targetCounter);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.remove_device_with_evm_k256(input, ...solArgs(input), targetEpoch, targetCounter, { is_some: false, value: ZERO32 }, authArg(auth),
    evmK256RemoveHint(input, targetEpoch, targetCounter));
  return { typedData, auth, input, txId: txIdOf(r) };
}

/** remove_device_with_evm_k256, literal-entry form: an entry this wallet
 *  cannot describe, under "Removes a device this wallet cannot identify". */
export async function removeUnknownDeviceWithEvmK256(account: EvmK256LifecycleSurface, device: EvmK256Device, entry: Uint8Array) {
  if (entry.length !== 32) throw new Error('evm_k256: an entry is 32 bytes');
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.removeUnknownDevice(frame, entry);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.remove_device_with_evm_k256(EVM_K256_UNUSED_DESCRIPTOR, ...EVM_K256_SOL_FILLER_ARGS, 0n, 0n, { is_some: true, value: new Uint8Array(entry) }, authArg(auth),
    evmK256RemoveHint(EVM_K256_UNUSED_DESCRIPTOR, 0n, 0n));
  return { typedData, auth, txId: txIdOf(r) };
}

/** This device as a descriptor (another device adds or removes it). */
export const evmDeviceDescriptor = (d: EvmK256Device): Descriptor => ({ scheme: 'evm_k256', address: new Uint8Array(d.address), blind: new Uint8Array(d.blind) });

// ── Scoped grants ──────────────────────────────────────────────────────

/** How a readable owner shows a grantee's site: an `evm_k256` or
 *  `sol_ed25519` grantee by its 32-byte site label (shown as text), a
 *  passkey by its exact 21-byte origin (shown as text), a k256 or JubJub
 *  grantee by its origin hash (shown under the fixed member
 *  `siteLabelHash`; the client shows the client id beside it). */
export type GranteeSite = { label: Uint8Array } | { origin: Uint8Array } | { originHash: Uint8Array; clientId?: string };

/** The circuit's `EvmK256GranteeDescriptor` for a grantee of any scheme
 *  (its key as a readable descriptor, its site, its slot). */
export function evmK256GranteeInput(descriptor: Descriptor, site: GranteeSite, slot: bigint): EvmK256GranteeInput {
  if (!descriptor || !Object.hasOwn(DESCRIPTOR_TAGS['grant-id'], (descriptor as { scheme?: string }).scheme ?? '')) {
    throw new Error('descriptor: not a registered grantee scheme');
  }
  if (slot < 0n || slot > 255n) throw new Error('descriptor: a grant slot is a Uint<8>');
  const d = checkDescriptor(descriptor);
  const base = { tag: padTag(DESCRIPTOR_TAGS['grant-id'][d.scheme]), key: ZERO32, key2: ZERO32, address: new Uint8Array(20), envelope: 0n,
    origin: ZERO21, label: ZERO32, origin_hash: ZERO32, slot };
  const need = (k: 'label' | 'origin' | 'originHash', n: number): Uint8Array => {
    const v = (site as any)[k];
    if (!(v instanceof Uint8Array) || v.length !== n) throw new Error(`descriptor: a ${d.scheme} grantee is shown by its ${k} (${n} bytes)`);
    return new Uint8Array(v);
  };
  switch (d.scheme) {
    case 'evm_k256': return { ...base, address: new Uint8Array(d.address), key2: new Uint8Array(d.blind), label: need('label', 32) };
    case 'sol_ed25519': return { ...base, key: new Uint8Array(d.key), key2: new Uint8Array(d.blind), label: need('label', 32) };
    case 'jubjub': return { ...base, key: le32(d.x), key2: le32(d.y), origin_hash: need('originHash', 32) };
    case 'k256': return { ...base, key: le32(d.x), key2: le32(d.y), envelope: BigInt(d.envelope), origin_hash: need('originHash', 32) };
    case 'p256': return { ...base, key: le32(d.x), key2: le32(d.y), origin: checkPasskeySiteOrigin(d, need('origin', 21)) };
  }
}

/** A passkey grantee's site origin (its own field, apart from
 *  any policy on the key) passes the base's origin rule (21 bytes, visible
 *  ASCII, no quote or backslash; descriptors.ts checkDescriptor), checked by
 *  the base function itself on the key with that origin. */
function checkPasskeySiteOrigin(d: { x: bigint; y: bigint }, origin: Uint8Array): Uint8Array {
  checkDescriptor({ scheme: 'p256', x: d.x, y: d.y, policy: { rpIdHash: new Uint8Array(32), origin } } as Descriptor);
  return origin;
}

/** The tag of a grantee's read seed (client only: the key never enters a circuit). */
export const EVM_K256_GRANT_READ_TAG = 'midnight:account:read:evm:v1';

/** A grant's X25519 read key: the secret (clamped per RFC 7748) and `read_pk`. */
export interface EvmK256ReadKey { secretKey: Uint8Array; publicKey: Uint8Array }

/** The read seed of a grantee blind request's canonical signature. */
export function evmK256GrantReadSeed(canonical: Uint8Array): Uint8Array {
  if (canonical.length !== 64) throw new Error('read key: a canonical signature is 64 bytes');
  return sha256(new Uint8Array([...padTag(EVM_K256_GRANT_READ_TAG), ...canonical]));
}

/** The read key of one grant: fresh per account (32 bytes) and per grant
 *  (site label, 32 bytes, and slot). */
export function evmK256GrantReadKey(readSeed: Uint8Array, account: Uint8Array, label: Uint8Array, slot: bigint): EvmK256ReadKey {
  if (readSeed.length !== 32 || account.length !== 32 || label.length !== 32) throw new Error('read key: the seed, the account and the label are 32 bytes each');
  if (slot < 0n || slot > 255n) throw new Error('read key: a grant slot is a Uint<8>');
  const k = sha256(new Uint8Array([...readSeed, ...account, ...label, Number(slot)]));
  k[0] &= 248; k[31] &= 127; k[31] |= 64;
  return { secretKey: k, publicKey: x25519.getPublicKey(k) };
}

/**
 * An `evm_k256` key as a GRANTEE of an account: its point, its blind (from
 * the grantee blind request, signed with `personal_sign`), the 32-byte site
 * label it is known by, and its slot. Its grant id is
 * derive_grant_id_with_evm_k256(account, address, blind,
 * H(origin tag || label), slot). It signs one readable type per operation
 * over the grant frame (the record's issuedAt and nonce, never auth_nonce).
 */
export class EvmK256Grantee {
  readonly arm = 'evm_k256' as const;
  readonly address: Uint8Array;

  constructor(
    readonly pk: Secp256k1Point,
    readonly blind: Uint8Array,
    readonly label: Uint8Array,
    readonly slot: bigint,
    readonly wallet?: EvmWallet,
    private readonly readSeed?: Uint8Array,
  ) {
    if (blind.length !== 32) throw new Error('evm_k256: a blind is 32 bytes');
    if (label.length !== 32) throw new Error('evm_k256: a site label is 32 bytes');
    if (readSeed && readSeed.length !== 32) throw new Error('evm_k256: a read seed is 32 bytes');
    if (pk.x === 0n && pk.y === 0n) throw new Error('evm_k256: the point at infinity is not a grantee key');
    secp256k1.Point.fromAffine({ x: pk.x, y: pk.y }).assertValidity();
    this.address = evmAddressOfPoint(pk);
  }

  /** A grantee for `wallet` of the account `issuingAccount` on `network` (the
   *  grantee blind request signed twice), known to the owner by `label`
   *  and `slot`. */
  static async enrol(wallet: EvmWallet, network: string, issuingAccount: Uint8Array, label: Uint8Array, slot: bigint): Promise<EvmK256Grantee> {
    const e = await enrolEvmGranteeBlind(wallet, network, issuingAccount);
    return new EvmK256Grantee(e.pk, e.blind, label, slot, wallet, evmK256GrantReadSeed(e.canonical));
  }

  /** This grant's read key on `account` (its `read_pk` goes into the grant
   *  request); needs the grantee's own enrolment (the read seed). */
  readKey(account: Uint8Array): EvmK256ReadKey {
    if (!this.readSeed) throw new Error('evm_k256: this grantee has no read seed (enrol it from its wallet)');
    return evmK256GrantReadKey(this.readSeed, account, this.label, this.slot);
  }

  /** The same grantee under another site label or slot (another grant of the
   *  same issuing account), keeping its wallet and read seed. */
  withGrant(label: Uint8Array, slot: bigint): EvmK256Grantee {
    return new EvmK256Grantee(this.pk, this.blind, label, slot, this.wallet, this.readSeed);
  }

  /** origin_hash of the site label (what the grant id binds). */
  get originHash(): Uint8Array { return grantOriginHash(this.label); }

  grantId(contractAddress: Uint8Array): Uint8Array {
    return pureCircuits.derive_grant_id_with_evm_k256({ bytes: contractAddress }, this.address, this.blind, this.originHash, this.slot);
  }

  /** This grantee as the owner shows it (IssueGrant, RevokeGrant). */
  descriptor(): EvmK256GranteeInput {
    return evmK256GranteeInput({ scheme: 'evm_k256', address: this.address, blind: this.blind }, { label: this.label }, this.slot);
  }

  /** Signs `typedData` with the grantee's wallet; refuses a signature that
   *  does not recover to this grantee's point. */
  async authorise(typedData: Eip712TypedData): Promise<EvmK256GrantAuthorisation> {
    if (!this.wallet) throw new Error('evm_k256: this grantee has no wallet');
    const sig = parseEvmSignature(await this.wallet.signTypedData(typedData));
    const pk = recoverEvmPoint(typedDataDigest(typedData), sig);
    if (pk.x !== this.pk.x || pk.y !== this.pk.y) throw new Error('evm_k256: the signature does not recover to this grantee');
    const m = typedData.message as { account: string; issuedAt: string; grantNonce: string };
    const hint = evmK256GrantSeamHint(this.pk, unhex(m.account.replace(/^0x/, '')), typedDataDigest(typedData), this.label, BigInt(m.issuedAt), BigInt(m.grantNonce));
    return { arm: 'evm_k256', pk: this.pk, blind: this.blind, label: this.label, sig: { r: sig.r, s: sig.s }, hint };
  }
}

/** The surface the grant calls use (CustodyAccount). */
export interface EvmK256GrantSurface extends EvmK256LifecycleSurface {
  heldCoin(color: Uint8Array): Promise<{ nonce: Uint8Array; color: Uint8Array; value: bigint; mt_index: bigint }>;
  encKey(): Promise<Uint8Array>;
  grantRecord(grantId: Uint8Array): Promise<{ issued_at: bigint; nonce: bigint } | null>;
  withdrawUnshieldedWithGrantAuth(color: Uint8Array, amount: bigint, recipient: Uint8Array, opening: GrantOpening, a: EvmK256GrantAuthorisation): Promise<{ txId: string }>;
  withdrawShieldedWithGrantAuth(recipient: Uint8Array, color: Uint8Array, amount: bigint, changeEntry: Uint8Array, encPk: Uint8Array, opening: GrantOpening, a: EvmK256GrantAuthorisation): Promise<{ txId: string; change: unknown }>;
  withdrawShieldedToContractWithGrantAuth(recipient: Uint8Array, color: Uint8Array, amount: bigint, changeEntry: Uint8Array, encPk: Uint8Array, opening: GrantOpening, a: EvmK256GrantAuthorisation): Promise<{ txId: string; sent: unknown; change: unknown }>;
}

const leInt = (b: Uint8Array): bigint => { let v = 0n; for (let i = b.length - 1; i >= 0; i--) v = (v << 8n) | BigInt(b[i]); return v; };

/** A grantee input built elsewhere (not by
 *  `evmK256GranteeInput`) is re-checked before any wallet signs: its tag
 *  must be a registered grant-id tag, and the descriptor it encodes must pass
 *  the strict client decoders (`checkDescriptor`: points on their curves and
 *  in their subgroups, a valid Ed25519 encoding, address and blind lengths).
 *  Returns the input unchanged. */
export function checkEvmK256GranteeInput(g: EvmK256GranteeInput): EvmK256GranteeInput {
  const scheme = (Object.keys(DESCRIPTOR_TAGS['grant-id']) as (keyof typeof DESCRIPTOR_TAGS['grant-id'])[])
    .find((k) => { const t = padTag(DESCRIPTOR_TAGS['grant-id'][k]); return t.length === g.tag.length && t.every((b, i) => b === g.tag[i]); });
  if (!scheme) throw new Error('descriptor: not a registered grant-id tag');
  const d = scheme === 'evm_k256' ? { scheme, address: g.address, blind: g.key2 }
    : scheme === 'sol_ed25519' ? { scheme, key: g.key, blind: g.key2 }
    : scheme === 'jubjub' ? { scheme, x: leInt(g.key), y: leInt(g.key2) }
    : scheme === 'k256' ? { scheme, x: leInt(g.key), y: leInt(g.key2), envelope: Number(g.envelope) }
    : { scheme, x: leInt(g.key), y: leInt(g.key2) };
  checkDescriptor(d as Descriptor);
  if (scheme === 'p256') checkPasskeySiteOrigin(d as { x: bigint; y: bigint }, g.origin);
  return g;
}

/** The circuit arguments of issue_grant_with_evm_k256 after the grantee
 *  (the scope, the read key itself, the caller pin). The grant's scope salt
 *  is no argument: the circuit derives it (evmK256GrantScopeSalt). */
export function evmK256IssueArgs(scope: IssueScope): unknown[] {
  const caller = scope.caller
    ? { is_some: true, value: { bytes: new Uint8Array(scope.caller) } }
    : { is_some: false, value: { bytes: new Uint8Array(32) } };
  return [scope.opWithdrawUnshielded, scope.opWithdrawShielded, scope.opWithdrawShieldedToContract, scope.read,
    scope.color, scope.recipientKind, scope.recipient, scope.maxCoinValue, scope.perCallCap, scope.cap, scope.expiresAt,
    scope.rpIdHash, scope.read ? scope.readPk : new Uint8Array(32), scope.windowLen, scope.windowCap, caller];
}

/** The scope salt issue_grant_with_evm_k256 derives for a grant: from the
 *  issuing device's blind, the account and the auth_nonce of the issuing
 *  call (the frame's authNonce), under the arm's salt tag, through the
 *  account's own pure circuit. The issuer hands it to the grantee, which
 *  opens the grant's commitments with it when it spends. */
export function evmK256GrantScopeSalt(blind: Uint8Array, account: Uint8Array, authNonce: bigint): Uint8Array {
  if (blind.length !== 32 || account.length !== 32) throw new Error('evm_k256: the blind and the account are 32 bytes each');
  return pureCircuits.derive_grant_scope_salt(pureCircuits.salt_tag_evm_k256(), blind, { bytes: account }, authNonce);
}

/** issue_grant_with_evm_k256: the IssueGrant message ("Lets this key use
 *  this account within the limits below", the grantee, every scope field),
 *  signed by the device's wallet, then the call. The record stores
 *  SHA-256(read key) as read_pk_hash. Returns the grant's scope salt, which
 *  the circuit derives and the grantee needs to spend. */
export async function issueGrantWithEvmK256(
  account: EvmK256LifecycleSurface, device: EvmK256Device, grantee: EvmK256GranteeInput, scope: IssueScope,
) {
  checkEvmK256GranteeInput(grantee);
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.issueGrant(frame, grantee, scope);
  const auth = await device.authorise(typedData, counter);
  const scopeSalt = evmK256GrantScopeSalt(device.blind, frame.account, frame.authNonce);
  const r = await account.callTx.issue_grant_with_evm_k256(grantee, ...solArgs(grantee), ...evmK256IssueArgs(scope), authArg(auth),
    evmK256IssueHint(grantee, scope));
  return { typedData, auth, scopeSalt, txId: txIdOf(r) };
}

/** revoke_grant_with_evm_k256: the grantee shown by its descriptor; the
 *  circuit re-derives the grant id. */
export async function revokeGrantWithEvmK256(account: EvmK256LifecycleSurface, device: EvmK256Device, grantee: EvmK256GranteeInput) {
  checkEvmK256GranteeInput(grantee);
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.revokeGrant(frame, grantee);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.revoke_grant_with_evm_k256(grantee, ...solArgs(grantee), authArg(auth), evmK256GranteeHint(grantee));
  return { typedData, auth, txId: txIdOf(r) };
}

/** revoke_all_grants_with_evm_k256. */
export async function revokeAllGrantsWithEvmK256(account: EvmK256LifecycleSurface, device: EvmK256Device) {
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.revokeAllGrants(frame);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.revoke_all_grants_with_evm_k256(authArg(auth));
  return { typedData, auth, txId: txIdOf(r) };
}

// ── Recovery ───────────────────────────────────────────────────────────
//
// The two device-gated recovery operations. The recovery gate itself
// (recover_submit) and finalisation are arm-independent and stay on
// CustodyAccount (recoverSubmit, recoverFinalise).

/** One recovery session's artefact set (recovery MIP section 5), as the
 *  client's own guardian ceremony produced it (a client obligation):
 *  P = s·G for the session's fresh secret, a fresh 32-byte session
 *  identifier, 1..4 public phi values, and the 64-byte wrap. */
export interface EvmK256RecoveryArtefacts {
  recoveryPk: { x: bigint; y: bigint };
  sessionNonce: Uint8Array;
  phi: bigint[];
  wrap: Uint8Array;
}

/** The circuit's operands of a session: the phi slots (unused ones zero) and
 *  the length field. Refuses what the chip would refuse, before any wallet
 *  signature (as upstream's publishRecoverySession does). */
export function evmK256RecoverySession(a: EvmK256RecoveryArtefacts) {
  if (a.phi.length < 1 || a.phi.length > 4) throw new Error(`evm_k256: phi carries ${a.phi.length} entries; the slot bound admits 1..4`);
  if (a.sessionNonce.length !== 32 || a.sessionNonce.every((b) => b === 0)) {
    throw new Error('evm_k256: a session identifier is 32 non-zero bytes (REC-4)');
  }
  if (a.wrap.length !== 64) throw new Error('evm_k256: the recovery wrap is 64 bytes');
  const slots: [bigint, bigint, bigint, bigint] = [0n, 0n, 0n, 0n];
  a.phi.forEach((p, i) => { slots[i] = p; });
  return { recoveryPk: a.recoveryPk, sessionNonce: new Uint8Array(a.sessionNonce), phi: slots, phiLen: BigInt(a.phi.length), wrap: new Uint8Array(a.wrap) };
}

/** publish_recovery_session_with_evm_k256: the PublishRecoverySession
 *  message ("Sets this account's recovery key", the new recovery key, the
 *  session identifier, the four phi values, the length and the 64-byte wrap,
 *  all in full), signed by the device's wallet, then the call. */
export async function publishRecoverySessionWithEvmK256(account: EvmK256LifecycleSurface, device: EvmK256Device, artefacts: EvmK256RecoveryArtefacts) {
  const session = evmK256RecoverySession(artefacts);
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.publishRecoverySession(frame, session);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.publish_recovery_session_with_evm_k256(
    session.recoveryPk, session.sessionNonce, ...session.phi, session.phiLen, session.wrap, authArg(auth));
  return { typedData, auth, txId: txIdOf(r) };
}

/** recover_cancel_with_evm_k256: the CancelRecovery message (the frame
 *  alone: account, device, authNonce), signed, then the call; vetoes the
 *  pending recovery. */
export async function recoverCancelWithEvmK256(account: EvmK256LifecycleSurface, device: EvmK256Device) {
  const { frame, counter } = await deviceFrame(account, device);
  const typedData = evmK256Messages.cancelRecovery(frame);
  const auth = await device.authorise(typedData, counter);
  const r = await account.callTx.recover_cancel_with_evm_k256(authArg(auth));
  return { typedData, auth, txId: txIdOf(r) };
}

/** The grantee frame of the next call under the grantee's grant. */
async function granteeFrame(account: EvmK256GrantSurface, g: EvmK256Grantee) {
  const rec = await account.grantRecord(g.grantId(account.addressBytes));
  if (!rec) throw new Error('evm_k256: no grant record for this grantee (not issued, or revoked by revoke_all)');
  return { account: account.addressBytes, grantee: g.address, label: g.label, slot: g.slot, issuedAt: rec.issued_at, grantNonce: rec.nonce };
}

const openingFor = (g: EvmK256Grantee, o: Omit<GrantOpening, 'originHash' | 'slot'>): GrantOpening => ({ ...o, originHash: g.originHash, slot: g.slot });

/** withdraw_unshielded_with_grant_evm_k256, signed by the grantee. */
export async function withdrawUnshieldedAsEvmGrantee(
  account: EvmK256GrantSurface, g: EvmK256Grantee, opening: Omit<GrantOpening, 'originHash' | 'slot'>,
  color: Uint8Array, amount: bigint, recipient: Uint8Array, site: SiteAmount,
) {
  const frame = await granteeFrame(account, g);
  const typedData = evmK256Messages.withdrawUnshieldedAsGrantee(frame, color, amount, recipient, site);
  const auth = { ...(await g.authorise(typedData)), op: evmK256AmountHint(amount, site) };
  return { typedData, auth, ...(await account.withdrawUnshieldedWithGrantAuth(color, amount, recipient, openingFor(g, opening), auth)) };
}

async function grantCoin(account: EvmK256GrantSurface, color: Uint8Array): Promise<SpentCoin> {
  const c = await account.heldCoin(color);
  if (!eq(c.color, color)) throw new Error('evm_k256: the held coin is not of the withdrawn colour');
  return { nonce: c.nonce, value: c.value, mtIndex: c.mt_index };
}

/** withdraw_shielded_with_grant_evm_k256, signed by the grantee: the change
 *  entry the grantee sealed to the account's live enc_key is shown with it. */
export async function withdrawShieldedAsEvmGrantee(
  account: EvmK256GrantSurface, g: EvmK256Grantee, opening: Omit<GrantOpening, 'originHash' | 'slot'>,
  recipient: Uint8Array, color: Uint8Array, amount: bigint, changeEntry: Uint8Array, site: SiteAmount, encPk?: Uint8Array,
) {
  const frame = await granteeFrame(account, g);
  const enc = encPk ?? await account.encKey();
  const coin = await grantCoin(account, color);
  const typedData = evmK256Messages.withdrawShieldedAsGrantee(frame, color, amount, recipient, changeEntry, enc, coin, site);
  const auth = { ...(await g.authorise(typedData)), op: evmK256CoinHint(amount, coin.value, coin.mtIndex, site) };
  return { typedData, auth, coin, ...(await account.withdrawShieldedWithGrantAuth(recipient, color, amount, changeEntry, enc, openingFor(g, opening), auth)) };
}

/** withdraw_shielded_to_contract_with_grant_evm_k256: typed data and
 *  authorisation (a direct transfer is composed with the recipient's claim). */
export async function authoriseWithdrawShieldedToContractAsEvmGrantee(
  account: EvmK256GrantSurface, g: EvmK256Grantee, recipientContract: Uint8Array, color: Uint8Array, amount: bigint,
  changeEntry: Uint8Array, site: SiteAmount, encPk?: Uint8Array,
) {
  const frame = await granteeFrame(account, g);
  const enc = encPk ?? await account.encKey();
  const coin = await grantCoin(account, color);
  const typedData = evmK256Messages.withdrawShieldedToContractAsGrantee(frame, color, amount, recipientContract, changeEntry, enc, coin, site);
  return { typedData, coin, encPk: enc, auth: { ...(await g.authorise(typedData)), op: evmK256CoinHint(amount, coin.value, coin.mtIndex, site) } };
}
