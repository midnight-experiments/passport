// The `evm_eip712` arm's client facade (spec FR-017, Q19): an Ethereum
// account (MetaMask, or any EIP-712 wallet) as a Passport device or grantee.
//
// The device is its 20-byte Ethereum address, BLINDED (FR-013, Q13, Q16):
// every entry, boot commitment and grant id binds the address together with a
// per-account secret, the blind, which the client derives from the wallet's
// own deterministic signature over a readable request message:
//
//   1. The client builds the request for (network, wallet address, account
//      index) with blind.ts `blindMessage` (the wallet shows it as text).
//   2. The wallet signs it TWICE with `personal_sign` (EIP-191, Q25). Both
//      signatures must have the same canonical form (low-S r || s): RFC 6979
//      makes an honest wallet deterministic, and a hedged or MPC wallet,
//      whose blind could never be re-derived, is refused here.
//   3. blind = SHA-256(pad32("midnight:account:blind:evm:v2") || r || s).
//   4. The device's public point is RECOVERED from that same signature (a
//      wallet never exposes it), and its address must be the wallet's own.
//
// The roster record (`EvmEip712RosterRecord`) persists the address, point,
// blind, network and account index per device. A restored client re-derives
// blind_0, blind_1, ... from the wallet and finds its accounts by testing
// entries (`entryAt`) against each account's device set.
//
// Every derivation goes through the contract's own exported pure circuits
// (`derive_*_with_evm_eip712`), so the client and the circuit can never
// disagree. Signing the readable EIP-712 approvals is added with the arm's
// codec (signing bytes frozen at S4E).

import { secp256k1 } from '@noble/curves/secp256k1.js';
import { keccak_256 } from '@noble/hashes/sha3.js';

import { pureCircuits, type Secp256k1Point } from './contract.js';
import {
  blindMessageBytes,
  canonicalEvmSignature,
  deriveBlind,
  sameCanonicalSignature,
} from './blind.js';
import { evmAddressOf, evmChecksumAddress, parseEvmAddress } from './descriptors.js';
import { typedDataDigest, evmEip712Messages, type Eip712TypedData } from './evm-eip712-codec.js';

// ── Signatures ───────────────────────────────────────────────────────────────

export const SECP256K1_ORDER = secp256k1.Point.Fn.ORDER;

/** An ECDSA signature as the circuit ABI carries it (`Secp256k1EcdsaSignature`). */
export interface EvmEcdsaSignature { r: bigint; s: bigint }

/** A 65-byte wallet signature `r || s || v`, parsed. Both S forms are kept as
 *  given: the contract accepts both (spec FR-011); the rolling entry makes a
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
  if (!/^([0-9a-f]{2})*$/i.test(h)) throw new Error('evm_eip712: not a hex string');
  return new Uint8Array((h.match(/../g) ?? []).map((x) => parseInt(x, 16)));
};
const eq = (a: Uint8Array, b: Uint8Array): boolean => a.length === b.length && a.every((v, i) => v === b[i]);

/** Parses the wallet form `r || s || v` (65 bytes; v in {0, 1, 27, 28}).
 *  Refuses r or s outside [1, n). */
export function parseEvmSignature(sig: Uint8Array): ParsedEvmSignature {
  if (sig.length !== 65) throw new Error(`evm_eip712: a wallet signature is 65 bytes (r || s || v), got ${sig.length}`);
  const r = beInt(sig.subarray(0, 32));
  const s = beInt(sig.subarray(32, 64));
  if (r === 0n || r >= SECP256K1_ORDER) throw new Error('evm_eip712: signature r outside [1, n)');
  if (s === 0n || s >= SECP256K1_ORDER) throw new Error('evm_eip712: signature s outside [1, n)');
  const v = sig[64];
  if (![0, 1, 27, 28].includes(v)) throw new Error(`evm_eip712: signature v must be 0, 1, 27 or 28, got ${v}`);
  return { r, s, v, recovery: (v >= 27 ? v - 27 : v) as 0 | 1 };
}

/** The wallet form of a parsed signature. */
export function serialiseEvmSignature(sig: ParsedEvmSignature): Uint8Array {
  return new Uint8Array([...be32(sig.r), ...be32(sig.s), sig.v]);
}

/** The malleated twin (r, n - s): the same digest and key, the other S and
 *  recovery parity. The contract accepts it (FR-011); used by the tests. */
export function highSTwin(sig: ParsedEvmSignature): ParsedEvmSignature {
  const recovery = (sig.recovery ^ 1) as 0 | 1;
  return { r: sig.r, s: SECP256K1_ORDER - sig.s, recovery, v: sig.v >= 27 ? 27 + recovery : recovery };
}

/** The point that produced `sig` over `digest` (the wallet never exposes it). */
export function recoverEvmPoint(digest: Uint8Array, sig: ParsedEvmSignature): Secp256k1Point {
  if (digest.length !== 32) throw new Error('evm_eip712: a digest is 32 bytes');
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
 *  the circuit's `secp256k1EthereumAddress` computes. */
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
    if (sk <= 0n || sk >= SECP256K1_ORDER) throw new Error('evm_eip712: a secret key is in [1, n)');
    this.pk = pureCircuits.compute_public_point_with_evm_eip712(sk);
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

/** The roster record a client persists per device (FR-013). Test keys never
 *  appear here: a device is its wallet. */
export interface EvmEip712RosterRecord {
  scheme: 'evm_eip712';
  network: string;
  accountIndex: string;
  /** EIP-55 checksummed address. */
  address: string;
  /** The recovered public point, big-endian hex coordinates. */
  pk: { x: string; y: string };
  /** The blind, hex. A secret: it links this wallet to the account. */
  blind: string;
}

/** The authorising material an `evm_eip712` device-gated circuit consumes
 *  (the trailing `EvmEip712Auth` struct argument). The circuit derives the
 *  address from `pk`; `blind` and `use_counter` are ledger-pinned openings of
 *  the device's entry. */
export interface EvmEip712Authorisation {
  arm: 'evm_eip712';
  pk: Secp256k1Point;
  use_counter: bigint;
  blind: Uint8Array;
  sig: EvmEcdsaSignature;
}

/** The authorising material an `evm_eip712` grantee twin consumes. The
 *  grantee's origin label (32-byte zero-padded ASCII) travels with it; the
 *  circuit derives `origin_hash` from it. Provisional until S8E freezes the
 *  grantee ABI. */
export interface EvmEip712GrantAuthorisation {
  arm: 'evm_eip712';
  pk: Secp256k1Point;
  blind: Uint8Array;
  label: Uint8Array;
  sig: EvmEcdsaSignature;
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
  const message = blindMessageBytes({ scheme: 'evm_eip712', network, identity: address, accountIndex });
  const first = await wallet.personalSign(message);
  const second = await wallet.personalSign(message);
  if (!sameCanonicalSignature('evm_eip712', first, second)) {
    throw new Error('blind: the wallet signed the privacy-key request twice with different signatures (not deterministic); this wallet cannot be a Passport device');
  }
  const canonical = canonicalEvmSignature(first);
  const pk = recoverEvmPoint(personalMessageDigest(message), parseEvmSignature(first));
  if (!eq(evmAddressOfPoint(pk), address)) {
    throw new Error('blind: the privacy-key signature does not recover to the wallet address');
  }
  return { message, signatures: [first, second], canonical, blind: deriveBlind('evm_eip712', canonical), pk, address };
}

/**
 * An `evm_eip712` device of one account: its wallet (when present), its
 * recovered point, its address and the account's blind.
 */
export class EvmEip712Device {
  readonly arm = 'evm_eip712' as const;
  readonly address: Uint8Array;

  constructor(
    readonly pk: Secp256k1Point,
    readonly blind: Uint8Array,
    readonly network: string,
    readonly accountIndex: bigint,
    readonly wallet?: EvmWallet,
  ) {
    if (blind.length !== 32) throw new Error('evm_eip712: a blind is 32 bytes');
    if (pk.x === 0n && pk.y === 0n) throw new Error('evm_eip712: the point at infinity is not a device key');
    secp256k1.Point.fromAffine({ x: pk.x, y: pk.y }).assertValidity();
    this.address = evmAddressOfPoint(pk);
  }

  /** Enrols `wallet` for the account at `accountIndex` on `network`. */
  static async enrol(wallet: EvmWallet, network: string, accountIndex: bigint | number): Promise<EvmEip712Device> {
    const e = await enrolEvmBlind(wallet, network, accountIndex);
    return new EvmEip712Device(e.pk, e.blind, network, BigInt(accountIndex), wallet);
  }

  /** The EIP-55 form a wallet shows. */
  get checksumAddress(): string { return evmChecksumAddress(this.address); }

  /** The device's rolling entry at an account, epoch and use counter. */
  entryAt(contractAddress: Uint8Array, epoch: bigint, counter: bigint): Uint8Array {
    return pureCircuits.derive_device_entry_with_evm_eip712({ bytes: contractAddress }, this.address, this.blind, epoch, counter);
  }

  /** The boot commitment for an account deployed with `salt`. */
  bootCommitment(salt: Uint8Array): Uint8Array {
    return pureCircuits.derive_boot_commitment_with_evm_eip712(salt, this.address, this.blind);
  }

  /** The grant id of this key as a grantee of `contractAddress`. */
  grantId(contractAddress: Uint8Array, originHash: Uint8Array, slot: bigint): Uint8Array {
    return pureCircuits.derive_grant_id_with_evm_eip712({ bytes: contractAddress }, this.address, this.blind, originHash, slot);
  }

  /**
   * Signs `typedData` with the device's wallet (`eth_signTypedData_v4`) and
   * returns the circuit's authorising material. Refuses a signature that does
   * not recover to this device's point (a wallet that signed with another
   * account). The signature is passed on as the wallet produced it; the
   * contract accepts both S forms.
   */
  async authorise(typedData: Eip712TypedData, useCounter: bigint): Promise<EvmEip712Authorisation> {
    if (!this.wallet) throw new Error('evm_eip712: this device has no wallet');
    return this.authorisationFrom(typedData, await this.wallet.signTypedData(typedData), useCounter);
  }

  /** The authorising material of an existing wallet signature over `typedData`. */
  authorisationFrom(typedData: Eip712TypedData, signature: Uint8Array, useCounter: bigint): EvmEip712Authorisation {
    const sig = parseEvmSignature(signature);
    const pk = recoverEvmPoint(typedDataDigest(typedData), sig);
    if (pk.x !== this.pk.x || pk.y !== this.pk.y) throw new Error('evm_eip712: the signature does not recover to this device');
    return { arm: 'evm_eip712', pk: this.pk, use_counter: useCounter, blind: this.blind, sig: { r: sig.r, s: sig.s } };
  }

  /** The arguments of `activate_initial_device_with_evm_eip712`. */
  activationArgs(salt: Uint8Array): [Secp256k1Point, Uint8Array, Uint8Array] {
    return [this.pk, salt, this.blind];
  }

  /** The roster record to persist. */
  toRecord(): EvmEip712RosterRecord {
    return {
      scheme: 'evm_eip712', network: this.network, accountIndex: this.accountIndex.toString(),
      address: this.checksumAddress,
      pk: { x: this.pk.x.toString(16).padStart(64, '0'), y: this.pk.y.toString(16).padStart(64, '0') },
      blind: hex(this.blind),
    };
  }

  /** A device from its roster record; refuses a record whose address is not
   *  its point's. */
  static fromRecord(rec: EvmEip712RosterRecord, wallet?: EvmWallet): EvmEip712Device {
    if (rec.scheme !== 'evm_eip712') throw new Error('evm_eip712: not an evm_eip712 roster record');
    const pk = { x: BigInt('0x' + rec.pk.x), y: BigInt('0x' + rec.pk.y), identity: false } as Secp256k1Point;
    const d = new EvmEip712Device(pk, unhex(rec.blind), rec.network, BigInt(rec.accountIndex), wallet);
    if (!eq(d.address, parseEvmAddress(rec.address))) throw new Error('evm_eip712: the roster address is not the point\'s address');
    return d;
  }
}

/**
 * Restore (FR-013): the account indexes 0..maxIndex of `wallet` on `network`,
 * each with its blind re-derived from the wallet, tested against candidate
 * accounts' device sets at counters 0..maxCounter. Returns every match.
 */
export async function restoreEvmDevices(
  wallet: EvmWallet,
  network: string,
  accounts: { address: Uint8Array; epoch: bigint; isMember: (entry: Uint8Array) => boolean }[],
  opts: { maxIndex?: number; maxCounter?: bigint } = {},
): Promise<{ accountIndex: bigint; account: Uint8Array; counter: bigint; device: EvmEip712Device }[]> {
  const found: { accountIndex: bigint; account: Uint8Array; counter: bigint; device: EvmEip712Device }[] = [];
  const maxIndex = opts.maxIndex ?? 4;
  const maxCounter = opts.maxCounter ?? 256n;
  for (let i = 0; i <= maxIndex; i++) {
    const device = await EvmEip712Device.enrol(wallet, network, i);
    for (const a of accounts) {
      for (let k = 0n; k <= maxCounter; k++) {
        if (a.isMember(device.entryAt(a.address, a.epoch, k))) {
          found.push({ accountIndex: BigInt(i), account: a.address, counter: k, device });
          break;
        }
      }
    }
  }
  return found;
}

// ── Calls (the arm-owned facade, Q19) ────────────────────────────────────────
//
// The account client (account.ts) routes authorised calls by the
// Authorisation's arm through the registered authArgs branch, so the
// `*WithAuth` methods of a CustodyAccount reach this arm's circuits unchanged.
// What it cannot do for this arm is build the readable message and find the
// device's use counter; these helpers do.

/** The surface of a CustodyAccount these helpers use. */
export interface EvmEip712AccountSurface {
  addressBytes: Uint8Array;
  ledgerState(): Promise<{ auth_nonce: bigint; device_epoch: bigint; devices: { member(e: Uint8Array): boolean } }>;
  rotateEncKeyWithAuth(newKey: Uint8Array, a: EvmEip712Authorisation): Promise<{ txId: string }>;
}

/** The device's current use counter: the first counter whose entry is live at
 *  the current epoch (MIP-0013 S11 rescan). */
export async function resolveEvmEip712Counter(account: EvmEip712AccountSurface, device: EvmEip712Device, limit = 4096n): Promise<bigint> {
  const l = await account.ledgerState();
  for (let k = 0n; k < limit; k++) {
    if (l.devices.member(device.entryAt(account.addressBytes, l.device_epoch, k))) return k;
  }
  throw new Error('evm_eip712: no live entry for this device (rescan limit reached)');
}

/** rotate_enc_key_with_evm_eip712: the RotateEncKey message, signed by the
 *  device's wallet, then the call. */
export async function rotateEncKeyWithEvmEip712(account: EvmEip712AccountSurface, device: EvmEip712Device, newKey: Uint8Array) {
  const l = await account.ledgerState();
  const counter = await resolveEvmEip712Counter(account, device);
  const typedData = evmEip712Messages.rotateEncKey({ account: account.addressBytes, device: device.address, authNonce: l.auth_nonce }, newKey);
  const auth = await device.authorise(typedData, counter);
  return { typedData, auth, ...(await account.rotateEncKeyWithAuth(newKey, auth)) };
}
