// Arm `sol_ed25519`: which formats a Solana wallet can sign, and the adapters
// that ask a wallet for exactly those.
//
// A Solana key signs Passport approvals and blind requests in one of two
// formats (sol-ed25519-message.ts): raw, what `signMessage` signs, or the
// Solana off-chain message v1. Wallets differ, and a wallet asked for a
// format it cannot sign either refuses or shows the user bytes it cannot
// read:
//   - Phantom signs raw only: it refuses an off-chain message, even one the
//     page builds.
//   - Backpack and Solflare sign raw, and the off-chain message v1 through
//     their own wallet-standard feature `solana:signOffchainMessage`, which
//     shows the text with its line breaks. Handed the off-chain bytes through
//     `signMessage`, a wallet shows the binary head as garbled characters, so
//     the off-chain format always goes through the feature.
//   - Ledger and Trezor sign the off-chain message v1 only: their Solana apps
//     refuse raw bytes.
//   - Any other wallet-standard wallet: raw when it offers
//     `solana:signMessage`, off-chain when it advertises the feature with
//     message version 1.
// solWalletFormats gives the formats a wallet can sign, preferred first:
// enrolment signs in the first, a restore tries each. The adapters refuse,
// without asking the wallet, bytes of a format it cannot sign.
//
// A wallet may answer with another key than the one it reports (with two
// extensions installed, one may answer requests made to the other's
// wallet-standard entry). The adapters do not decide who signed: the arm's
// signer check does (signer-sol-ed25519.ts `checkSolSignature`), over the
// exact bytes the wallet was asked to sign. `others` gives it the keys other
// connected wallets report, so that a refusal can name the wallet that
// answered.
//
// Auto-approve: a wallet setting that signs messages without showing them
// (for example a time-limited "auto-approve message signing") signs Passport
// approvals unseen as well. Passport cannot detect it; such a setting must
// stay off for a wallet that holds a Passport device.

import { base58Encode, parseSolanaPublicKey } from './descriptors.js';
import { SOL_HEAD_LENGTH, SOL_OFFCHAIN_VERSION, solFormatOfSigned, solMessageHead, type SolFormat } from './sol-ed25519-message.js';
import type { SolSigner } from './signer-sol-ed25519.js';

/** The wallet-standard feature of raw message signing. */
export const SOL_SIGN_MESSAGE_FEATURE = 'solana:signMessage';
/** The wallet-standard feature of off-chain message signing. */
export const SOL_SIGN_OFFCHAIN_MESSAGE_FEATURE = 'solana:signOffchainMessage';

/** The wallet families whose formats the client knows; `other` is any other
 *  wallet-standard wallet, judged by the features it advertises. */
export type SolWalletFamily = 'phantom' | 'backpack' | 'solflare' | 'ledger' | 'trezor' | 'other';

/** A wallet as the client meets it: its family and, for a wallet-standard
 *  wallet, the features it advertises (`wallet.features`). */
export interface SolWalletProfile {
  family: SolWalletFamily;
  features?: Readonly<Record<string, unknown>>;
}

/** The family of a wallet-standard wallet, by the name it registers. */
export function solWalletFamily(name: unknown): SolWalletFamily {
  const n = typeof name === 'string' ? name.trim().toLowerCase() : '';
  return n === 'phantom' || n === 'backpack' || n === 'solflare' ? n : 'other';
}

/** A wallet-standard account. */
export interface SolStandardAccount { address: string; publicKey: Uint8Array }

/** `solana:signMessage`: signs exactly the bytes given. */
export interface SolSignMessageFeature {
  signMessage(...inputs: { account: SolStandardAccount; message: Uint8Array }[]): Promise<readonly { signedMessage?: unknown; signature: unknown }[]>;
}

/** `solana:signOffchainMessage`: the wallet builds the off-chain message of
 *  the given text, with the required signers, and signs it. */
export interface SolSignOffchainMessageFeature {
  supportedMessageVersions?: readonly number[];
  signOffchainMessage(...inputs: { messageVersion: number; account: SolStandardAccount; message: string; requiredSigners: readonly Uint8Array[] }[]):
    Promise<readonly { signedOffchainMessage?: unknown; signature: unknown }[]>;
}

/** A wallet-standard wallet, as far as the adapter uses it. */
export interface SolStandardWallet { name: string; features: Readonly<Record<string, unknown>> }

const feature = <T>(features: Readonly<Record<string, unknown>> | undefined, name: string, method: string): T | undefined => {
  const f = features?.[name] as any;
  return f && typeof f[method] === 'function' ? (f as T) : undefined;
};

/** The wallet's raw signing feature, if it offers one. */
export function solSignMessageFeature(features?: Readonly<Record<string, unknown>>): SolSignMessageFeature | undefined {
  return feature<SolSignMessageFeature>(features, SOL_SIGN_MESSAGE_FEATURE, 'signMessage');
}

/** The wallet's off-chain signing feature, if it advertises message version
 *  1 (the only version the arm verifies). */
export function solOffchainV1Feature(features?: Readonly<Record<string, unknown>>): SolSignOffchainMessageFeature | undefined {
  const f = feature<SolSignOffchainMessageFeature>(features, SOL_SIGN_OFFCHAIN_MESSAGE_FEATURE, 'signOffchainMessage');
  if (!f) return undefined;
  let versions: unknown[];
  try { versions = [...(f.supportedMessageVersions ?? [])]; } catch { return undefined; }
  return versions.includes(SOL_OFFCHAIN_VERSION) ? f : undefined;
}

/** The formats a wallet can sign, preferred first. Phantom: raw, never
 *  off-chain, whatever it advertises; Ledger and Trezor: off-chain, never
 *  raw; Backpack, Solflare and any other wallet-standard wallet: off-chain
 *  when it advertises the off-chain feature with version 1, raw when it
 *  offers `signMessage`. A wallet that signs neither gets an empty list and
 *  is asked for nothing. */
export function solWalletFormats(p: SolWalletProfile): SolFormat[] {
  switch (p.family) {
    case 'ledger': case 'trezor': return ['offchain'];
    case 'phantom': return solSignMessageFeature(p.features) ? ['raw'] : [];
    case 'backpack': case 'solflare': case 'other': return [
      ...(solOffchainV1Feature(p.features) ? ['offchain' as const] : []),
      ...(solSignMessageFeature(p.features) ? ['raw' as const] : []),
    ];
    default: throw new Error(`sol_ed25519: unknown wallet family ${String((p as any)?.family)}`);
  }
}

/** Bytes a wallet returned: a Uint8Array, or an array of byte values. */
function walletBytes(v: unknown, what: string, length?: number): Uint8Array {
  let b: Uint8Array;
  if (v instanceof Uint8Array) b = new Uint8Array(v);
  else if (Array.isArray(v) && v.every((x) => Number.isInteger(x) && x >= 0 && x <= 255)) b = Uint8Array.from(v);
  else throw new Error(`sol_ed25519: the wallet returned no ${what}`);
  if (length !== undefined && b.length !== length) throw new Error(`sol_ed25519: the wallet's ${what} is ${b.length} bytes, not ${length}`);
  return b;
}
const same = (a: Uint8Array, b: Uint8Array) => a.length === b.length && a.every((v, i) => v === b[i]);

/** Refuses bytes whose format the wallet cannot sign, before asking it. */
function formatOf(bytes: Uint8Array, formats: readonly SolFormat[], who: string): SolFormat {
  const format = solFormatOfSigned(bytes);
  if (!formats.includes(format)) throw new Error(`sol_ed25519: ${who} cannot sign the ${format} format; not asked`);
  return format;
}

/** The text of an off-chain message for `key` (the bytes after the head),
 *  checked: the head names `key`, the text is printable ASCII. */
function offchainText(bytes: Uint8Array, key: Uint8Array): string {
  const head = solMessageHead('offchain', key);
  if (bytes.length <= SOL_HEAD_LENGTH || !same(bytes.subarray(0, SOL_HEAD_LENGTH), head)) throw new Error('sol_ed25519: not an off-chain message for this key');
  const text = new TextDecoder().decode(bytes.subarray(SOL_HEAD_LENGTH));
  if (!/^[\x20-\x7e\n]*$/.test(text)) throw new Error('sol_ed25519: an off-chain message text is printable ASCII');
  return text;
}

/**
 * A signer for a wallet-standard wallet's account (Phantom, Backpack,
 * Solflare, or another wallet). Its formats are solWalletFormats of the
 * wallet's family and features. Raw bytes go to `solana:signMessage`; an
 * off-chain message goes to `solana:signOffchainMessage` as its text, with
 * the account as the one required signer, and the wallet's own envelope,
 * when it returns it, must be exactly the bytes the client built. Whether the
 * signature comes from the account's key is the arm's signer check.
 */
export function solStandardSigner(wallet: SolStandardWallet, account: SolStandardAccount, opts: { others?: () => readonly Uint8Array[] } = {}): SolSigner {
  const publicKey = parseSolanaPublicKey(walletBytes(account?.publicKey, 'account key', 32));
  if (typeof account.address === 'string' && account.address !== base58Encode(publicKey)) throw new Error('sol_ed25519: the account\'s address and key disagree');
  const name = typeof wallet?.name === 'string' ? wallet.name : 'the wallet';
  const formats = solWalletFormats({ family: solWalletFamily(wallet?.name), features: wallet?.features });
  return {
    publicKey,
    formats,
    ...(opts.others ? { others: opts.others } : {}),
    sign: async (message: Uint8Array) => {
      const bytes = new Uint8Array(message);
      if (formatOf(bytes, formats, name) === 'raw') {
        const [answer] = await solSignMessageFeature(wallet.features)!.signMessage({ account, message: bytes });
        if (answer?.signedMessage !== undefined && !same(walletBytes(answer.signedMessage, 'signed message'), bytes)) {
          throw new Error(`sol_ed25519: ${name} reports that it signed other bytes than asked; refused`);
        }
        return walletBytes(answer?.signature, 'signature', 64);
      }
      const text = offchainText(bytes, publicKey);
      const [answer] = await solOffchainV1Feature(wallet.features)!.signOffchainMessage({ messageVersion: SOL_OFFCHAIN_VERSION, account, message: text, requiredSigners: [publicKey] });
      if (answer?.signedOffchainMessage !== undefined && !same(walletBytes(answer.signedOffchainMessage, 'off-chain message'), bytes)) {
        throw new Error(`sol_ed25519: ${name} signed another off-chain message than the one asked; refused`);
      }
      return walletBytes(answer?.signature, 'signature', 64);
    },
  };
}

/** A hardware wallet's off-chain signing: `envelope` is the whole off-chain
 *  message v1 (what a Ledger's Solana app takes), `text` its text (what a
 *  Trezor takes, building the envelope itself). It returns the signature,
 *  and the signed bytes when the device reports them. */
export type SolHardwareSignFn = (envelope: Uint8Array, text: Uint8Array) =>
  Promise<Uint8Array | { signature: Uint8Array; signed?: Uint8Array }> | Uint8Array | { signature: Uint8Array; signed?: Uint8Array };

/**
 * A signer for a Ledger or a Trezor account (its 32-byte key and its
 * transport's off-chain signing). Off-chain only: raw bytes are refused
 * without asking the device. The signed bytes a device reports must be
 * exactly the envelope the client built.
 */
export function solHardwareSigner(opts: { family: 'ledger' | 'trezor'; publicKey: Uint8Array; signOffchain: SolHardwareSignFn; others?: () => readonly Uint8Array[] }): SolSigner {
  if (opts.family !== 'ledger' && opts.family !== 'trezor') throw new Error(`sol_ed25519: not a hardware wallet family: ${String(opts.family)}`);
  const publicKey = parseSolanaPublicKey(opts.publicKey);
  const formats = solWalletFormats({ family: opts.family });
  return {
    publicKey,
    formats,
    ...(opts.others ? { others: opts.others } : {}),
    sign: async (message: Uint8Array) => {
      const bytes = new Uint8Array(message);
      formatOf(bytes, formats, `the ${opts.family === 'ledger' ? 'Ledger' : 'Trezor'}`);
      offchainText(bytes, publicKey);
      const r = await opts.signOffchain(new Uint8Array(bytes), bytes.slice(SOL_HEAD_LENGTH));
      const answer = r instanceof Uint8Array || Array.isArray(r) ? { signature: r as Uint8Array } : r;
      if (answer?.signed !== undefined && !same(walletBytes(answer.signed, 'signed message'), bytes)) {
        throw new Error('sol_ed25519: the device signed another off-chain message than the one asked; refused');
      }
      return walletBytes(answer?.signature, 'signature', 64);
    },
  };
}
