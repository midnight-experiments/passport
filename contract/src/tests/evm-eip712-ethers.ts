// The independent check of the `evm_eip712` arm against ethers (spec FR-E03,
// FR-018). ethers is NOT a dependency of this package (Q24): this script loads
// it at run time, from `ETHERS_MODULE` (a path to ethers' ESM entry) or a
// resolvable `ethers`, for example after `npm i --no-save ethers@6.17.0`.
// Without ethers it ends in ERROR, never in PASS.
//
//   keys       ethers' address of a secret key == the contract's
//              evm_eip712_address == the client's; EIP-55 forms agree
//   blind      ethers' hashMessage == the client's EIP-191 digest; ethers'
//              signMessage == the software wallet's personal_sign, byte for
//              byte (both RFC 6979); ethers recovers the address and the
//              public point; ethers' sha256 of the blind preimage == the
//              blind (enrolment and the contract's derive_blind)
//
// Writes $EVIDENCE_DIR/evm-eip712-ethers.json when EVIDENCE_DIR is set.

import { strict as assert } from 'node:assert';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { pathToFileURL } from 'node:url';
import { pureCircuits } from '../wallet/contract.js';
import { evmChecksumAddress, padTag } from '../wallet/descriptors.js';
import { blindMessageBytes } from '../wallet/blind.js';
import {
  SoftwareEvmWallet, enrolEvmBlind, personalMessageDigest, SECP256K1_ORDER,
} from '../wallet/signer-evm-eip712.js';

let ethers: any;
try {
  const spec = process.env.ETHERS_MODULE;
  ethers = await import(spec ? pathToFileURL(spec).href : 'ethers');
} catch (e: any) {
  console.error(`◆ evm-eip712-ethers: ERROR — ethers is not available (${e?.message ?? e}); set ETHERS_MODULE or install ethers@6 without saving`);
  process.exit(2);
}

const SEED = 'aa00067/e/s2/evm-eip712-ethers/v1';
let ctr = 0;
const rnd = (n: number): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) out.set(createHash('sha256').update(SEED).update(String(ctr++)).digest().subarray(0, Math.min(32, n - i)), i);
  return out;
};
const hex = (b: Uint8Array) => Buffer.from(b).toString('hex');
const beInt = (b: Uint8Array) => { let v = 0n; for (const x of b) v = (v << 8n) | BigInt(x); return v; };
const scalar = () => { for (;;) { const k = beInt(rnd(32)); if (k > 0n && k < SECP256K1_ORDER) return k; } };
const sk32 = (k: bigint) => '0x' + k.toString(16).padStart(64, '0');
const pc = pureCircuits as any;

const checks: Record<string, number> = {};
const ok = (k: string, n = 1) => { checks[k] = (checks[k] ?? 0) + n; };
const vectors: unknown[] = [];

// ── Keys ─────────────────────────────────────────────────────────────────────
for (const k of [1n, 2n, SECP256K1_ORDER - 1n, ...Array.from({ length: 13 }, scalar)]) {
  const w = new ethers.Wallet(sk32(k));
  const ours = new SoftwareEvmWallet(k);
  const contractAddr = pc.evm_eip712_address(pc.compute_public_point_with_evm_eip712(k));
  assert.equal(evmChecksumAddress(contractAddr), w.address, 'contract address == ethers');
  assert.equal(evmChecksumAddress(ours.addressBytes), w.address, 'client address == ethers');
  assert.equal(ethers.getAddress(w.address.toLowerCase()), evmChecksumAddress(ours.addressBytes), 'EIP-55 == ethers');
  const uncompressed = ethers.SigningKey.computePublicKey(sk32(k), false);
  assert.equal(uncompressed, '0x04' + ours.pk.x.toString(16).padStart(64, '0') + ours.pk.y.toString(16).padStart(64, '0'), 'point == ethers');
  ok('keys', 4);
}
console.log(`  ✓ keys: addresses, EIP-55 forms and points == ethers (${checks.keys} checks)`);

// ── Blind (personal_sign) ────────────────────────────────────────────────────
const blindTag = padTag('midnight:account:blind:evm:v2');
for (const [k, network, index] of [[1n, 'undeployed', 0], [1n, 'undeployed', 1], [1n, 'preview', 0], [scalar(), 'mainnet', 7], [scalar(), 'preprod', 4294967295]] as [bigint, string, number][]) {
  const w = new ethers.Wallet(sk32(k));
  const ours = new SoftwareEvmWallet(k);
  const msg = blindMessageBytes({ scheme: 'evm_eip712', network, identity: ours.addressBytes, accountIndex: index });
  assert.equal(ethers.hashMessage(msg), '0x' + hex(personalMessageDigest(msg)), 'EIP-191 digest == ethers.hashMessage');
  const theirs = await w.signMessage(msg);
  const mine = await ours.personalSign(msg);
  assert.equal(theirs, '0x' + hex(mine), 'personal_sign == ethers.signMessage, byte for byte');
  assert.equal(ethers.verifyMessage(msg, theirs), w.address, 'ethers recovers the address');
  const e = await enrolEvmBlind(ours, network, index);
  const recovered = ethers.SigningKey.recoverPublicKey(ethers.hashMessage(msg), theirs);
  assert.equal(recovered, '0x04' + e.pk.x.toString(16).padStart(64, '0') + e.pk.y.toString(16).padStart(64, '0'), 'recovered point == ethers');
  const sig = ethers.Signature.from(theirs);
  const canonical = ethers.getBytes(ethers.concat([sig.r, sig.s]));
  assert.equal(hex(canonical), hex(e.canonical), 'canonical low-S r || s == ethers (ethers signs low-S)');
  const blind = ethers.sha256(ethers.concat([blindTag, canonical]));
  assert.equal(blind, '0x' + hex(e.blind), 'blind == ethers.sha256 of the preimage');
  assert.equal(blind, '0x' + hex(pc.derive_blind(blindTag, canonical)), 'blind == the contract');
  vectors.push({ scalar: k === 1n ? '1' : 'seeded', address: w.address, network, accountIndex: String(index), eip191Digest: ethers.hashMessage(msg), signature: theirs, blind });
  ok('blind', 7);
}
console.log(`  ✓ blind: EIP-191 digest, personal_sign bytes, recovery, canonical form and blind == ethers (${checks.blind} checks)`);

const report = { suite: 'evm-eip712-ethers', step: 'S2E', ethersVersion: ethers.version, seed: SEED, ranAt: new Date().toISOString(), checks, vectors, verdict: 'PASS' };
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'evm-eip712-ethers.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log(`\n◆ evm-eip712-ethers: PASS (ethers ${ethers.version})`);
