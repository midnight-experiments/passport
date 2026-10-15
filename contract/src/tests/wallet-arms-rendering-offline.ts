// Offline suite for the readable rendering helpers (contracts/modules/
// WalletArmRendering.compact), compiled through the base probe contract.
// Every helper is compared with an independent renderer written here, and
// every check the helpers make is exercised with inputs that must be refused.
//
//   decimal  uint{8,32,64,128}_text: each value accepts exactly its canonical
//            text (left-aligned, space-padded, no leading zero); edge values
//            of every width, including 2^128 - 1 (39 digits); refusals for
//            leading zeros, empty, right-aligned, inner spaces, zero-byte
//            padding, signs, letters, and wrong digits.
//   hex      hex_text_{20,32,64,192}: every byte value, lowercase, in full;
//            reverse_32.
//   labels   label_text_32: canonical zero-padded words accepted and shown
//            with spaces; leading, trailing, and double spaces, empty labels,
//            inner zero bytes, and control and non-ASCII bytes refused; distinct
//            labels never show the same text. visible_text_21: visible ASCII
//            only.
//
// Writes $EVIDENCE_DIR/wallet-arms-rendering-offline.json when EVIDENCE_DIR
// is set; never writes into the repository.

import { strict as assert } from 'node:assert';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { pureCircuits as probe } from '../../contracts/managed/probe-wallet-arms-base/contract/index.js';

const SEED = 'aa00067/s1/wallet-arms-rendering-offline/v1';
let ctr = 0;
const rnd = (n: number): Uint8Array => {
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i += 32) {
    const h = createHash('sha256').update(SEED).update(String(ctr++)).digest();
    out.set(h.subarray(0, Math.min(32, n - i)), i);
  }
  return out;
};
// Vector<n, Uint<8>> crosses the generated JavaScript as an array of bigint.
const vec = (b: Uint8Array): bigint[] => [...b].map(BigInt);
const ascii = (v: Uint8Array | bigint[]): string => Buffer.from(Uint8Array.from(v as ArrayLike<number>, Number)).toString('latin1');
const bytes = (s: string): Uint8Array => new Uint8Array(Buffer.from(s, 'latin1'));
const randBig = (bits: number): bigint => {
  const b = rnd(Math.ceil(bits / 8));
  let v = 0n;
  for (const x of b) v = (v << 8n) | BigInt(x);
  return v & ((1n << BigInt(bits)) - 1n);
};

// ── Independent renderers ───────────────────────────────────────────────────

const decimal = (v: bigint, width: number): Uint8Array => {
  const s = v.toString(10);
  if (s.length > width) throw new Error('value too wide');
  return bytes(s.padEnd(width, ' '));
};
const hexOf = (b: Uint8Array): string => Buffer.from(b).toString('hex');
const labelShown = (b: Uint8Array): string => ascii(b.map((c) => (c === 0 ? 32 : c)));
const zeroPadded = (s: string, w: number): Uint8Array => { const o = new Uint8Array(w); o.set(bytes(s)); return o; };

const report: Record<string, unknown> = { suite: 'wallet-arms-rendering-offline', seed: SEED, ranAt: new Date().toISOString() };
const counts: Record<string, { accepted: number; refused: number }> = {};
const count = (k: string, field: 'accepted' | 'refused') => { (counts[k] ??= { accepted: 0, refused: 0 })[field]++; };

// ── Decimal ─────────────────────────────────────────────────────────────────

console.log('\n── decimal (digit binding)');
const WIDTHS: [string, number, number, (v: bigint, t: bigint[]) => bigint[]][] = [
  ['uint8_text', 8, 3, probe.uint8_text],
  ['uint32_text', 32, 10, probe.uint32_text],
  ['uint64_text', 64, 20, probe.uint64_text],
  ['uint128_text', 128, 39, probe.uint128_text],
];
for (const [name, bits, width, f] of WIDTHS) {
  const max = (1n << BigInt(bits)) - 1n;
  assert.equal(max.toString().length, width, `${name}: the width is the type's widest value`);
  const values = new Set<bigint>([0n, 1n, 9n, 10n, 11n, 99n, 100n, max, max - 1n]);
  for (let k = 1; 10n ** BigInt(k) <= max; k++) { values.add(10n ** BigInt(k) - 1n); values.add(10n ** BigInt(k)); }
  for (let i = 0; i < 24; i++) values.add(randBig(bits));
  for (const v of values) {
    const t = decimal(v, width);
    const out = f(v, vec(t));
    assert.equal(ascii(out), ascii(t), `${name}(${v})`);
    count(name, 'accepted');
  }
  // Refusals: each text below is wrong for the value next to it.
  const refuse = (v: bigint, text: string, why: RegExp, label: string) => {
    assert.equal(text.length, width, `${name}: test text width (${label})`);
    assert.throws(() => f(v, vec(bytes(text))), why, `${name}: ${label}`);
    count(name, 'refused');
  };
  const sp = (s: string) => s.padEnd(width, ' ');
  refuse(7n, sp('07'), /leading zero/, 'leading zero');
  refuse(0n, sp('00'), /leading zero/, 'zero with a leading zero');
  refuse(0n, sp(''), /empty decimal/, 'empty');
  refuse(7n, (' 7').padEnd(width, ' '), /empty decimal|left-aligned/, 'right-shifted');
  refuse(12n, sp('1 2'), /left-aligned/, 'inner space');
  refuse(1n, '1' + '\0'.repeat(width - 1), /left-aligned/, 'zero-byte padding');
  refuse(1n, sp('+1'), /left-aligned/, 'sign');
  refuse(10n, sp('1a'), /left-aligned/, 'letter');
  refuse(5n, sp('6'), /do not match/, 'wrong digit');
  refuse(5n, sp('5').replace(/ $/, '0'), /left-aligned/, 'digit after the padding');
  if (bits < 128) {
    // A text of the next power of ten (the type cannot hold it) never matches.
    refuse(0n, sp((max + 1n).toString().slice(0, width)), /do not match|leading zero/, 'out-of-range digits');
  }
  console.log(`  ✓ ${name}: ${counts[name].accepted} values accepted with their canonical text, ${counts[name].refused} wrong texts refused`);
}

// ── Hex ─────────────────────────────────────────────────────────────────────

console.log('\n── hex');
const allBytes = Uint8Array.from({ length: 256 }, (_, i) => i);
for (const [name, n, f] of [
  ['hex_text_20', 20, probe.hex_text_20],
  ['hex_text_32', 32, probe.hex_text_32],
  ['hex_text_64', 64, probe.hex_text_64],
  ['hex_text_192', 192, probe.hex_text_192],
] as [string, number, (b: Uint8Array) => bigint[]][]) {
  let checked = 0;
  for (let off = 0; off < 256; off += n) {
    const b = new Uint8Array(n);
    for (let j = 0; j < n; j++) b[j] = allBytes[(off + j) % 256];
    assert.equal(ascii(f(b)), hexOf(b), `${name} @${off}`);
    checked++;
  }
  for (let i = 0; i < 8; i++) { const b = rnd(n); assert.equal(ascii(f(b)), hexOf(b), `${name} random`); checked++; }
  counts[name] = { accepted: checked, refused: 0 };
  console.log(`  ✓ ${name}: every byte value, lowercase, ${2 * n} digits (${checked} vectors)`);
}
for (let i = 0; i < 8; i++) {
  const b = rnd(32);
  assert.equal(hexOf(probe.reverse_32(b)), hexOf(Uint8Array.from(b).reverse()));
}
console.log('  ✓ reverse_32: byte order reversed');

// ── Labels ──────────────────────────────────────────────────────────────────

console.log('\n── labels');
const GOOD = [
  'midnight:account:device:v1', 'midnight:account:grant:id:evm:v2', 'Midnight Night Market',
  'wallet.example', 'a', 'A b C d', 'x'.repeat(32), '~!#$%&()*+,-./:;<=>?@[]^_`{|}', 'MN Bank - grants v1',
];
const shown = new Map<string, string>();
for (const s of GOOD) {
  const b = zeroPadded(s, 32);
  const out = probe.label_text_32(b);
  assert.equal(ascii(out), labelShown(b), `label_text_32(${JSON.stringify(s)})`);
  assert.equal(ascii(out).trimEnd(), s);
  shown.set(ascii(out), s);
  count('label_text_32', 'accepted');
}
for (let i = 0; i < 64; i++) {
  // Random canonical labels: words of visible characters, single spaces.
  const r = rnd(32);
  const len = 1 + (r[0] % 32);
  let s = '';
  for (let j = 0; j < len; j++) {
    const c = 0x21 + (r[j] % 94);
    s += j > 0 && j < len - 1 && r[j] % 7 === 0 && s[s.length - 1] !== ' ' ? ' ' : String.fromCharCode(c);
  }
  const b = zeroPadded(s, 32);
  const out = ascii(probe.label_text_32(b));
  assert.equal(out, labelShown(b));
  if (shown.has(out)) assert.equal(shown.get(out), s, `two labels show the same text: ${JSON.stringify(out)}`);
  shown.set(out, s);
  count('label_text_32', 'accepted');
}
const BAD: [string, Uint8Array][] = [
  ['empty', new Uint8Array(32)],
  ['leading space', zeroPadded(' a', 32)],
  ['trailing space before the padding', zeroPadded('a ', 32)],
  ['trailing space at full width', bytes('a'.repeat(31) + ' ')],
  ['double space', zeroPadded('a  b', 32)],
  ['zero byte inside the text', zeroPadded('a\0b', 32)],
  ['space-padded instead of zero-padded', bytes('abc'.padEnd(32, ' '))],
  ['newline', zeroPadded('a\nb', 32)],
  ['tab', zeroPadded('a\tb', 32)],
  ['DEL', zeroPadded('a\x7fb', 32)],
  ['non-ASCII byte', zeroPadded('caf\xe9', 32)],
  ['carriage return at the end', zeroPadded('a\r', 32)],
];
for (const [why, b] of BAD) {
  assert.throws(() => probe.label_text_32(b), /not a zero-padded label/, `label_text_32 must refuse: ${why}`);
  count('label_text_32', 'refused');
}
console.log(`  ✓ label_text_32: ${counts.label_text_32.accepted} canonical labels shown one-to-one, ${counts.label_text_32.refused} malformed labels refused`);

for (const o of ['https://a.example.com', 'http://localhost:5173', 'https://x.y.bank.test']) {
  assert.equal(ascii(probe.visible_text_21(bytes(o))), o);
  count('visible_text_21', 'accepted');
}
for (const [why, o] of [
  ['space', 'https://a example.com'], ['zero byte', 'https://a.example.co\0'],
  ['DEL', 'https://a.example.co\x7f'], ['non-ASCII', 'https://a.example.co\xe9'], ['newline', 'https://a.example.co\n'],
] as [string, string][]) {
  assert.throws(() => probe.visible_text_21(bytes(o)), /not visible ASCII/, `visible_text_21 must refuse: ${why}`);
  count('visible_text_21', 'refused');
}
console.log(`  ✓ visible_text_21: ${counts.visible_text_21.accepted} origins shown byte for byte, ${counts.visible_text_21.refused} refused`);

report.counts = counts;
report.verdict = 'PASS';
if (process.env.EVIDENCE_DIR) {
  const file = path.join(process.env.EVIDENCE_DIR, 'wallet-arms-rendering-offline.json');
  fs.mkdirSync(process.env.EVIDENCE_DIR, { recursive: true });
  fs.writeFileSync(file, JSON.stringify(report, null, 2) + '\n');
  console.log(`\n■ evidence → ${file}`);
}
console.log('\n◆ wallet-arms-rendering-offline: PASS');
