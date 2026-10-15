# The `evm_eip712` authorisation arm

**Byte contract AUTH-EIP712-PASSPORT-EVM-V2: draft.** Signing bytes frozen 2026/10/15. The seam is in place (section 9); the measurement report (section 11) grows as the arm's circuits land.

An ordinary Ethereum account, for example MetaMask, acts as a Passport device or as a grantee. It authorises every operation by signing EIP-712 typed data. In that typed data, every operand and every consumed witness value is a member, shown by the wallet in full and recomputed by the circuit from exactly the values it executes. Nothing opaque is signed: there is no challenge hash and no fingerprint. Four labelled values are the only exception (section 6). The wallet needs no ETH and sends no Ethereum transaction.

| | |
|---|---|
| Circuits | `contracts/account-evm-eip712.compact` (the arm), `contracts/modules/EvmEip712.compact` (the codec) |
| Client | `src/wallet/signer-evm-eip712.ts` (wallet, device, blind, roster), `src/wallet/evm-eip712-codec.ts` (typed data) |
| Frozen vectors | `src/tests/vectors/evm-eip712-v2.json`: 53 positive and 14 negative vectors, hashes computed by ethers 6.17.0 |
| Tests | `src/tests/evm-eip712-offline.ts` (`npm run test:evm_eip712-offline`), `src/tests/evm-eip712-ethers.ts` (needs ethers, see section 8), `src/tests/evm-eip712-prover.ts` (constraint-level negatives) |

## 1. Identity

The device is its 20-byte Ethereum address, `secp256k1EthereumAddress(pk) = keccak256(x_be ‖ y_be)[12..32]`, **blinded** (spec FR-013). Every recipe below is SHA-256 (`persistentHash`) over the plain concatenation. `A` is the account's 32-byte contract address, and `le4`/`le8` are little-endian `Uint<32>`/`Uint<64>`:

```
entry    = H(pad32("midnight:account:device:evm:v2")   ‖ A    ‖ address(20) ‖ blind(32) ‖ le4(epoch) ‖ le8(counter))
boot     = H(pad32("midnight:account:boot:evm:v2")     ‖ salt ‖ address(20) ‖ blind(32))
grant id = H(pad32("midnight:account:grant:id:evm:v2") ‖ A    ‖ address(20) ‖ blind(32) ‖ origin_hash(32) ‖ slot(1))
```

These are width class 52 of the shared descriptor module (`modules/WalletArmDescriptors.compact`). Every readable arm derives an `evm_eip712` target's entry with the same recipe.

Every path that admits a key takes the secp256k1 **point** and derives the address itself (spec FR-011). Before that, it refuses the point at infinity by its coordinates, which catches both encodings. A caller can never present an address without a key.

## 2. The blind

`blind = H(pad32("midnight:account:blind:evm:v2") ‖ r ‖ s)`, where `r ‖ s` is the low-S canonical form (big-endian, 32 bytes each) of the wallet's `personal_sign` signature (EIP-191 version `0x45`, Q25) over this readable request:

```
Midnight Passport account privacy key (v1)
Network: <network name>
Wallet: Ethereum address <EIP-55 address>
Account index: <0 … 4294967295>
Warning: this signature reveals the privacy key of this Passport account.
Anyone who obtains it can link this wallet to that account.
Sign it only in a Midnight Passport client you trust.
It authorises nothing: no transfer, no new device, no grant.
```

The procedure:

- The client asks for the signature **twice** and refuses the wallet if the two canonical forms differ. Such a wallet is non-deterministic (MPC, hedged nonces), so its blind could never be derived again.
- The client recovers the device's public point from the same signature and checks that it hashes to the wallet's address.
- The `personal_sign` hash preimage begins `0x19 0x45` (`0x19` and `'E'` of `"Ethereum Signed Message:\n"`), and every authorisation's hash preimage begins `0x19 0x01`. The preimages are disjoint, so the two digests coincide only on a keccak256 collision: a blind signature is never an authorisation, and an authorisation is never a blind signature. No circuit consumes a `personal_sign` digest.
- A restored client derives `blind_0 … blind_k` and finds its accounts by testing entries (`restoreEvmDevices`).

## 3. Domain

```
EIP712Domain(string name,string version,address verifyingContract)
name               "Midnight Passport Account"
version            "2"
verifyingContract  the low 20 bytes of keccak256(A)
```

There is no `chainId` and no `salt`. The contract holds no network value (Q4), and the cross-network clone argument is in section 10. The circuit recomputes the domain separator on every call: it is constant per account, but a cache would need a ledger or constructor field (FR-001).

What the wallet signs:

```
digest = keccak256(0x19 ‖ 0x01 ‖ domainSeparator ‖ hashStruct(message))
```

## 4. Encoding

This is EIP-712 `encodeData`, one 32-byte word per member:

| Member type | Word |
|---|---|
| `bytes32` | the 32 bytes |
| `address` | 12 zero bytes ‖ the 20 bytes |
| `uint8`, `uint32`, `uint64`, `uint128` | big-endian, zero-extended |
| `bool` | 0 or 1 as a uint |
| `string`, `bytes` | keccak256 of the content |
| nested struct | its `hashStruct` |

The byte order of points and field elements follows Q29:

- secp256k1 and P-256 coordinates are big-endian (SEC1).
- JubJub coordinates and other `Field` values are little-endian, as the contract encodes them.

Text members:

- `scheme` is a registered tag's text, without its zero padding.
- `origin` is a passkey's exact 21-byte origin, which must be visible ASCII.
- `siteLabel` is a 32-byte zero-padded site label, shown with its zero bytes as spaces. It is 32 characters long. Its grammar makes the shown text one-to-one with the stored bytes: one or more visible words separated by single spaces, then zero bytes only.
- `effect` is a circuit-fixed line.

## 5. Types

There are 16 primary types, one per operation and role. The device role's 13 share the frame `bytes32 account, address device, uint64 authNonce`. The grantee role's 3 share `bytes32 account, address grantee, string siteLabel, uint8 slot, uint64 issuedAt, uint64 grantNonce`. A grantee's frame never carries `auth_nonce`.

| Circuit | Primary type |
|---|---|
| `withdraw_unshielded_with_evm_eip712` | `WithdrawUnshielded(bytes32 account,address device,uint64 authNonce,bytes32 color,uint128 amount,bytes32 recipient)` |
| `withdraw_shielded_with_evm_eip712` | `WithdrawShielded(…frame…,bytes32 color,uint128 amount,bytes32 recipient,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |
| `withdraw_shielded_to_contract_with_evm_eip712` | `WithdrawShieldedToContract(…frame…,bytes32 color,uint128 amount,bytes32 recipientContract,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |
| `append_inbox_with_evm_eip712` | `AppendInbox(…frame…,bytes entry)` |
| `rotate_enc_key_with_evm_eip712` | `RotateEncKey(…frame…,string effect,bytes32 newKey)` |
| `add_device_with_evm_eip712` | `AddDevice(…frame…,string effect,<Scheme>Device newDevice)` |
| `remove_device_with_evm_eip712` (descriptor) | `RemoveDevice(…frame…,<Scheme>Device target,uint32 targetEpoch,uint64 targetCounter)` |
| `remove_device_with_evm_eip712` (literal, Q20) | `RemoveUnknownDevice(…frame…,string effect,bytes32 entry)` |
| `issue_grant_with_evm_eip712` | `IssueGrant(…frame…,string effect,<Scheme>Grantee grantee,bool withdrawUnshielded,bool withdrawShielded,bool withdrawShieldedToContract,bool read,bytes32 color,uint8 recipientKind,bytes32 recipient,uint128 maxCoinValue,uint128 perCallCap,uint128 cap,uint64 expiresAt,bytes32 passkeyRpHash,bytes32 readKey,uint64 windowLength,uint128 windowCap,bool callerPinned,bytes32 caller)` |
| `revoke_grant_with_evm_eip712` | `RevokeGrant(…frame…,<Scheme>Grantee grantee)` |
| `revoke_all_grants_with_evm_eip712` | `RevokeAllGrants(…frame…)` |
| `publish_recovery_session_with_evm_eip712` | `PublishRecoverySession(…frame…,string effect,bytes32 recoveryKeyX,bytes32 recoveryKeyY,bytes32 sessionNonce,bytes32 phi1,bytes32 phi2,bytes32 phi3,bytes32 phi4,uint8 phiLength,bytes wrap)` |
| `recover_cancel_with_evm_eip712` | `CancelRecovery(…frame…)` |
| `withdraw_unshielded_with_grant_evm_eip712` | `WithdrawUnshieldedAsGrantee(…grantee frame…,bytes32 color,uint128 amount,bytes32 recipient)` |
| `withdraw_shielded_with_grant_evm_eip712` | `WithdrawShieldedAsGrantee(…grantee frame…,bytes32 color,uint128 amount,bytes32 recipient,bytes changeEntry,bytes32 encryptionKey,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |
| `withdraw_shielded_to_contract_with_grant_evm_eip712` | `WithdrawShieldedToContractAsGrantee(…grantee frame…,bytes32 color,uint128 amount,bytes32 recipientContract,bytes changeEntry,bytes32 encryptionKey,bytes32 coinNonce,uint128 coinValue,uint64 coinMerkleIndex,uint128 change)` |

The exact `encodeType` strings, 32 of them counting each descriptor scheme, are in the vector file under `typeStrings`.

The nested descriptor types follow Q28, one per target scheme. The parent's type string names the nested type, so the parent type hash follows the scheme:

| Scheme (tag) | Device type | Grantee type |
|---|---|---|
| `evm_eip712` | `EvmDevice(string scheme,address wallet,bytes32 privacySalt)` | `EvmGrantee(string scheme,address wallet,bytes32 privacySalt,string siteLabel,uint8 slot)` |
| `sol_ed25519` | `SolanaDevice(string scheme,bytes32 publicKey,bytes32 privacySalt)` | `SolanaGrantee(string scheme,bytes32 publicKey,bytes32 privacySalt,string siteLabel,uint8 slot)` |
| `jubjub` | `JubjubDevice(string scheme,bytes32 x,bytes32 y)` | `JubjubGrantee(string scheme,bytes32 x,bytes32 y,bytes32 siteLabelHash,uint8 slot)` |
| `k256` | `K256Device(string scheme,bytes32 x,bytes32 y,uint8 envelope)` | `K256Grantee(string scheme,bytes32 x,bytes32 y,uint8 envelope,bytes32 siteLabelHash,uint8 slot)` |
| `p256` | `PasskeyDevice(string scheme,bytes32 x,bytes32 y,string origin,bytes32 passkeyRpHash)` | `PasskeyGrantee(string scheme,bytes32 x,bytes32 y,string origin,uint8 slot)` (its RP is the scope's `passkeyRpHash`) |

The circuit derives the target's entry or grant id from exactly these values, with the target scheme's own recipe (FR-005). An unregistered tag is refused (the S1 tightening).

Two members are shown as numbers (Q35; a labelled `string` member is a `v3` candidate). A client shows the meaning beside each:

| Member | Value | Meaning |
|---|---|---|
| `IssueGrant.recipientKind` | 0 | any recipient (no pin) |
| | 1 | pinned to a user address (unshielded) |
| | 2 | pinned to a Zswap coin public key (shielded) |
| | 3 | pinned to a contract (direct transfer) |
| `K256Device.envelope`, `K256Grantee.envelope` | 0 | the key signs SHA-256 of the challenge |
| | 1 | the key signs through a connector's `signData` prefix (read-only grants only) |

The effect lines (FR-023, Q20) are circuit constants:

| Type | `effect` |
|---|---|
| `AddDevice` | Gives this key FULL control of this account |
| `IssueGrant` | Lets this key use this account within the limits below |
| `PublishRecoverySession` | Sets this account's recovery key |
| `RotateEncKey` | Sets the key that can read this account's private coin records |
| `RemoveUnknownDevice` | Removes a device this wallet cannot identify |

## 6. What is shown, and the four labelled values

Every member is a value shown in full: an identifier, a key, an amount, a counter, a witness value, a ciphertext as `bytes`, or circuit-fixed text. The offline suite classifies every member of every type, and fails on a member it cannot classify. Exactly four hash-like values appear, each under a fixed name, and none of them grants authority (FR-004; Q17, Q20, Q21):

| Member | Value | Why it cannot be a preimage |
|---|---|---|
| `siteLabelHash` (`JubjubGrantee`, `K256Grantee`) | a `jubjub`/`k256` grantee's `origin_hash` | upstream hashes a client id of any length; the client shows the client id beside it |
| `passkeyRpHash` (`PasskeyDevice`, `IssueGrant`) | a passkey's `rp_id_hash` | the RP ID may be a registrable parent of the origin's host; the client shows the RP ID beside it |
| `privacySalt` (`EvmDevice`, `SolanaDevice`, `EvmGrantee`, `SolanaGrantee`) | the target's blind | a secret by design (section 2) |
| `entry` (`RemoveUnknownDevice` only) | a literal device entry, under "Removes a device this wallet cannot identify" | revocation only; the caller's own post-roll entry can never be removed |

Ledger-pinned private openings are not shown: the signer's own blind and use counter, `scope_salt`, `spent_prev`, and the grantee's pinned recipient and maximum coin value. They are checked against state, not chosen. A shielded spend shows its coin by nonce, value and Merkle index. Its colour is `color`, because the circuit asserts `coin.color == color`. The change is `coinValue − amount`.

**Verifiable by eye** (FR-022):

- the EVM address (MetaMask shows `address` members in EIP-55 form);
- the passkey origin;
- the 32-byte Solana key (shown as hex; the client shows the base58 form beside it).

**Shown only**: `k256`, `jubjub` and passkey public keys.

**Length bound per layout**:

- every struct is fixed at its member count;
- the dynamic members are `entry` and `changeEntry` (192 bytes) and `wrap` (64 bytes);
- the longest message is `IssueGrant`: 22 words plus a 6-word grantee struct (7 words for `K256Grantee`).

## 7. Client codec

`src/wallet/evm-eip712-codec.ts` has two parts:

- a general EIP-712 encoder written from the EIP;
- one builder per operation, producing `eth_signTypedData_v4` JSON. The `types` object holds only the primary type, its nested type and `EIP712Domain`, because ethers refuses unused types.

The builders are strict. They range-check every integer, check labels and origins against the circuit's text rules, and refuse an unregistered tag. These are client-layer refusals, before any wallet sees the message.

## 8. Frozen vectors

`src/tests/vectors/evm-eip712-v2.json` holds:

- **53 positive vectors.** Every primary type is covered, and every descriptor-taking type with all five schemes. The vectors include edge values (`2^128 − 1`, `2^64 − 1`, zeros), dynamic members with leading zero bytes and all-zero bytes, and the passkey parent-domain shape. Each vector holds its inputs, its typed data, the `encodeType` string, the domain separator, the struct hash and the digest. **ethers' `TypedDataEncoder` computed every hash.**
- **14 negative vectors.** Each names the layers that must refuse it:

| Negative | Refused by |
|---|---|
| an unregistered device tag; a space-padded registered tag; a grant-id tag as a device tag | client, runtime |
| a passkey origin with a space or a NUL | client, runtime |
| a site label ending in a space, with a double space, or empty | client, runtime |
| an unregistered grant-id tag | client, runtime |
| an amount above the spent coin (device and grantee) | client, runtime |
| an amount of 2^128; an `authNonce` of 2^64; a 191-byte inbox entry | client, runtime |

"Runtime" is the generated JavaScript of the contract's pure circuits. In the impure circuits the same asserts are constraints of the proof: the constraint-level refusals are recorded per circuit (`evm-eip712-prover.ts`).

Agreement, from `npm run test:evm_eip712-offline`: the contract's pure circuits, the client codec and the frozen values agree on all 53 vectors. To reproduce the frozen values with ethers, which is not a dependency (Q24):

```sh
npm i --no-save ethers@6.17.0 && npx tsx src/tests/evm-eip712-ethers.ts
```

That script also checks that `signTypedData` is byte-identical to ethers'.

## 9. The seam and the acceptance policy

`require_authorised_with_evm_eip712<T>(auth, type_hash, tail)` follows upstream `p256`'s order (FR-007):

1. the device's address derived from the presented point, `evm_eip712_address(auth.pk)` (the point at infinity refused in both encodings);
2. membership of the single-use entry at the active epoch;
3. `r ≠ 0` and `s ≠ 0`;
4. ECDSA verification of `digest(account, struct_hash)`, where the seam builds `struct_hash` itself from the frame and the export's tail;
5. the entry rolled to its successor;
6. `auth_nonce` advanced and `round` bumped.

Any failure aborts the whole call. The trailing argument `EvmEip712Auth { pk, use_counter, blind, sig }` is internal.

There are three entry points, and one internal core that only they call: `require_authorised_with_evm_eip712<T>` (one message type), `require_authorised_with_evm_eip712_either<T, U>` (`remove_device`'s two forms: it builds both struct hashes from its own frame and verifies the one the call selects) and `require_authorised_with_evm_eip712_bare` (a type with no members of its own, `RevokeAllGrants` and `CancelRecovery`). Each derives the address and builds its frame, then hands the address and the struct hash to `evm_eip712_verify_and_roll`. Each returns the caller's post-roll entry, which `remove_device`'s S13 guard needs.

**The grant seam** (`require_grant_with_evm_eip712<T>`, grantee role) applies the same rule to the grantee frame (`account`, `grantee`, `siteLabel`, `slot`, `issuedAt`, `grantNonce`). It derives the grantee's address from the presented point, then the grant id from that address, the blind, H(origin tag ‖ label) and the slot. It reads `issuedAt` and the nonce from the record, never `auth_nonce`, and touches no device entry (FR-008). The MIP's steps run in order: the record by id; liveness (active, epoch, generation, expiry); upstream's shared `check_spend_scope` (operation, caller pin, object, per-call cap, spent opening, cumulative cap, recipient pin); `r ≠ 0`, `s ≠ 0`; the signature; the record written back with its nonce advanced and the new spent commitment; `round` bumped. The shielded twins assert `coin.color == color` and run upstream's `check_shielded_grant_bounds` (coin value, live `enc_key`) first.

**The arm's own rules on top of upstream's chips.**

- Every shielded spend asserts `coin.color == color` (FR-010) and `amount ≤ coin.value`.
- `add_device` derives the new entry at the current `device_epoch` and counter 0, so the arm cannot plant a future-epoch entry.
- `remove_device` takes the target's epoch and counter (removal only reduces authority, so a planted `device_epoch + 1` entry can be evicted), or a literal entry under the Q20 line. The Maybe that selects the form must be canonical when absent.
- `issue_grant` hashes the read key as zero, and requires it to be zero, when `read` is off (audit G1E-7). It requires a non-zero key when `read` is on. It admits an RP hash only for a passkey grantee, so that no other hash-like value ever appears in an approval. It stores SHA-256 of the shown read key as `read_pk_hash`, as the grants MIP defines it.

**The seam owns the frame** (audit G1E-1, G0 C9). An export passes only its operation's type hash and tail, from the module's `evm_eip712_parts_<operation>` circuit. The seam supplies every frame value itself: `account` is `kernel.self()`, `device` is the address of the presented point, and `authNonce` is the ledger's (read before this call advances it). No export can name an account, a device or a nonce, so an entry is matched and a signature verified only for the address of the key that signed. The exported struct-hash oracles `evm_eip712_struct_<operation>` are built from the same frame builders (`evm_eip712_device_struct<T>`, `evm_eip712_grantee_struct<T>`) and the same parts, so an oracle and its export cannot diverge. `keccak256` over a tuple whose last member is a generic tuple hashes that member flat (QA-A1; all 53 frozen vectors still agree with ethers), and the refactor cost no rows. A malicious-prover mutant that forges the derived address in the generated JavaScript (so that the victim's entry matches while the attacker's key signs) is refused at the proof server (`evm-eip712-prover.ts`, section `frame`).

The table below gives the acceptance policy. Each rule's refusing layer was measured with the JavaScript checks bypassed, after a proved positive control (`evm-eip712-prover.ts`, 37 cases, 2026/10/15).

| Rule | Enforced by | Refused at (simulator / prover) |
|---|---|---|
| The signature covers exactly the executed values (binding: `newKey`, `account`, `device`, `authNonce`, `effect`, the domain's name, version and verifyingContract, the type name, a member name) | the in-circuit digest + `secp256k1EcdsaVerify` | "invalid signature" / `/check` 400 "Failed direct assertion" |
| The key, blind and counter open a live entry (an unenrolled key, another blind, a wrong counter) | the entry membership assert | "unknown device entry" / `/check` 400 |
| `r ≠ 0`, `s ≠ 0`, and `(r, s) = (0, 0)` | the arm's zero-scalar assert (and ZKIR's inverse) | the arm's assert / `/check` 400. `(0, 0)` verifies in the generated JavaScript once inverses of 0 are taken as 0, so only the arm's assert fires there, and the proof still fails |
| Both S forms accepted | `secp256k1EcdsaVerify` (FIPS 186-5) | the high-S twin proves and lands. The low-S original is then refused: "unknown device entry" (simulator), `/check` 400 (prover), and node `1010: Invalid Transaction: Custom error 104` for its proof made before the twin landed (three submissions; a fresh call from the same wallet landed in between) |
| The point at infinity (flagged) | ZKIR coordinate extraction; the arm's coordinate guard and the stdlib's struct guard (defence in depth) | "cannot extract the x-coordinate" / "Cannot extract coordinates of the Secp256k1 identity" |
| The unflagged `(0, 0)` | the runtime validator; the honest proof server's input decoding; in-circuit, the `Secp256k1Point` on-curve assignment (`(0, 0)` is not on the curve) | type error / proof-server input decoding "Failed to decode" (a decoding refusal of an honest prover, not a constraint failure; see the note below) |
| A coordinate not reduced below `p` (QA-1) | the runtime's foreign-field encoder; the honest proof server's input decoding; for soundness, the size argument below | type error / proof-server input decoding "The encoded value of type Secp256k1Point is not in canonical form" (not a constraint failure) |
| Replay across accounts, arms (`k256` ↔ `evm_eip712` with the same key), operations (`CancelRecovery`, `RevokeAllGrants`), roles (a grantee type) and nonces | the domain and type hash in the digest; the arm-specific digest rule | "invalid signature" (or "unknown device entry" for a consumed entry) / `/check` 400 |

**Decoding refusals are not constraint refusals** (audit G1E-4). The last two rows above are refused by the honest toolchain: the runtime's encoder and the proof server's input decoder. A malicious prover builds its own witness and never runs that decoder, so these rows do not show that a constraint refuses the value. The closure for this arm is a size argument. A secp256k1 coordinate `c` has a second 32-byte representation `c + p` only when `c < 2^256 − p ≈ 2^32`. For any real key the cast to `Bytes<32>` therefore has no alternative output, and forging an address through it would also need a keccak256 preimage. The same bound applies to the `secp256k1PointX` inside `secp256k1EcdsaVerify`. The `(0, 0)` point is refused in-circuit by the on-curve assignment. Constraint-level canonicity of the foreign-field-to-bytes cast itself remains an upstream residual (#182).

## 10. Network (Q4, FR-015)

The domain carries no network value, as upstream's arms carry none. An account can be cloned onto another network at the same address. No in-contract value can tell the clone apart, because a sealed salt is copied with the clone and circuits cannot read the network id. Clients therefore use random deploy nonces, and the upstream ledger issue proposes binding the network id. The full argument is completed with the MIP text at S10.

## 11. Measurements (S3E spike; per-circuit report at S10)

Mock-compile rows of the worst-case layouts:

| Circuit | k | rows |
|---|---|---|
| `rotate_enc_key` | 17 | 102,693 |
| `append_inbox` | 17 | 111,550 |
| `publish_recovery_session` | 17 | 118,329 |
| `withdraw_shielded` | 18 | 138,639 |
| `add_device` | 18 | 163,793 |
| `revoke_grant` | 18 | 171,763 |
| `withdraw_shielded_with_grant` | 18 | 179,607 |
| `remove_device` (both forms) | 18 | 183,957 |
| `withdraw_shielded_to_contract_with_grant` | 18 | 185,330 |
| `issue_grant` | 18 | 232,006 |

Built so far:

| Circuit | k | rows | verifier key | prover key | measured on the shared stack |
|---|---|---|---|---|---|
| `activate_initial_device_with_evm_eip712` | 16 | 42,289 | 3,321 B | 142.6 MB | prove + submit ≈ 23 s |
| `rotate_enc_key_with_evm_eip712` | 17 | 102,705 | 3,321 B | 285.2 MB | prove ≈ 14–16 s |
| `append_inbox_with_evm_eip712` | 17 | 111,562 | 3,321 B | 285.2 MB | |
| `withdraw_unshielded_with_evm_eip712` | 17 | 107,686 | 3,321 B | 285.2 MB | |
| `withdraw_shielded_with_evm_eip712` | 18 | 138,652 | 3,321 B | 570.5 MB | contract proof ≈ 19 s |
| `withdraw_shielded_to_contract_with_evm_eip712` | 18 | 144,375 | 3,321 B | 570.5 MB | |
| `add_device_with_evm_eip712` | 18 | 167,206 | 3,321 B | 570.5 MB | |
| `remove_device_with_evm_eip712` | 18 | 181,730 | 3,321 B | 570.5 MB | |
| `issue_grant_with_evm_eip712` | 18 | 235,442 | 3,321 B | 570.5 MB | |
| `revoke_grant_with_evm_eip712` | 18 | 175,193 | 3,321 B | 570.5 MB | |
| `revoke_all_grants_with_evm_eip712` | 17 | 98,457 | 3,321 B | 285.2 MB | |
| `withdraw_unshielded_with_grant_evm_eip712` | 18 | 137,116 | 3,321 B | 570.5 MB | |
| `withdraw_shielded_with_grant_evm_eip712` | 18 | 179,620 | 3,321 B | 570.5 MB | |
| `withdraw_shielded_to_contract_with_grant_evm_eip712` | 18 | 185,343 | 3,321 B | 570.5 MB | |

Moving the frame into the seam (G1E-1) changed no row count. Every verifier key is 3,321 bytes. Proving times go into the per-circuit report at S10.
