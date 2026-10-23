# `evm_k256` measurements

**Sizes** (k, rows and key sizes) are those of the circuits in this tree: k and rows by `zkir-v3 mock-compile` of each circuit's `.zkir`, and the proof server's `/k` agrees for all 16; the key sizes are those of `compact compile +0.35.0 --feature-zkir-v3`. **Proving times** were measured on 2026-10-18 (`issue_grant_with_evm_k256`: 2026-10-20) on the circuits of that date, before the fixed V1 domain and the k256 core's acceptance rules, which changed each circuit's rows by -14 % to +5 % (the activation grew: it now applies the key rule itself); "Rows when timed" gives their size then, and four circuits were then one k higher. Proving time depends mainly on k, so the times are expected to be lower for those four and similar for the rest; they are re-measured with the next proof-server run. Compact 0.35.0 (`--feature-zkir-v3`), midnight-zkir 3.1.0-rc.1, runtime 0.20.0, ledger 9; proof server midnightntwrk/proof-server:9.0.0-rc.8 on the reference localnet (node 2.1.0-rc.4).

## Per circuit

| Circuit | k | Rows | Prover key (MiB) | Verifier key (bytes) | Rows when timed | Proving time, median (s) | Observations | Min / max (s) |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `activate_initial_device_with_evm_k256` | 15 | 17,953 | 68.0 | 3,321 | 17,139 | 2.8 | 7 | 2.7 / 3.6 |
| `revoke_all_grants_with_evm_k256` | 16 | 54,033 | 136.0 | 3,321 | 62,470 | 7.6 | 2 | 7.6 / 7.6 |
| `recover_cancel_with_evm_k256` | 16 | 54,735 | 142.0 | 3,465 | 63,172 | 5.9 | 4 | 5.8 / 7.2 |
| `rotate_enc_key_with_evm_k256` | 16 (timed at 17) | 58,281 | 136.0 | 3,321 | 60,921 | 9.9 | 9 | 9.7 / 13.5 |
| `append_inbox_with_evm_k256` | 17 | 61,333 | 272.0 | 3,321 | 69,778 | 13.5 | 2 | 13.5 / 13.5 |
| `withdraw_unshielded_with_evm_k256` | 17 | 64,757 | 272.1 | 3,321 | 73,202 | 13.1 | 10 | 10.5 / 15.1 |
| `publish_recovery_session_with_evm_k256` | 17 | 68,112 | 284.0 | 3,465 | 76,557 | 10.7 | 9 | 10.4 / 14.8 |
| `withdraw_shielded_with_evm_k256` | 17 | 87,447 | 272.1 | 3,321 | 95,892 | 14.0 | 3 | 10.7 / 14.1 |
| `withdraw_unshielded_with_grant_evm_k256` | 17 | 90,823 | 272.1 | 3,321 | 99,268 | 10.7 | 22 | 10.4 / 15.6 |
| `withdraw_shielded_to_contract_with_evm_k256` | 17 | 93,150 | 272.1 | 3,321 | 101,595 | 14.6 | 3 | 11.5 / 15.2 |
| `add_device_with_evm_k256` | 17 (timed at 18) | 126,449 | 304.1 | 3,705 | 133,169 | 26.1 | 18 | 24.8 / 35.5 |
| `withdraw_shielded_with_grant_evm_k256` | 17 (timed at 18) | 126,817 | 272.2 | 3,321 | 133,618 | 24.4 | 30 | 22.9 / 34.4 |
| `revoke_grant_with_evm_k256` | 17 (timed at 18) | 130,788 | 304.1 | 3,705 | 137,452 | 26.6 | 6 | 25.9 / 38.4 |
| `withdraw_shielded_to_contract_with_grant_evm_k256` | 18 | 130,923 | 544.2 | 3,321 | 139,321 | 24.1 | 29 | 23.0 / 33.3 |
| `remove_device_with_evm_k256` | 18 | 133,771 | 608.1 | 3,705 | 142,161 | 27.2 | 9 | 25.9 / 37.3 |
| `issue_grant_with_evm_k256` | 18 | 181,201 | 608.1 | 3,705 | 189,595 | 28.0 | 43 | 23.5 / 43.5 |

All 16 circuits are at k ≤ 18 (k 18: three; the largest, `issue_grant_with_evm_k256`, at 181,201 rows). Their verifier keys total 54,960 bytes; with `evm_k256` registered in the client's arm registry (`ARM_REGISTRY` in `src/wallet/signer.ts`, from which `ARMS` follows), `planWaves` packs the 68-circuit roster into waves of at most 15,000 verifier bytes each (`evidence/evm-k256/full-roster-deploy.json`).

**Scope of the timings.** Each observation is the wall time of one `/prove` request to the proof server, recorded by the test harness (`src/tests/constraint-negative.ts`) during the constraint-level suite (`npm run test:evm_k256`): the honest calls and the positive controls that precede the negatives, against local account states. It includes the upload of the prover key with the request and the proof server's key loading; it excludes signing, local execution, balancing and inclusion. Requests whose verifier key differs from the measured build are excluded. These are observations, not a latency distribution.

**Hardware.** Apple M4 Max, 16 logical CPUs, 48 GiB host RAM (darwin/arm64). Proving in Docker: aarch64, 12 CPUs, no container memory limit (the Docker VM has 30.1 GiB).

**Memory.** A k 18 proof needs the proof server's resident memory plus the proof's own. On this VM (30.1 GiB, no container limit), a proof server that has proved many k 18 circuits holds most of the VM, and the next k 18 proof can exceed it; the suite therefore starts each section from a freshly restarted proof server, and a request that finds the server gone is retried once after a restart (no such restart in the measured runs). `docker stats`, sampled once a minute during the measured runs of 2026-10-18 (328 samples), peaks at 20.7 GiB. This is an operating note, not a minimum-memory requirement. The proof server image has no `cat`, so the container's `memory.peak` is not read.

**Evidence.** [Circuit sizes, key hashes and timings of the 2026-10-18 measurement](evidence/evm-k256/circuit-sizes.json); [the prover suite's cases and refusing layers](evidence/evm-k256/prover-suite.json).
