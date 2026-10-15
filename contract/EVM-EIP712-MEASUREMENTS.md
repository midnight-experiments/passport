# `evm_eip712` measurements

Measured 2026/10/15. Compact 0.35.0 (`--feature-zkir-v3`), midnight-zkir 3.1.0-rc.1, runtime 0.20.0, ledger 9; proof server midnightntwrk/proof-server:9.0.0-rc.8 on the reference localnet (node 2.1.0-rc.4).

## Per circuit

| Circuit | k | Rows | Prover key (MiB) | Verifier key (bytes) | Proving time, median (s) | Observations | Min / max (s) |
|---|---:|---:|---:|---:|---:|---:|---|
| `activate_initial_device_with_evm_eip712` | 16 | 42,289 | 136.0 | 3,321 | 5.5 | 7 | 5.3 / 7.2 |
| `revoke_all_grants_with_evm_eip712` | 17 | 98,457 | 272.0 | 3,321 | 13.7 | 2 | 13.4 / 14.0 |
| `recover_cancel_with_evm_eip712` | 17 | 99,158 | 284.0 | 3,465 | 10.3 | 3 | 10.2 / 12.5 |
| `rotate_enc_key_with_evm_eip712` | 17 | 102,705 | 272.0 | 3,321 | 11.9 | 13 | 10.2 / 17.1 |
| `withdraw_unshielded_with_evm_eip712` | 17 | 107,686 | 272.0 | 3,321 | 12.2 | 3 | 11.7 / 14.9 |
| `append_inbox_with_evm_eip712` | 17 | 111,562 | 272.0 | 3,321 | 14.5 | 2 | 12.4 / 16.5 |
| `publish_recovery_session_with_evm_eip712` | 17 | 118,341 | 284.0 | 3,465 | 11.4 | 8 | 11.1 / 13.9 |
| `withdraw_unshielded_with_grant_evm_eip712` | 18 | 137,116 | 544.0 | 3,321 | 19.8 | 15 | 19.3 / 28.5 |
| `withdraw_shielded_with_evm_eip712` | 18 | 138,652 | 544.0 | 3,321 | 21.8 | 3 | 21.2 / 32.3 |
| `withdraw_shielded_to_contract_with_evm_eip712` | 18 | 144,375 | 544.0 | 3,321 | 24.2 | 3 | 20.9 / 33.0 |
| `withdraw_shielded_with_grant_evm_eip712` | 18 | 179,620 | 544.0 | 3,321 | 22.9 | 21 | 21.3 / 30.5 |
| `add_device_with_evm_eip712` | 18 | 183,290 | 608.0 | 3,705 | 24.8 | 6 | 24.3 / 39.7 |
| `withdraw_shielded_to_contract_with_grant_evm_eip712` | 18 | 185,343 | 544.0 | 3,321 | 23.3 | 22 | 22.4 / 30.5 |
| `revoke_grant_with_evm_eip712` | 18 | 191,268 | 608.1 | 3,705 | 32.0 | 2 | 30.5 / 33.5 |
| `remove_device_with_evm_eip712` | 18 | 197,801 | 608.0 | 3,705 | 25.2 | 5 | 25.1 / 34.1 |
| `issue_grant_with_evm_eip712` | 18 | 251,534 | 608.1 | 3,705 | 27.8 | 4 | 23.7 / 35.3 |

All 16 circuits are at k ≤ 18. Their verifier keys total 54,960 bytes; with `evm_eip712` registered in `ARMS`, `planWaves` packs the 68-circuit roster into waves of at most 15,000 verifier bytes each (`evidence/evm-eip712/full-roster-deploy.json`).

**Scope of the timings.** Each observation is the wall time of one `/prove` request to the proof server, recorded by the test harness (`src/tests/constraint-negative.ts`) during the constraint-level suite (`npm run test:evm_eip712`): the honest calls and the positive controls that precede the negatives, against local account states. It includes the upload of the prover key with the request and the proof server's key loading; it excludes signing, local execution, balancing and inclusion. Requests whose verifier key differs from the measured build are excluded. These are observations, not a latency distribution.

**Hardware.** Apple M4 Max, 16 logical CPUs, 48 GiB host RAM (darwin/arm64). Proving in Docker: aarch64, 12 CPUs, no container memory limit (the Docker VM has 30.1 GiB).

**Memory.** The shared proof server was killed twice by the Docker VM's out-of-memory handling while the suite ran (30.1 GiB VM, no container limit): once during a `/prove` of the grantee path and once on the positive control of `issue_grant_with_evm_eip712` (251,534 rows), each time after the server had held about 18 GiB resident across many earlier proofs. A server restarted before each part of the suite stayed between about 5 and 15 GiB (`docker stats` once a minute) and completed every proof. A k 18 proof of this arm therefore needs the proof server's own resident memory plus the proof's, so a shared server that proves many k 18 circuits should be restarted between runs or given more memory; this is an operating note, not a minimum-memory requirement. The proof server image has no `cat`, so the container's `memory.peak` is not available.

**Evidence.** [Circuit sizes, key hashes and timings](evidence/evm-eip712/circuit-sizes.json); [the prover suite's cases and refusing layers](evidence/evm-eip712/prover-suite.json).
