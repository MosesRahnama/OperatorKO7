# OperatorKO7 Micro-Benchmarks

This note records lightweight artifact-facing replay costs for the active repository state.

## Environment

- Machine: `MOSES-DELL-XPS`
- OS: `Windows 10 Home`, version `2009`, build `26200`
- CPU: `12th Gen Intel(R) Core(TM) i9-12900HK`
- Visible RAM: `33217592 KB`

## Lean Replay Timings

Measured as single warm-cache runs from the repository root on 2026-03-20.

| Command | Time |
|---|---:|
| `lake build OperatorKO7` | `9.281s` |
| `lake build OperatorKO7.SchemaAPI` | `8.460s` |
| `lake exe verifyTpdbExport` | `3.480s` |
| `lake build OperatorKO7.Meta.DM_OrderType_LowerBound` | `4.412s` |
| `lake build OperatorKO7.Meta.ContextClosed_SN_Full` | `4.510s` |
| `lake build OperatorKO7.Meta.MPO_ProofTheoreticBound` | `9.817s` |

These numbers are intended as reviewer guidance, not as a performance claim. They are
single-run wall-clock measurements in an already-initialized local workspace.

## Archived External Tool Timings

The repository archives the TTT2/CeTA validation trail under `Artifacts/ttt2/`.

TTT2 wall-clock times recorded in the archived runs / paper table:

| Strategy | TTT2 result | Time |
|---|---|---:|
| `FAST` | `YES` | `0.06s` |
| `COMP` | `YES` | `0.70s` |
| `LPO` | `YES` | `0.02s` |
| `POLY` | `MAYBE` | `0.15s` |
| `KBO` | `MAYBE` | `0.02s` |
| `MAT(2)` | `MAYBE` | `0.31s` |
| `MAT(3)` | `MAYBE` | `0.37s` |
| `FBI` | `MAYBE` | `0.17s` |

The archived CeTA certification log records verdicts and provenance but does not include
per-strategy wall-clock timings for the web-interface run. The artifact therefore reports
the archived TTT2 times directly and treats the CeTA layer as a checked verdict trail
rather than a timed replay benchmark.
