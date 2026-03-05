# TTT2 Artifacts (KO7 Full Step)

This folder stores reproducibility artifacts for the KO7 full-step TRS.

## Input
- `KO7_full_step.trs`: input TRS (8 rules, 7 constructors)

## TTT2 Proof Outputs

### Certified (YES → CeTA CERTIFIED)
- `KO7_FAST.cpf`: FAST strategy (DP + SCC + subterm criterion)
- `KO7_LPO.cpf`: LPO strategy (lexicographic path order, rule removal)
- `KO7_COMP.cpf`: COMP strategy (DP + TDG + SCC + subterm + matrix + LPO)

### Rejected (MAYBE → CeTA REJECTED)
- `KO7_KBO.cpf`: KBO strategy (Knuth-Bendix order)
- `KO7_POLY.cpf`: POLY strategy (polynomial interpretation, `-ib 5 -ob 6`)
- `KO7_MAT2.cpf`: MAT(2) strategy (matrix interpretation, dim 2)
- `KO7_MAT3.cpf`: MAT(3) strategy (matrix interpretation, dim 3)

### Not Certifiable
- `KO7_FBI.cpf`: FBI strategy (forward/backward instantiation) — MAYBE, no proof generated

## Prior Text Outputs
- `KO7_full_step_TTT2_results_FAST.txt`: FAST strategy human-readable output
- `KO7_full_step_TTT2_results_POLY.txt`: POLY strategy human-readable output

## Certification Log
- `KO7_CeTA_certification.txt`: full CeTA 2.36 verification results for all strategies

## Generation

TTT2 1.20 on WSL:
```bash
cd /mnt/c/Users/Moses/OperatorKO7/Comments/ttt2-1.20/ttt2
./ttt2 -cpf <TRS>                              # FAST (default)
./ttt2 -cpf -s lpo <TRS>                       # LPO
./ttt2 -cpf -s 'dp;...' <TRS>                  # COMP (full strategy string in certification log)
./ttt2 -cpf -s kbo <TRS>                       # KBO
./ttt2 -cpf -s 'poly -direct -ib 5 -ob 6' <TRS>   # POLY
./ttt2 -cpf -s 'matrix -dim 2 -ib 2 -ob 2' <TRS>  # MAT(2)
./ttt2 -cpf -s 'matrix -dim 3 -ib 2 -ob 2' <TRS>  # MAT(3)
```

Post-processing: raw TTT2 output has a `YES`/`MAYBE` line before XML; CPF files here have that line stripped.

## CeTA Certification (2026-03-04)

CeTA 2.36 via web interface at http://138.232.18.220/tool/ceta (official binary host was down).

| Strategy | TTT2 | CeTA |
|----------|------|------|
| FAST | YES | **CERTIFIED** |
| LPO | YES | **CERTIFIED** |
| COMP | YES | **CERTIFIED** |
| KBO | MAYBE | REJECTED |
| POLY | MAYBE | REJECTED |
| MAT(2) | MAYBE | REJECTED |
| MAT(3) | MAYBE | REJECTED |
| FBI | MAYBE | N/A |

All modular/structural methods certify. All global/compositional methods fail.
