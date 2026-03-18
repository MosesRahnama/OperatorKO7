# TPDB Submission Prep

This note is a preparation layer for a future KO7 submission to the Termination
Problems Database. It is not itself the submission.

## Current Source of Truth

- Lean-side exporter/input artifact:
  `Artifacts/ttt2/KO7_full_step.trs`
- Lean-side verifier:
  `VerifyTpdbExport.lean`
- Replay command:

```bash
lake exe verifyTpdbExport
```

Run the verifier before staging any external submission material.

## What Is Already Archived

The repository already stores the external validation trail in `Artifacts/ttt2/`:

- input TRS
- TTT2 text outputs
- CPF certificates
- CeTA certification log

That is enough to prepare a TPDB-facing bundle without regenerating the artifacts first.

## Staging Helper

Create a TPDB-prep staging directory with:

```bash
python scripts/stage_tpdb_submission.py
```

Default output:

- `artifact/tpdb-submission/ko7.trs`
- `artifact/tpdb-submission/README.md`
- `artifact/tpdb-submission/METADATA_TEMPLATE.md`
- `artifact/tpdb-submission/PROVENANCE.txt`

## Suggested Submission Checklist

1. Re-run `lake exe verifyTpdbExport`.
2. Check that `artifact/tpdb-submission/ko7.trs` matches the intended public problem text.
3. Fill in `METADATA_TEMPLATE.md` with the repository URL, category choice, authorship,
   and benchmark notes.
4. Choose the target path in `https://github.com/TermCOMP/TPDB-ARI` according to the
   maintainers' current naming conventions.
5. Decide whether the complexity-category submission should reference the current
   lower/upper-bound story separately from the standard termination entry.

## Scope

This prep layer keeps the external submission work separate from the Lean development.
It documents provenance and staging only; it does not claim that the TPDB submission
has already been accepted upstream.
