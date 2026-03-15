import OperatorKO7.Meta.TPDB_Export

/-!
Tiny smoke test for the KO7 TPDB exporter.

Why this file exists:
- Prints the exported full-step TRS so reviewers can regenerate the external
  TTT2 input directly from Lean.
- Checks the exact-match theorem on the generated text.
- Like `Test/Sanity.lean`, this is lightweight and does not contribute to the
  theorem development itself.
-/

#eval IO.println OperatorKO7.ko7_full_step_tpdb
#check OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
