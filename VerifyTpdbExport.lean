import OperatorKO7.Meta.TPDB_Export

open OperatorKO7

/-- Runnable artifact check for the KO7 TPDB export bridge.
It verifies the exporter text against both the embedded checked literal and the
on-disk `Artifacts/ttt2/KO7_full_step.trs` file. -/
def main : IO UInt32 := do
  let artifactPath := "Artifacts/ttt2/KO7_full_step.trs"
  let onDisk <- IO.FS.readFile artifactPath
  if ko7_full_step_tpdb != ko7_full_step_tpdb_artifact_text then
    IO.eprintln "Exporter does not match embedded artifact text."
    return 1
  if onDisk != ko7_full_step_tpdb_artifact_text then
    IO.eprintln s!"On-disk artifact mismatch: {artifactPath}"
    return 1
  IO.println s!"TPDB export verified against embedded text and {artifactPath}."
  return 0
