import CLightLean.Exec.CSmithIO
import Test.CSmithSeeds.MinimalChecksumProgram

open CLightLean.Exec

/-- Execute the checked-in default CSmith program and print exactly one host
result-envelope line. Normal completion exits with code zero; initialization
failures and executor unsupported/stuck outcomes emit their envelope first and
then exit with code one. -/
def main : IO Unit := do
  let result ← runCSmithProgramUntilTermination Test.CSmithSeeds.MinimalChecksumProgram.prog
  IO.println (renderCSmithProgramEnvelope result)
  match result with
  | .ok (.completed ..) => pure ()
  | _ => IO.Process.exit 1
