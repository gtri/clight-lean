import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.MinimalChecksumGenerated

/- The fixture is a structurally faithful generated export with root-level
declarations. This alias gives the integration test its stable module-qualified
program path without modifying that generated AST. -/
namespace Test.CSmithSeeds.MinimalChecksumGenerated

def prog : program_type function := _root_.prog

end Test.CSmithSeeds.MinimalChecksumGenerated

namespace Test.Exec

open CLightLean.Exec

def minimalChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/-- The checked-in source-exported fixed-signature seed executes through the
CSmith-aware runner, exits normally, and emits precisely the canonical checksum
bytes `checksum = 1A2B\n`. The fixture is structurally faithful to the verified
exporter output. -/
def minimalChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.MinimalChecksumGenerated.prog 32 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == minimalChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

-- Execute the generated program through Lean's evaluator rather than proving
-- a HashMap-heavy reduction in the kernel. A false result raises an evaluation
-- error, so compiling this test checks the exit and exact stdout assertion.
#eval do
  if minimalChecksumGeneratedProgramRuns then
    IO.println "minimal fixed checksum CSmith program: pass"
  else
    throw (IO.userError "minimal fixed checksum CSmith program: failed")

end Test.Exec
