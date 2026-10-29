import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.GotoChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def gotoChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The forward goto skips the assignment of 99, resolves the labeled statement
from the function body, and continues at the checksum computation. -/
def gotoChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.GotoChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == gotoChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if gotoChecksumGeneratedProgramRuns then
    IO.println "goto fixed checksum CSmith program: pass"
  else
    throw (IO.userError "goto fixed checksum CSmith program: failed")

end Test.Exec
