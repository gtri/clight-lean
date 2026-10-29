import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.GlobalChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def globalChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x43, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes the global `crc` to `0x1A2B`, loads and increments
it through ordinary global lvalue evaluation, stores it back, then passes the
reloaded value to the fixed-signature checksum helper. -/
def globalChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.GlobalChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == globalChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if globalChecksumGeneratedProgramRuns then
    IO.println "global fixed checksum CSmith program: pass"
  else
    throw (IO.userError "global fixed checksum CSmith program: failed")

end Test.Exec
