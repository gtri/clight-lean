import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.ArrayChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def arrayChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x45, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes the global array `values` as `[1, 2, 0x1A2B]`,
uses array-to-pointer decay and indexed dereferences to update `values[1]`,
then loads `values[2]` and `values[1]` to form the checksum `0x1A2E`. -/
def arrayChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.ArrayChecksumProgram.prog 128 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == arrayChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if arrayChecksumGeneratedProgramRuns then
    IO.println "array fixed checksum CSmith program: pass"
  else
    throw (IO.userError "array fixed checksum CSmith program: failed")

end Test.Exec
