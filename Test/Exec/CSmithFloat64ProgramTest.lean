import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.Float64ChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def float64ChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x41, 0x0a].foldl ByteArray.push ByteArray.empty

/- The fixture initializes a double global, performs add/multiply/divide with
binary64 rounding, then explicitly narrows to the fixed uint32 checksum ABI. -/
def float64ChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.Float64ChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == float64ChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if float64ChecksumGeneratedProgramRuns then
    IO.println "float64 fixed checksum CSmith program: pass"
  else
    throw (IO.userError "float64 fixed checksum CSmith program: failed")

end Test.Exec
