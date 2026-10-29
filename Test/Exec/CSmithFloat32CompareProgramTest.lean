import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.Float32CompareProgram

namespace Test.Exec

open CLightLean.Exec

def float32CompareExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x37, 0x0a].foldl ByteArray.push ByteArray.empty

/- The fixture compares two ordered binary32 globals, executes the true branch,
and sends its uint32 result through the fixed checksum ABI. -/
def float32CompareGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.Float32CompareProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == float32CompareExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if float32CompareGeneratedProgramRuns then
    IO.println "float32 comparison CSmith program: pass"
  else
    throw (IO.userError "float32 comparison CSmith program: failed")

end Test.Exec
