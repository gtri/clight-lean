import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.PointerCompareChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def pointerCompareChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x46, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture compares two valid pointers into the same array, pointers to
different array elements, a valid pointer against null, and null against null.
The defined comparisons contribute 1 + 2 + 4 + 8 = 15. -/
def pointerCompareChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.PointerCompareChecksumProgram.prog 128 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == pointerCompareChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if pointerCompareChecksumGeneratedProgramRuns then
    IO.println "pointer comparison fixed checksum CSmith program: pass"
  else
    throw (IO.userError "pointer comparison fixed checksum CSmith program: failed")

end Test.Exec
