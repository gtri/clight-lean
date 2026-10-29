import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.StructCopyChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def structCopyChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture copies an initialized global struct to a zero-initialized global
struct through assignLoc's aggregate By_copy branch, then reads both fields. -/
def structCopyChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.StructCopyChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == structCopyChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if structCopyChecksumGeneratedProgramRuns then
    IO.println "struct copy fixed checksum CSmith program: pass"
  else
    throw (IO.userError "struct copy fixed checksum CSmith program: failed")

end Test.Exec
