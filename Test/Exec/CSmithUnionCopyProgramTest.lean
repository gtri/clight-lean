import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.UnionCopyChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def unionCopyChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x41, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture copies a union through assignLoc's aggregate By_copy branch and
reads the same active `word` member from the destination. -/
def unionCopyChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.UnionCopyChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == unionCopyChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if unionCopyChecksumGeneratedProgramRuns then
    IO.println "union copy fixed checksum CSmith program: pass"
  else
    throw (IO.userError "union copy fixed checksum CSmith program: failed")

end Test.Exec
