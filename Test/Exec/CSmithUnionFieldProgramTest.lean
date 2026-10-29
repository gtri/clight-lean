import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.UnionFieldChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def unionFieldChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes and subsequently reads/writes only the union's
active `word` member. -/
def unionFieldChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.UnionFieldChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == unionFieldChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if unionFieldChecksumGeneratedProgramRuns then
    IO.println "union field fixed checksum CSmith program: pass"
  else
    throw (IO.userError "union field fixed checksum CSmith program: failed")

end Test.Exec
