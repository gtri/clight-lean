import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.MuldivChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def muldivChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x32, 0x34, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture executes defined unsigned division and multiplication:
`(84 / 7) * 3 = 36`. -/
def muldivChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.MuldivChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == muldivChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if muldivChecksumGeneratedProgramRuns then
    IO.println "muldiv fixed checksum CSmith program: pass"
  else
    throw (IO.userError "muldiv fixed checksum CSmith program: failed")

end Test.Exec
