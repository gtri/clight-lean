import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.PointerCallChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def pointerCallChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture takes the address of a global, passes it as a Vptr argument to
an internal function, mutates through that argument, and returns the reloaded
value to the checksum helper. -/
def pointerCallChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.PointerCallChecksumProgram.prog 96 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == pointerCallChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if pointerCallChecksumGeneratedProgramRuns then
    IO.println "pointer call fixed checksum CSmith program: pass"
  else
    throw (IO.userError "pointer call fixed checksum CSmith program: failed")

end Test.Exec
