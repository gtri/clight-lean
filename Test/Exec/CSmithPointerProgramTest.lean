import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.PointerChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def pointerChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture uses Init_addrof to initialize a global pointer, reloads that
pointer from memory, dereferences it for a read-modify-write, then dereferences
it again for the checksum argument. -/
def pointerChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.PointerChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == pointerChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if pointerChecksumGeneratedProgramRuns then
    IO.println "pointer fixed checksum CSmith program: pass"
  else
    throw (IO.userError "pointer fixed checksum CSmith program: failed")

end Test.Exec
