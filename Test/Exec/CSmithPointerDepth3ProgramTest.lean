import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.PointerDepth3ChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def pointerDepth3ChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes three nested global pointer objects through
Init_addrof, reloads each pointer from memory, and performs a triple
dereference read-modify-write. -/
def pointerDepth3ChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.PointerDepth3ChecksumProgram.prog 96 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == pointerDepth3ChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if pointerDepth3ChecksumGeneratedProgramRuns then
    IO.println "pointer depth-three fixed checksum CSmith program: pass"
  else
    throw (IO.userError "pointer depth-three fixed checksum CSmith program: failed")

end Test.Exec
