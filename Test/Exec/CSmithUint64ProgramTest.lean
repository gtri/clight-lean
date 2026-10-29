import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.Uint64ChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def uint64ChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x39, 0x41, 0x42, 0x43, 0x44, 0x46, 0x30, 0x30, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes a 64-bit unsigned global, executes long multiply,
divide, and add, then explicitly narrows it to the fixed uint32 checksum ABI. -/
def uint64ChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.Uint64ChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == uint64ChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if uint64ChecksumGeneratedProgramRuns then
    IO.println "uint64 fixed checksum CSmith program: pass"
  else
    throw (IO.userError "uint64 fixed checksum CSmith program: failed")

end Test.Exec
