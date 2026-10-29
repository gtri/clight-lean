import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.Int8ChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def int8ChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x46, 0x46, 0x46, 0x46, 0x46, 0x46, 0x46, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes `int8_t value` to -2, stores -5 through a
Mint8signed location, then sign-extends the reloaded byte to int32 before its
conversion to the checksum helper's uint32 argument. -/
def int8ChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.Int8ChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == int8ChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if int8ChecksumGeneratedProgramRuns then
    IO.println "int8 fixed checksum CSmith program: pass"
  else
    throw (IO.userError "int8 fixed checksum CSmith program: failed")

end Test.Exec
