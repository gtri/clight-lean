import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.Int64ChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def int64ChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x42, 0x39, 0x37, 0x35, 0x33, 0x30, 0x45, 0x45, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes a negative signed 64-bit global, executes signed
long multiplication/division, then narrows through uint32 for checksum output. -/
def int64ChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.Int64ChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == int64ChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if int64ChecksumGeneratedProgramRuns then
    IO.println "int64 fixed checksum CSmith program: pass"
  else
    throw (IO.userError "int64 fixed checksum CSmith program: failed")

end Test.Exec
