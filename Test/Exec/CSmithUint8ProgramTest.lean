import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.Uint8ChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def uint8ChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes `uint8_t value` to 254, stores the narrowing of
`254 + 3` back through a Mint8unsigned location, then zero-extends the reloaded
byte to the fixed-signature checksum helper. -/
def uint8ChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.Uint8ChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == uint8ChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if uint8ChecksumGeneratedProgramRuns then
    IO.println "uint8 fixed checksum CSmith program: pass"
  else
    throw (IO.userError "uint8 fixed checksum CSmith program: failed")

end Test.Exec
