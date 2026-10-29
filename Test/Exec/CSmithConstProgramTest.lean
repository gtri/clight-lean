import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.ConstChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def constChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes and reads a const-qualified global, exercising the
same global allocation and scalar load path while preserving its readonly
declaration in the generated Clight program. -/
def constChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.ConstChecksumProgram.prog 32 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == constChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if constChecksumGeneratedProgramRuns then
    IO.println "const fixed checksum CSmith program: pass"
  else
    throw (IO.userError "const fixed checksum CSmith program: failed")

end Test.Exec
