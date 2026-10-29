import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.StructFieldChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def structFieldChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The fixture initializes a global two-field struct, resolves both field
locations through composite layout, updates one field, and reloads it. -/
def structFieldChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.StructFieldChecksumProgram.prog 64 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == structFieldChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if structFieldChecksumGeneratedProgramRuns then
    IO.println "struct field fixed checksum CSmith program: pass"
  else
    throw (IO.userError "struct field fixed checksum CSmith program: failed")

end Test.Exec
