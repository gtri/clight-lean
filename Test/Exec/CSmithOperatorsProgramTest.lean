import CLightLean.Exec.CSmithRun
import Test.CSmithSeeds.OperatorsChecksumProgram

namespace Test.Exec

open CLightLean.Exec

def operatorsChecksumExpectedStdout : ByteArray :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x34, 0x0a].foldl
    ByteArray.push ByteArray.empty

/- The defined-C fixture uses sequenced compound assignment, comma sequencing,
embedded assignment, pre/post increment/decrement, and unary plus. The frontend
lowers these into ordinary Clight Sassign, Sset, Ebinop, Ecast, and Evar forms. -/
def operatorsChecksumGeneratedProgramRuns : Bool :=
    match runCSmithProgramFuel Test.CSmithSeeds.OperatorsChecksumProgram.prog 128 with
    | .ok (.completed runtime trace exit _) =>
        runtime.stdout == operatorsChecksumExpectedStdout &&
          trace.isEmpty && exit == CompCert.Int.repr 0
    | _ => false

#eval do
  if operatorsChecksumGeneratedProgramRuns then
    IO.println "normalized operators fixed checksum CSmith program: pass"
  else
    throw (IO.userError "normalized operators fixed checksum CSmith program: failed")

end Test.Exec
