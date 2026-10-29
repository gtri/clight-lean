import CLightLean.Exec.CSmithIO
import Test.CSmithSeeds.MinimalChecksumProgram

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def csmithIOBytes (values : List UInt8) : ByteArray :=
  values.foldl ByteArray.push ByteArray.empty

/-- Envelope serialization keeps non-UTF-8 modeled stdout in the byte-exact
hex field rather than decoding it as host text. This is evaluated directly,
rather than asking the kernel to normalize string formatting. -/
def renderCompletedEnvelopeEncodesNonUtf8Stdout : Bool :=
    renderCSmithResultEnvelope
      (.completed
        (Runtime.appendStdout Runtime.empty (csmithIOBytes [0x00, 0xff, 0x0a]))
        Events.E0 (CompCert.Int.repr 7) 12) =
      "CLIGHT_LEAN_RUNNER_V1 status=completed steps=12 exit=7 error_code=- stdout_hex=00FF0A"

/-- Error outcomes retain their classification while still encoding arbitrary
modeled stdout bytes without emitting them directly. -/
def renderUnsupportedEnvelopeIncludesErrorCode : Bool :=
    renderCSmithResultEnvelope
      (.unsupported
        (Runtime.appendStdout Runtime.empty (csmithIOBytes [0x80, 0xfe]))
        Events.E0 (.unsupportedExternal "puts") 3) =
      "CLIGHT_LEAN_RUNNER_V1 status=unsupported steps=3 exit=- error_code=unsupported_external stdout_hex=80FE"

def minimalChecksumExpectedStdout : ByteArray :=
  csmithIOBytes [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a]

-- Run the checked-in default fixture once through the unbounded IO loop. This
-- evaluates sequentially rather than reducing HashMap-heavy initialization and
-- memory operations in the proof kernel.
#eval do
  if !renderCompletedEnvelopeEncodesNonUtf8Stdout then
    throw (IO.userError "completed result envelope encoding failed")
  if !renderUnsupportedEnvelopeIncludesErrorCode then
    throw (IO.userError "error result envelope encoding failed")
  let result ← runCSmithProgramUntilTermination Test.CSmithSeeds.MinimalChecksumProgram.prog
  match result with
  | .ok (.completed runtime trace exit steps) =>
      if runtime.stdout == minimalChecksumExpectedStdout && trace.isEmpty &&
          exit == CompCert.Int.repr 0 && steps > 0 then
        IO.println "minimal CSmith IO program: pass"
      else
        throw (IO.userError "minimal CSmith IO program: completed with an unexpected result")
  | .ok result =>
      throw (IO.userError s!"minimal CSmith IO program: unexpected {result.statusCode}")
  | .error error =>
      throw (IO.userError s!"minimal CSmith IO program: initialization {error.code}")

end Test.Exec
