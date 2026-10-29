import CLightLean.Exec.CSmithStep

set_option maxRecDepth 4096

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def csmithStepGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def csmithStepCaller : function :=
  { fn_return := type_int32s
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def csmithStepResultId : ident := (1201 : Nat)

def csmithPrefixedRuntime : Runtime :=
  Runtime.appendStdout Runtime.empty (ByteArray.empty.push 0xff)

def csmithExternalCall (args : List val) (k : cont) (memory : Memory.mem) : state :=
  .Callstate
    (.External (.EF_external "csmith_checksum_print" csmithChecksumPrintSignature)
      csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
    args k memory

def csmithFabsExternalCall (args : List val) (k : cont) (memory : Memory.mem) : state :=
  .Callstate
    (.External (.EF_external "fabs" csmithFabsSignature)
      csmithFabsArgTypes csmithFabsResultType cc_default)
    args k memory

def csmithFabsfExternalCall (args : List val) (k : cont) (memory : Memory.mem) : state :=
  .Callstate
    (.External (.EF_external "fabsf" csmithFabsfSignature)
      csmithFabsfArgTypes csmithFabsfResultType cc_default)
    args k memory

/-- The fixed helper does not inspect or alter its modeled memory argument.
This direct test uses an abstract memory rather than reducing a HashMap-backed
allocation. -/
theorem csmith_checksum_external_updates_runtime_and_returns_silently
    (memory : Memory.mem) :
    stepCSmith csmithStepGenv Runtime.empty
        (csmithExternalCall [.Vint (CompCert.Int.repr 0x1A2B)] .Kstop memory) =
      .ok
        { runtime := Runtime.appendStdout Runtime.empty (csmithChecksumOutput 0x1A2B)
          trace := Events.E0
          state := .Returnstate (.Vint (CompCert.Int.repr 16)) .Kstop memory } := by
  rfl

/-- The external action appends rather than replaces existing modeled stdout. -/
theorem csmith_checksum_external_appends_existing_runtime (memory : Memory.mem) :
    stepCSmith csmithStepGenv csmithPrefixedRuntime
        (csmithExternalCall [.Vint (CompCert.Int.repr 0x1A2B)] .Kstop memory) =
      .ok
        { runtime := Runtime.appendStdout csmithPrefixedRuntime (csmithChecksumOutput 0x1A2B)
          trace := Events.E0
          state := .Returnstate (.Vint (CompCert.Int.repr 16)) .Kstop memory } := by
  rfl

/-- The fixed helper's single argument is not a format pointer: wrong arity is
reported as a malformed call. -/
theorem csmith_checksum_external_rejects_wrong_arity (memory : Memory.mem) :
    stepCSmith csmithStepGenv Runtime.empty
        (csmithExternalCall [] .Kstop memory) = .error .malformedCall := by
  rfl

/-- A one-element list has the admitted arity but must contain an integer. -/
theorem csmith_checksum_external_rejects_noninteger_argument (memory : Memory.mem) :
    stepCSmith csmithStepGenv Runtime.empty
        (csmithExternalCall [.Vundef] .Kstop memory) = .error .invalidExpression := by
  rfl

/-- CSmith's safe double wrapper receives a pure, silent `fabs` action. -/
theorem csmith_fabs_external_returns_absolute_value (memory : Memory.mem)
    (value : CompCert.Float64) :
    stepCSmith csmithStepGenv Runtime.empty
        (csmithFabsExternalCall [.Vfloat value] .Kstop memory) =
      .ok
        { runtime := Runtime.empty
          trace := Events.E0
          state := .Returnstate (.Vfloat (CompCert.Float64.abs value)) .Kstop memory } := by
  rfl

/-- CSmith's safe single wrapper receives a pure, silent `fabsf` action. -/
theorem csmith_fabsf_external_returns_absolute_value (memory : Memory.mem)
    (value : CompCert.Float32) :
    stepCSmith csmithStepGenv Runtime.empty
        (csmithFabsfExternalCall [.Vsingle value] .Kstop memory) =
      .ok
        { runtime := Runtime.empty
          trace := Events.E0
          state := .Returnstate (.Vsingle (CompCert.Float32.abs value)) .Kstop memory } := by
  rfl

/-- The external name is insufficient: changing the generated signature's
calling convention keeps the call unsupported. -/
theorem csmith_checksum_external_rejects_wrong_signature (memory : Memory.mem) :
    stepCSmith csmithStepGenv Runtime.empty
        (.Callstate
          (.External (.EF_external "csmith_checksum_print"
            { sig_args := [.Xint]
              sig_res := .Xint
              sig_cc := { cc_vararg := some 1, cc_unproto := false, cc_structret := false } })
            csmithChecksumPrintArgTypes csmithChecksumPrintResultType
            { cc_vararg := some 1, cc_unproto := false, cc_structret := false })
          [.Vint (CompCert.Int.repr 1)] .Kstop memory) =
      .error (.unsupportedExternal "external-call") := by
  rfl

/-- An unrecognized external preserves the pre-existing unsupported-external
classification from the internal-only dispatcher. -/
theorem csmith_step_rejects_other_external (memory : Memory.mem) :
    stepCSmith csmithStepGenv Runtime.empty
        (.Callstate
          (.External (.EF_external "puts" csmithChecksumPrintSignature)
            csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
          [.Vint (CompCert.Int.repr 1)] .Kstop memory) =
      .error (.unsupportedExternal "external-call") := by
  rfl

/-- Once the external call has formed a `Returnstate`, the next CSmith-aware
step delegates to the existing internal call-continuation resumption path. -/
theorem csmith_checksum_external_then_kcall_resumes (memory : Memory.mem) :
    match stepCSmith csmithStepGenv Runtime.empty
        (csmithExternalCall [.Vint (CompCert.Int.repr 0x1A2B)]
          (.Kcall (some csmithStepResultId) csmithStepCaller empty_env ∅ .Kstop) memory) with
    | .ok transition =>
        stepCSmith csmithStepGenv transition.runtime transition.state =
          .ok
            { runtime := Runtime.appendStdout Runtime.empty (csmithChecksumOutput 0x1A2B)
              trace := Events.E0
              state := .State csmithStepCaller .Sskip .Kstop empty_env
                ((∅ : temp_env).insert csmithStepResultId (.Vint (CompCert.Int.repr 16))) memory }
    | .error _ => False := by
  rfl

end Test.Exec
