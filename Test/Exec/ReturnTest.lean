import CLightLean.Exec.Return

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def returnResumeResultId : ident := (401 : Nat)
def returnResumePreservedId : ident := (402 : Nat)

def returnResumeFunction : function :=
  { fn_return := type_int32s
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

/-- A call continuation with a result destination stores the returned value in
that caller temporary. -/
theorem resume_returnstate_some_destination :
    resumeReturn (.Vint (CompCert.Int.repr 23)) (some returnResumeResultId)
        returnResumeFunction empty_env
        ((∅ : temp_env).insert returnResumePreservedId (.Vint (CompCert.Int.repr 7)))
        .Kstop Memory.empty =
      .State returnResumeFunction .Sskip .Kstop empty_env
        (((∅ : temp_env).insert returnResumePreservedId (.Vint (CompCert.Int.repr 7))).insert
          returnResumeResultId (.Vint (CompCert.Int.repr 23)))
        Memory.empty := by
  rfl

/-- A call continuation without a result destination preserves the caller
temporary environment unchanged. -/
theorem resume_returnstate_no_destination :
    resumeReturn (.Vint (CompCert.Int.repr 29)) none returnResumeFunction empty_env
        ((∅ : temp_env).insert returnResumePreservedId (.Vint (CompCert.Int.repr 7)))
        .Kstop Memory.empty =
      .State returnResumeFunction .Sskip .Kstop empty_env
        ((∅ : temp_env).insert returnResumePreservedId (.Vint (CompCert.Int.repr 7)))
        Memory.empty := by
  rfl

end Test.Exec
