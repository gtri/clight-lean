import CLightLean.Exec.Call

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def callIdCallee : ident := (201 : Nat)
def callIdCaller : ident := (202 : Nat)
def callIdResult : ident := (203 : Nat)
def callIdParam : ident := (204 : Nat)
def callIdMissing : ident := (299 : Nat)

def callIntTy : type := type_int32s

def callFunctionTy : type := .Tfunction [callIntTy] callIntTy cc_default
def callFunctionPtrTy : type := .Tpointer callFunctionTy noattr

def callCallee : function :=
  { fn_return := callIntTy
    fn_callconv := cc_default
    fn_params := [(callIdParam, callIntTy)]
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def callCaller : function :=
  { fn_return := callIntTy
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def callGenv : genv :=
  { genv_genv := Genv.add_global (Genv.empty_genv [])
      (callIdCallee, .Gfun (.Internal callCallee))
    genv_cenv := empty_composite_env }

def callCalleeExpr : expr :=
  .Eaddrof (.Evar callIdCallee callFunctionTy) callFunctionPtrTy
def callArgument : expr := .Econst_int (CompCert.Int.repr 9) callIntTy

def internalCallSuccess : Bool :=
  match stepCall callGenv callCaller (some callIdResult) callCalleeExpr [callArgument]
      .Kstop empty_env ∅ Memory.empty with
  | .ok (.Callstate (.Internal _) [.Vint arg]
      (.Kcall (some result) _ _ _ .Kstop) _) =>
      arg == CompCert.Int.repr 9 && result == callIdResult
  | _ => false

theorem step_call_internal_success : internalCallSuccess = true := by
  native_decide

def nonFunctionCallFails : Bool :=
  match stepCall callGenv callCaller none (.Econst_int (CompCert.Int.repr 0) callIntTy) []
      .Kstop empty_env ∅ Memory.empty with
  | .error .invalidExpression => true
  | _ => false

theorem step_call_non_function_callee_fails : nonFunctionCallFails = true := by
  native_decide

def missingFunctionCallFails : Bool :=
  match stepCall callGenv callCaller none
      (.Etempvar callIdMissing callFunctionTy) [callArgument]
      .Kstop empty_env
      ((∅ : temp_env).insert callIdMissing (.Vptr 99 Ptrofs.zero)) Memory.empty with
  | .error .invalidExpression => true
  | _ => false

theorem step_call_missing_function_fails : missingFunctionCallFails = true := by
  native_decide

def signatureMismatchCallFails : Bool :=
  match stepCall callGenv callCaller none
      (.Eaddrof (.Evar callIdCallee (.Tfunction [] callIntTy cc_default))
        (.Tpointer (.Tfunction [] callIntTy cc_default) noattr)) []
      .Kstop empty_env ∅ Memory.empty with
  | .error .invalidExpression => true
  | _ => false

theorem step_call_signature_mismatch_fails : signatureMismatchCallFails = true := by
  native_decide

end Test.Exec
