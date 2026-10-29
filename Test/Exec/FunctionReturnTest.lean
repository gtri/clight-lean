import CLightLean.Exec.FunctionReturn

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def functionReturnLocalId : ident := (701 : Nat)
def functionReturnCallerId : ident := (702 : Nat)

def functionReturnIntTy : type := type_int32s
def functionReturnByteTy : type := .Tint .I8 .Unsigned noattr

def functionReturnGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def functionReturnFunction : function :=
  { fn_return := functionReturnIntTy
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def functionReturnByteFunction : function :=
  { fn_return := functionReturnByteTy
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def functionReturnPointerFunction : function :=
  { fn_return := .Tpointer functionReturnIntTy noattr
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

/-- Void return frees the sole local block and strips administrative
continuations through `call_cont`. -/
def voidReturnFreesLocal : Bool :=
  let allocated := Memory.alloc Memory.empty 0 4
  let locals := empty_env.insert functionReturnLocalId (allocated.1, functionReturnIntTy)
  match stepReturnVoid functionReturnGenv functionReturnFunction
      (.Kseq .Sskip .Kstop) locals ∅ allocated.2 with
  | .ok (.Returnstate .Vundef .Kstop m') =>
      match Memory.free m' allocated.1 0 4 with
      | none => true
      | some _ => false
  | _ => false

theorem void_return_frees_local_and_uses_call_cont : voidReturnFreesLocal = true := by
  native_decide

/-- A valued return evaluates its expression, casts it to the function return
type, and frees the local block. -/
def valuedReturnCastsAndFreesLocal : Bool :=
  let allocated := Memory.alloc Memory.empty 0 4
  let locals := empty_env.insert functionReturnLocalId (allocated.1, functionReturnIntTy)
  let value := .Econst_int (CompCert.Int.repr 300) functionReturnIntTy
  match stepReturnValue functionReturnGenv functionReturnByteFunction value
      (.Kswitch .Kstop) locals ∅ allocated.2 with
  | .ok (.Returnstate (.Vint result) .Kstop m') =>
      result == CompCert.Int.repr 44 &&
        match Memory.free m' allocated.1 0 4 with
        | none => true
        | some _ => false
  | _ => false

theorem valued_return_casts_and_frees_local : valuedReturnCastsAndFreesLocal = true := by
  native_decide

/-- `Sskip` at a `Kcall` continuation frees the callee local block and returns
to that exact call continuation. -/
def skipCallFreesLocal : Bool :=
  let allocated := Memory.alloc Memory.empty 0 4
  let locals := empty_env.insert functionReturnLocalId (allocated.1, functionReturnIntTy)
  let k : cont := .Kcall (some functionReturnCallerId) functionReturnFunction empty_env ∅ .Kstop
  match stepSkipCall functionReturnGenv functionReturnFunction k locals ∅ allocated.2 with
  | .ok (.Returnstate .Vundef (.Kcall (some resultId) _ _ _ .Kstop) m') =>
      resultId == functionReturnCallerId &&
        match Memory.free m' allocated.1 0 4 with
        | none => true
        | some _ => false
  | _ => false

theorem skip_call_continuation_frees_local : skipCallFreesLocal = true := by
  native_decide

/-- A sequence continuation is not a call continuation and therefore has no
`step_skip_call` transition. -/
theorem skip_non_call_continuation_is_stuck :
    stepSkipCall functionReturnGenv functionReturnFunction (.Kseq .Sskip .Kstop)
      empty_env ∅ Memory.empty = .error .stuck := by
  rfl

/-- A failed cast to the function return type is an invalid expression and is
reported before attempting local-block deallocation. -/
theorem valued_return_failed_cast_is_invalid_expression :
    stepReturnValue functionReturnGenv functionReturnPointerFunction
      (.Econst_float CompCert.Float64.zero (.Tfloat .F64 noattr)) .Kstop
      empty_env ∅ Memory.empty = .error .invalidExpression := by
  rfl

/-- Local-block deallocation failure is classified as a memory failure rather
than producing a fabricated return state. -/
def voidReturnUnallocatedLocalFails : Bool :=
  match stepReturnVoid functionReturnGenv functionReturnFunction .Kstop
      (empty_env.insert functionReturnLocalId (99, functionReturnIntTy)) ∅ Memory.empty with
  | .error .memoryFailure => true
  | _ => false

theorem void_return_unallocated_local_is_memory_failure :
    voidReturnUnallocatedLocalFails = true := by
  native_decide

end Test.Exec
