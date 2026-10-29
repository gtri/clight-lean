import CLightLean.Exec.Basic

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def basicIntTy : type := type_int32s
def basicTempId : ident := (601 : Nat)

def basicGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def basicFunction : function :=
  { fn_return := basicIntTy
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def basicOne : expr := .Econst_int (CompCert.Int.repr 1) basicIntTy
def basicTwo : expr := .Econst_int (CompCert.Int.repr 2) basicIntTy
def basicZero : expr := .Econst_int CompCert.Int.zero basicIntTy

/-- Setting a temporary evaluates its scalar source and retains all other
execution-state fields. -/
theorem step_set_scalar_temp_success :
    stepSet basicGenv basicFunction basicTempId basicTwo .Kstop empty_env ∅ Memory.empty =
      .ok (.State basicFunction .Sskip .Kstop empty_env
        ((∅ : temp_env).insert basicTempId (.Vint (CompCert.Int.repr 2))) Memory.empty) := by
  rfl

/-- An assignment to an actual allocated block writes through `assignLoc` and
leaves an observable stored integer. -/
def basicAssignmentSuccess : Bool :=
  let allocated := Memory.alloc Memory.empty 0 4
  let target : expr := .Ederef (.Etempvar basicTempId (.Tpointer basicIntTy noattr)) basicIntTy
  let source : expr := .Econst_int (CompCert.Int.repr 37) basicIntTy
  match stepAssign basicGenv basicFunction target source .Kstop empty_env
      ((∅ : temp_env).insert basicTempId (.Vptr allocated.1 Ptrofs.zero)) allocated.2 with
  | .ok (.State _ .Sskip .Kstop _ _ m') =>
      Memory.loadv .Mint32 m' (.Vptr allocated.1 Ptrofs.zero) = some (.Vint (CompCert.Int.repr 37))
  | _ => false

theorem step_assign_allocated_memory_success : basicAssignmentSuccess = true := by
  native_decide

/-- A resolved but unallocated destination is rejected by the existing memory
assignment API; no successor state is constructed. -/
def basicAssignmentMemoryFailure : Bool :=
  let target : expr := .Ederef (.Etempvar basicTempId (.Tpointer basicIntTy noattr)) basicIntTy
  match stepAssign basicGenv basicFunction target basicOne .Kstop empty_env
      ((∅ : temp_env).insert basicTempId (.Vptr 99 Ptrofs.zero)) Memory.empty with
  | .error .memoryFailure => true
  | _ => false

theorem step_assign_invalid_memory_fails : basicAssignmentMemoryFailure = true := by
  native_decide

/-- A syntactically non-lvalue assignment destination propagates the lvalue
evaluator's explicit failure. -/
theorem step_assign_invalid_lvalue_fails :
    stepAssign basicGenv basicFunction basicOne basicTwo .Kstop empty_env ∅ Memory.empty =
      .error .invalidLvalue := by
  rfl

/-- A source that cannot be cast to the destination's scalar type is rejected
before any memory update. -/
def basicAssignmentCastFailure : Bool :=
  match stepAssign basicGenv basicFunction
      (.Ederef (.Etempvar basicTempId
        (.Tpointer (.Tpointer basicIntTy noattr) noattr)) (.Tpointer basicIntTy noattr))
      (.Econst_float CompCert.Float64.zero (.Tfloat .F64 noattr))
      .Kstop empty_env
      ((∅ : temp_env).insert basicTempId (.Vptr 99 Ptrofs.zero)) Memory.empty with
  | .error .invalidExpression => true
  | _ => false

theorem step_assign_failed_cast_fails : basicAssignmentCastFailure = true := by
  native_decide

theorem step_if_true_selects_first_branch :
    stepIf basicGenv basicFunction basicOne .Scontinue .Sbreak .Kstop empty_env ∅ Memory.empty =
      .ok (.State basicFunction .Scontinue .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem step_if_false_selects_second_branch :
    stepIf basicGenv basicFunction basicZero .Scontinue .Sbreak .Kstop empty_env ∅ Memory.empty =
      .ok (.State basicFunction .Sbreak .Kstop empty_env ∅ Memory.empty) := by
  rfl

def basicSwitchCases : labeled_statements :=
  .LScons (some 2) .Scontinue (.LScons none .Sbreak .LSnil)

theorem step_switch_case_selects_matching_suffix :
    stepSwitch basicGenv basicFunction basicTwo basicSwitchCases .Kstop empty_env ∅ Memory.empty =
      .ok (.State basicFunction
        (.Ssequence .Scontinue (.Ssequence .Sbreak .Sskip)) (.Kswitch .Kstop)
        empty_env ∅ Memory.empty) := by
  rfl

theorem step_switch_default_selects_default_suffix :
    stepSwitch basicGenv basicFunction basicOne basicSwitchCases .Kstop empty_env ∅ Memory.empty =
      .ok (.State basicFunction (.Ssequence .Sbreak .Sskip) (.Kswitch .Kstop)
        empty_env ∅ Memory.empty) := by
  rfl

/-- A condition whose value/type pair cannot be boolean is rejected rather than
choosing a branch. -/
theorem step_if_invalid_condition_fails :
    stepIf basicGenv basicFunction
        (.Econst_long (CompCert.Int64.repr 1) basicIntTy) .Sskip .Sbreak
        .Kstop empty_env ∅ Memory.empty = .error .invalidExpression := by
  rfl

/-- A selector whose value/type pair cannot be a switch argument is rejected
rather than selecting a case or default. -/
theorem step_switch_invalid_selector_fails :
    stepSwitch basicGenv basicFunction
        (.Econst_long (CompCert.Int64.repr 1) basicIntTy) basicSwitchCases
        .Kstop empty_env ∅ Memory.empty = .error .invalidExpression := by
  rfl

end Test.Exec
