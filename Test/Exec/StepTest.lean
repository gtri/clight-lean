import CLightLean.Exec.Step

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def stepIntTy : type := type_int32s
def stepSetId : ident := (801 : Nat)
def stepResultId : ident := (802 : Nat)
def stepCalleeId : ident := (803 : Nat)
def stepParamId : ident := (804 : Nat)

def stepCallee : function :=
  { fn_return := stepIntTy
    fn_callconv := cc_default
    fn_params := [(stepParamId, stepIntTy)]
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def stepGenv : genv :=
  { genv_genv := Genv.add_global (Genv.empty_genv [])
      (stepCalleeId, .Gfun (.Internal stepCallee))
    genv_cenv := empty_composite_env }

def stepCaller : function :=
  { fn_return := stepIntTy
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

def stepOne : expr := .Econst_int (CompCert.Int.repr 1) stepIntTy
def stepZero : expr := .Econst_int CompCert.Int.zero stepIntTy
def stepFunctionTy : type := .Tfunction [stepIntTy] stepIntTy cc_default
def stepFunctionPtrTy : type := .Tpointer stepFunctionTy noattr
def stepCalleeExpr : expr :=
  .Eaddrof (.Evar stepCalleeId stepFunctionTy) stepFunctionPtrTy

/-- Assignment reaches the existing assignment helper through the dispatcher,
rather than duplicating its store semantics here. -/
def stepInternalAssignmentWrites : Bool :=
  let allocated := Memory.alloc Memory.empty 0 4
  let target : expr := .Ederef (.Etempvar stepSetId (.Tpointer stepIntTy noattr)) stepIntTy
  match stepInternal stepGenv
      (.State stepCaller (.Sassign target (.Econst_int (CompCert.Int.repr 37) stepIntTy)) .Kstop
        empty_env ((∅ : temp_env).insert stepSetId (.Vptr allocated.1 Ptrofs.zero)) allocated.2) with
  | .ok (.State _ .Sskip .Kstop _ _ m') =>
      Memory.loadv .Mint32 m' (.Vptr allocated.1 Ptrofs.zero) = some (.Vint (CompCert.Int.repr 37))
  | _ => false

theorem step_internal_assignment_path : stepInternalAssignmentWrites = true := by
  native_decide

/-- The dispatcher selects `stepControl` for a sequence, then its `Kseq`
continuation rule on the following state. -/
theorem step_internal_sequence_control_path :
    stepInternal stepGenv
        (.State stepCaller (.Ssequence .Sskip (.Sset stepSetId stepOne)) .Kstop
          empty_env ∅ Memory.empty) =
      .ok (.State stepCaller .Sskip (.Kseq (.Sset stepSetId stepOne) .Kstop)
        empty_env ∅ Memory.empty) ∧
    stepInternal stepGenv
        (.State stepCaller .Sskip (.Kseq (.Sset stepSetId stepOne) .Kstop)
          empty_env ∅ Memory.empty) =
      .ok (.State stepCaller (.Sset stepSetId stepOne) .Kstop empty_env ∅ Memory.empty) := by
  exact ⟨rfl, rfl⟩

/-- The dispatcher integrates `stepSet` and `stepIf` without selecting an
arbitrary branch. -/
theorem step_internal_set_if_path :
    stepInternal stepGenv (.State stepCaller (.Sset stepSetId stepOne) .Kstop
      empty_env ∅ Memory.empty) =
      .ok (.State stepCaller .Sskip .Kstop empty_env
        ((∅ : temp_env).insert stepSetId (.Vint (CompCert.Int.repr 1))) Memory.empty) ∧
    stepInternal stepGenv (.State stepCaller (.Sifthenelse stepZero .Sbreak .Scontinue) .Kstop
      empty_env ∅ Memory.empty) =
      .ok (.State stepCaller .Scontinue .Kstop empty_env ∅ Memory.empty) := by
  exact ⟨rfl, rfl⟩

/-- Switch selection is delegated to `stepSwitch` and retains its `Kswitch`
continuation. -/
theorem step_internal_switch_path :
    stepInternal stepGenv (.State stepCaller (.Sswitch stepOne .LSnil) .Kstop
      empty_env ∅ Memory.empty) =
      .ok (.State stepCaller .Sskip (.Kswitch .Kstop) empty_env ∅ Memory.empty) := by
  rfl

/-- An internal `Callstate` enters through the existing entry helper. -/
theorem step_internal_direct_internal_callstate_entry :
    stepInternal stepGenv
        (.Callstate (.Internal stepCallee) [.Vint (CompCert.Int.repr 9)] .Kstop Memory.empty) =
      .ok (.State stepCallee .Sskip .Kstop empty_env
        ((∅ : temp_env).insert stepParamId (.Vint (CompCert.Int.repr 9))) Memory.empty) := by
  rfl

/-- An ordinary call first becomes a call state, then the same dispatcher
enters the resolved internal function. -/
def scallThenInternalEntry : Bool :=
  match stepInternal stepGenv
      (.State stepCaller (.Scall (some stepResultId) stepCalleeExpr [stepOne]) .Kstop
        empty_env ∅ Memory.empty) with
  | .ok (.Callstate (.Internal callee) [.Vint arg]
      (.Kcall (some resultId) caller callerEnv callerTemps .Kstop) m) =>
      arg == CompCert.Int.repr 1 && resultId == stepResultId &&
        match stepInternal stepGenv
            (.Callstate (.Internal callee) [.Vint arg]
              (.Kcall (some resultId) caller callerEnv callerTemps .Kstop) m) with
        | .ok (.State _ .Sskip
            (.Kcall (some enteredResultId) _ _ _ .Kstop)
            _ localTemps _) =>
            match localTemps.get? stepParamId with
            | some (.Vint boundArg) =>
                enteredResultId == stepResultId && boundArg == CompCert.Int.repr 1
            | _ => false
        | _ => false
  | _ => false

theorem step_internal_scall_then_internal_entry : scallThenInternalEntry = true := by
  native_decide

/-- Returned values resume a `Kcall` continuation through `resumeReturn`. -/
theorem step_internal_returnstate_kcall_resumption :
    stepInternal stepGenv
        (.Returnstate (.Vint (CompCert.Int.repr 12))
          (.Kcall (some stepResultId) stepCaller empty_env ∅ .Kstop) Memory.empty) =
      .ok (.State stepCaller .Sskip .Kstop empty_env
        ((∅ : temp_env).insert stepResultId (.Vint (CompCert.Int.repr 12))) Memory.empty) := by
  rfl

/-- `Sskip` at `Kstop` exits through `stepSkipCall`, rather than the generic
control helper. -/
def skipKstopCallExit : Bool :=
  match stepInternal stepGenv (.State stepCaller .Sskip .Kstop empty_env ∅ Memory.empty) with
  | .ok (.Returnstate .Vundef .Kstop _) => true
  | _ => false

theorem step_internal_skip_kstop_call_exit : skipKstopCallExit = true := by
  native_decide

/-- A body-level void return reaches the existing return helper and produces
its `Returnstate`; no caller resumption or external behavior is involved. -/
def voidReturnDispatches : Bool :=
  match stepInternal stepGenv
      (.State stepCaller (.Sreturn none) .Kstop empty_env ∅ Memory.empty) with
  | .ok (.Returnstate .Vundef .Kstop _) => true
  | _ => false

theorem step_internal_void_return_path : voidReturnDispatches = true := by
  native_decide

/-- A final Clight state is deliberately not fabricated into a transition. -/
theorem step_internal_final_returnstate_is_stuck :
    stepInternal stepGenv
        (.Returnstate (.Vint (CompCert.Int.repr 0)) .Kstop Memory.empty) = .error .stuck := by
  rfl

/-- Builtin statements and all external call states stay outside this
internal-only milestone. -/
def stepVoidSignature : signature :=
  { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }

def stepUnsupportedExternal : external_function :=
  .EF_external "puts" stepVoidSignature

theorem step_internal_builtin_and_external_are_unsupported :
    stepInternal stepGenv
        (.State stepCaller (.Sbuiltin none stepUnsupportedExternal [] []) .Kstop empty_env ∅ Memory.empty) =
      .error (.unsupportedExternal "builtin") ∧
    stepInternal stepGenv
        (.Callstate (.External stepUnsupportedExternal [] stepIntTy cc_default)
          [] .Kstop Memory.empty) =
      .error (.unsupportedExternal "external-call") := by
  exact ⟨rfl, rfl⟩

end Test.Exec
