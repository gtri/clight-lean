import CLightLean.Exec.Run
import CLightLean.Exec.RunSound

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def runIntTy : type := type_int32s

def runGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

/-- A no-argument internal function whose body returns 42.  Starting in the
`Callstate` exercises internal entry, body return execution, and the final
return-state recognizer. -/
def runReturningFunction : function :=
  { fn_return := runIntTy
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sreturn (some (.Econst_int (CompCert.Int.repr 42) runIntTy)) }

def runInitialState : state :=
  .Callstate (.Internal runReturningFunction) [] .Kstop Memory.empty

def runBodyState : state :=
  .State runReturningFunction runReturningFunction.fn_body .Kstop empty_env ∅ Memory.empty

def runFinalState : state :=
  .Returnstate (.Vint (CompCert.Int.repr 42)) .Kstop Memory.empty

def runVoidSignature : signature :=
  { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }

def runUnsupportedExternal : external_function :=
  .EF_external "puts" runVoidSignature

/-- The exact two-transition internal path completes with two fuel units.  The
returned trace is `E0` and the executor runtime is unchanged because this
subset has no external or builtin semantics. -/
def runFromFuelCompletesInternalReturnPath : Bool :=
  match runFromFuel runGenv 2 Runtime.empty runInitialState with
  | .completed runtime trace exit steps =>
      runtime.stdout == ByteArray.empty && trace.isEmpty &&
        exit == CompCert.Int.repr 42 && steps == 2
  | _ => false

theorem run_from_fuel_completes_internal_return_path :
    runFromFuelCompletesInternalReturnPath = true := by
  native_decide

/-- `runFuel` is precisely the fresh-runtime wrapper for `runFromFuel`. -/
def runFuelUsesEmptyRuntime : Bool :=
  match runFuel runGenv 2 runInitialState with
  | .completed runtime trace exit steps =>
      runtime.stdout == ByteArray.empty && trace.isEmpty &&
        exit == CompCert.Int.repr 42 && steps == 2
  | _ => false

theorem run_fuel_uses_empty_runtime : runFuelUsesEmptyRuntime = true := by
  native_decide

/-- A nonfinal initial state receives no transition at zero fuel. -/
theorem run_zero_fuel_exhausts_before_internal_entry :
    runFromFuel runGenv 0 Runtime.empty runInitialState =
      .fuelExhausted Runtime.empty Events.E0 runInitialState 0 := by
  rfl

/-- Final-state recognition precedes the fuel check, so a pre-existing final
state completes even with zero fuel. -/
theorem run_zero_fuel_recognizes_existing_final_state :
    runFromFuel runGenv 0 Runtime.empty runFinalState =
      .completed Runtime.empty Events.E0 (CompCert.Int.repr 42) 0 := by
  rfl

/-- After one successful internal-entry transition, the runner reports the
current body state and the one consumed step when no fuel remains. -/
theorem run_fuel_exhaustion_retains_midrun_state :
    runFromFuel runGenv 1 Runtime.empty runInitialState =
      .fuelExhausted Runtime.empty Events.E0 runBodyState 1 := by
  rfl

/-- Builtins are intentionally outside `stepInternal`; the runner preserves
the dispatcher's unsupported classification rather than calling them. -/
theorem run_builtin_is_unsupported :
    runFromFuel runGenv 1 Runtime.empty
        (.State runReturningFunction (.Sbuiltin none runUnsupportedExternal [] []) .Kstop
          empty_env ∅ Memory.empty) =
      .unsupported Runtime.empty Events.E0 (.unsupportedExternal "builtin") 0 := by
  rfl

/-- External call states are likewise classified as unsupported by the
internal-only runner. -/
theorem run_external_callstate_is_unsupported :
    runFromFuel runGenv 1 Runtime.empty
        (.Callstate (.External runUnsupportedExternal [] runIntTy cc_default) [] .Kstop
          Memory.empty) =
      .unsupported Runtime.empty Events.E0 (.unsupportedExternal "external-call") 0 := by
  rfl

/-- Non-unsupported dispatcher failures retain the exact error and map to
`stuck`; this malformed final-shaped state cannot be recognized as final. -/
theorem run_noninteger_stop_return_is_stuck :
    runFromFuel runGenv 1 Runtime.empty (.Returnstate .Vundef .Kstop Memory.empty) =
      .stuck Runtime.empty Events.E0 .stuck 0 := by
  rfl

/-- The recognizer's executable result agrees with the authoritative final
state relation in both directions. -/
theorem final_return_recognizer_is_authoritative :
    finalReturn? runFinalState = some (CompCert.Int.repr 42) ∧
    final_state runFinalState (CompCert.Int.repr 42) := by
  constructor
  · rfl
  · exact finalReturn?_sound rfl

end Test.Exec
