import CLightLean.Exec.Program
import CLightLean.Exec.ProgramSound

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def programMainId : ident := (901 : Nat)
def programOtherId : ident := (902 : Nat)
def programParameterId : ident := (903 : Nat)

/-- A hand-authored, zero-argument `int main(void)` for exercising
whole-program initialization before generated Clight programs are introduced. -/
def constantMain : function :=
  { fn_return := type_int32s
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sreturn (some (.Econst_int (CompCert.Int.repr 42) type_int32s)) }

def constantMainProgram : program_type function :=
  make_program! function []
    [(programMainId, .Gfun (.Internal constantMain))]
    [programMainId] programMainId

/-- A program whose named main exists but has the wrong zero-argument entry
signature. -/
def malformedMain : function :=
  { fn_return := type_int32s
    fn_callconv := cc_default
    fn_params := [(programParameterId, type_int32s)]
    fn_vars := []
    fn_temps := []
    fn_body := .Sreturn (some (.Econst_int (CompCert.Int.repr 0) type_int32s)) }

def malformedMainProgram : program_type function :=
  make_program! function []
    [(programMainId, .Gfun (.Internal malformedMain))]
    [programMainId] programMainId

/-- The definition list has a function but does not define the declared main
identifier. -/
def missingMainProgram : program_type function :=
  make_program! function []
    [(programOtherId, .Gfun (.Internal constantMain))]
    [programOtherId] programMainId

/-- The constructor returns an internal, no-argument, stop-continuation call
state with the exact main signature accepted by authoritative initialization. -/
def initialStateHasExpectedShape : Bool :=
  match initialState constantMainProgram with
  | .ok (.Callstate (.Internal fd) [] .Kstop _) =>
      type_of_fundef (.Internal fd) == .Tfunction [] type_int32s cc_default
  | _ => false

theorem initial_state_has_expected_shape : initialStateHasExpectedShape = true := by
  native_decide

/-- A successful initial-state computation also has the authoritative
relational witness; this is deliberately a construction fact, not a
whole-program run theorem. -/
theorem initial_state_success_is_authoritative (state : state)
    (h : initialState constantMainProgram = .ok state) :
    initial_state constantMainProgram state := by
  exact initialState_sound constantMainProgram state h

/-- Entering the internal main and returning its constant takes exactly two
silent transitions in the current runner. -/
def programRunCompletes : Bool :=
  match runProgramFuel constantMainProgram 2 with
  | .ok (.completed runtime trace exit steps) =>
      runtime.stdout == ByteArray.empty && trace.isEmpty &&
        exit == CompCert.Int.repr 42 && steps == 2
  | _ => false

theorem program_run_completes_with_adequate_fuel : programRunCompletes = true := by
  native_decide

/-- An unsuitable declared main signature is rejected during initialization,
before a runner result is fabricated. -/
def malformedMainIsRejected : Bool :=
  match initialState malformedMainProgram with
  | .error .malformedCall => true
  | _ => false

theorem malformed_main_is_rejected : malformedMainIsRejected = true := by
  native_decide

/-- A missing declared main is likewise a malformed call setup, not a memory
failure or a synthesized state. -/
def missingMainIsRejected : Bool :=
  match initialState missingMainProgram with
  | .error .malformedCall => true
  | _ => false

theorem missing_main_is_rejected : missingMainIsRejected = true := by
  native_decide

/-- A valid but nonfinal initial call state is returned unchanged in the zero
fuel result, with no successful transition counted. -/
def programZeroFuelStopsBeforeEntry : Bool :=
  match runProgramFuel constantMainProgram 0 with
  | .ok (.fuelExhausted runtime trace (.Callstate (.Internal _) [] .Kstop _) steps) =>
      runtime.stdout == ByteArray.empty && trace.isEmpty && steps == 0
  | _ => false

theorem program_zero_fuel_stops_before_entry : programZeroFuelStopsBeforeEntry = true := by
  native_decide

end Test.Exec
