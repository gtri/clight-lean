import CLightLean.Exec.State

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def stateTestGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def stateId1 : ident := (101 : Nat)
def stateId2 : ident := (102 : Nat)
def stateId3 : ident := (103 : Nat)

def stateIntTy : type := type_int32s

def scalarAssignmentSuccess : Bool :=
  match assignLoc empty_composite_env type_int32s (Memory.alloc Memory.empty 0 4).2
      1 Ptrofs.zero .Full (.Vint (CompCert.Int.repr 37)) with
  | .ok _ => true
  | .error _ => false

def scalarAssignmentFailure : Bool :=
  match assignLoc empty_composite_env type_int32s Memory.empty
      99 Ptrofs.zero .Full (.Vint (CompCert.Int.repr 37)) with
  | .ok _ => false
  | .error .memoryFailure => true
  | .error _ => false

theorem assign_loc_scalar_constructed_memory_success : scalarAssignmentSuccess = true := by
  native_decide

theorem assign_loc_scalar_constructed_memory_failure : scalarAssignmentFailure = true := by
  native_decide

theorem bind_parameter_temps_success :
    bindParameterTemps [(stateId1, stateIntTy)] [.Vint (CompCert.Int.repr 9)]
        (createUndefTemps [(stateId3, stateIntTy)])
      = .ok ((createUndefTemps [(stateId3, stateIntTy)]).insert stateId1 (.Vint (CompCert.Int.repr 9))) := by
  rfl

theorem bind_parameter_temps_mismatched_arity :
    bindParameterTemps [(stateId1, stateIntTy)] [] (createUndefTemps [])
      = .error .malformedCall := by
  rfl

theorem undefined_temp_initialization :
    (createUndefTemps [(stateId1, stateIntTy), (stateId2, stateIntTy)]).get? stateId1
      = some .Vundef ∧
    (createUndefTemps [(stateId1, stateIntTy), (stateId2, stateIntTy)]).get? stateId2
      = some .Vundef := by
  simp only [createUndefTemps, create_undef_temps]
  constructor
  · rw [Std.HashMap.get?_insert]
    decide
  · rw [Std.HashMap.get?_insert]
    simp

theorem local_variable_allocation :
    ∀ e : env, ∀ m : Memory.mem,
      allocVariables stateTestGenv e m [(stateId1, stateIntTy)] =
        .ok { env := e.insert stateId1 (m.nextblock, stateIntTy)
              memory := (Memory.alloc m 0 (sizeof stateTestGenv.genv_cenv stateIntTy)).2 } := by
  intro e m
  rfl

def entryFunction : function :=
  { fn_return := stateIntTy
    fn_callconv := cc_default
    fn_params := [(stateId1, stateIntTy)]
    fn_vars := [(stateId2, stateIntTy)]
    fn_temps := [(stateId3, stateIntTy)]
    fn_body := .Sskip }

theorem function_entry2_success :
    ∀ m : Memory.mem,
      functionEntry2 stateTestGenv entryFunction [.Vint (CompCert.Int.repr 12)] m =
        .ok
          { env := empty_env.insert stateId2 (m.nextblock, stateIntTy)
            temps := (createUndefTemps [(stateId3, stateIntTy)]).insert stateId1
              (.Vint (CompCert.Int.repr 12))
            memory := (Memory.alloc m 0 (sizeof stateTestGenv.genv_cenv stateIntTy)).2 } := by
  intro m
  rfl

theorem function_entry2_mismatched_arity :
    ∀ m : Memory.mem,
      functionEntry2 stateTestGenv entryFunction [] m = .error .malformedCall := by
  intro m
  rfl

end Test.Exec
