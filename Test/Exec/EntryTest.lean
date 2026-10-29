import CLightLean.Exec.Entry

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def entryTransitionGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def entryTransitionParam : ident := (301 : Nat)
def entryTransitionLocal : ident := (302 : Nat)
def entryTransitionTemp : ident := (303 : Nat)
def entryTransitionIntTy : type := type_int32s

/-- A minimal `step2`-convention function with one parameter, local, and
temporary. -/
def entryTransitionFunction : function :=
  { fn_return := entryTransitionIntTy
    fn_callconv := cc_default
    fn_params := [(entryTransitionParam, entryTransitionIntTy)]
    fn_vars := [(entryTransitionLocal, entryTransitionIntTy)]
    fn_temps := [(entryTransitionTemp, entryTransitionIntTy)]
    fn_body := .Sskip }

theorem internal_entry_success :
    ∀ m : Memory.mem,
      enterInternalFunction entryTransitionGenv entryTransitionFunction
          [.Vint (CompCert.Int.repr 17)] .Kstop m =
        .ok
          (.State entryTransitionFunction entryTransitionFunction.fn_body .Kstop
            (empty_env.insert entryTransitionLocal (m.nextblock, entryTransitionIntTy))
            ((createUndefTemps [(entryTransitionTemp, entryTransitionIntTy)]).insert
              entryTransitionParam (.Vint (CompCert.Int.repr 17)))
            (Memory.alloc m 0
              (sizeof entryTransitionGenv.genv_cenv entryTransitionIntTy)).2) := by
  intro m
  rfl

theorem internal_entry_mismatched_arity_propagates_malformed_call :
    ∀ m : Memory.mem,
      enterInternalFunction entryTransitionGenv entryTransitionFunction [] .Kstop m =
        .error .malformedCall := by
  intro m
  rfl

end Test.Exec
