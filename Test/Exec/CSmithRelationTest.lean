import CLightLean.Exec.CSmithRelation

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def csmithRelationGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def csmithRelationFunction : function :=
  { fn_return := type_int32s
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Sskip }

/-- The direct specialized rule gives the owned helper's exact silent return
transition, without making any claim about the stock external-call relation. -/
theorem csmith_checksum_external_has_specialized_transition
    (memory : Memory.mem) (checksum : CompCert.Int) :
    csmithStep2 csmithRelationGenv
      (.Callstate
        (.External (.EF_external "csmith_checksum_print" csmithChecksumPrintSignature)
          csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
        [.Vint checksum] .Kstop memory)
      Events.E0
      (.Returnstate
        (.Vint (CompCert.Int.repr ((csmithChecksumOutput checksum.unsigned).size : Int)))
        .Kstop memory) := by
  exact .checksum_external checksum .Kstop memory

/-- A normal control source is not in the helper namespace, so the `base`
constructor imports its ordinary stock `step2` sequence transition. -/
theorem csmith_relation_base_accepts_ordinary_sequence (memory : Memory.mem) :
    csmithStep2 csmithRelationGenv
      (.State csmithRelationFunction (.Ssequence .Sskip .Sskip) .Kstop empty_env ∅ memory)
      Events.E0
      (.State csmithRelationFunction .Sskip (.Kseq .Sskip .Kstop) empty_env ∅ memory) := by
  apply csmithStep2.base
  · simp [isCSmithOwnedExternalState]
  · exact step.step_seq csmithRelationFunction .Sskip .Sskip .Kstop empty_env ∅ memory

/-- A hand-constructed program keeps the stock package's ordinary initial and
final-state fields.  Its transition field is intentionally the only changed
field. -/
def csmithRelationTinyProgram : program_type function :=
  make_program! function [] [((1 : Nat), .Gfun (.Internal csmithRelationFunction))]
    [(1 : Nat)] (1 : Nat)

theorem csmith_relation_package_has_stock_initial_and_final_shape
    (s : state) (result : CompCert.Int) :
    ((csmithSemantics2 csmithRelationTinyProgram).initial_state s ↔
      (semantics2 csmithRelationTinyProgram).initial_state s) ∧
    ((csmithSemantics2 csmithRelationTinyProgram).final_state s result ↔
      (semantics2 csmithRelationTinyProgram).final_state s result) := by
  constructor <;> rfl

end Test.Exec
