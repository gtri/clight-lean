import CLightLean.Exec.Control

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def controlLabel : label := (501 : Nat)
def missingControlLabel : label := (502 : Nat)

def controlFunction : function :=
  { fn_return := type_int32s
    fn_callconv := cc_default
    fn_params := []
    fn_vars := []
    fn_temps := []
    fn_body := .Ssequence (.Slabel controlLabel .Scontinue) .Sbreak }

def controlSequenceTail : statement := .Sreturn none
def controlLoopFirst : statement := .Scontinue
def controlLoopSecond : statement := .Sbreak

theorem control_sequence_entry :
    stepControl (.State controlFunction (.Ssequence .Sskip controlSequenceTail) .Kstop
      empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Sskip (.Kseq controlSequenceTail .Kstop)
        empty_env ∅ Memory.empty) := by
  rfl

theorem control_skip_through_sequence :
    stepControl (.State controlFunction .Sskip (.Kseq controlSequenceTail .Kstop)
      empty_env ∅ Memory.empty) =
      .ok (.State controlFunction controlSequenceTail .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_continue_through_sequence :
    stepControl (.State controlFunction .Scontinue (.Kseq controlSequenceTail .Kstop)
      empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Scontinue .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_break_through_sequence :
    stepControl (.State controlFunction .Sbreak (.Kseq controlSequenceTail .Kstop)
      empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Sbreak .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_label_stripping :
    stepControl (.State controlFunction (.Slabel controlLabel .Scontinue) .Kstop
      empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Scontinue .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_goto_uses_function_body_and_call_cont :
    stepControl (.State controlFunction (.Sgoto controlLabel)
      (.Kseq controlSequenceTail .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Scontinue (.Kseq .Sbreak .Kstop)
        empty_env ∅ Memory.empty) := by
  rfl

theorem control_goto_missing_label_fails :
    stepControl (.State controlFunction (.Sgoto missingControlLabel) .Kstop
      empty_env ∅ Memory.empty) = .error .stuck := by
  rfl

theorem control_skip_through_switch :
    stepControl (.State controlFunction .Sskip (.Kswitch .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Sskip .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_break_through_switch :
    stepControl (.State controlFunction .Sbreak (.Kswitch .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Sskip .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_continue_through_switch :
    stepControl (.State controlFunction .Scontinue (.Kswitch .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Scontinue .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_loop_entry :
    stepControl (.State controlFunction (.Sloop controlLoopFirst controlLoopSecond) .Kstop
      empty_env ∅ Memory.empty) =
      .ok (.State controlFunction controlLoopFirst
        (.Kloop1 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) := by
  rfl

theorem control_skip_through_loop1 :
    stepControl (.State controlFunction .Sskip
      (.Kloop1 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction controlLoopSecond
        (.Kloop2 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) := by
  rfl

theorem control_continue_through_loop1 :
    stepControl (.State controlFunction .Scontinue
      (.Kloop1 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction controlLoopSecond
        (.Kloop2 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) := by
  rfl

theorem control_break_through_loop1 :
    stepControl (.State controlFunction .Sbreak
      (.Kloop1 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Sskip .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_skip_through_loop2 :
    stepControl (.State controlFunction .Sskip
      (.Kloop2 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction (.Sloop controlLoopFirst controlLoopSecond) .Kstop
        empty_env ∅ Memory.empty) := by
  rfl

theorem control_break_through_loop2 :
    stepControl (.State controlFunction .Sbreak
      (.Kloop2 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) =
      .ok (.State controlFunction .Sskip .Kstop empty_env ∅ Memory.empty) := by
  rfl

theorem control_mismatched_loop2_continue_fails :
    stepControl (.State controlFunction .Scontinue
      (.Kloop2 controlLoopFirst controlLoopSecond .Kstop) empty_env ∅ Memory.empty) =
      .error .stuck := by
  rfl

end Test.Exec
