/-
  The CompCert verified compiler
  Original Rocq/Coq implementation: Xavier Leroy, INRIA Paris-Rocquencourt
  Lean 4 translation: Georgia Tech Research Institute

  Copyright (c) 2005-2024 Institut National de Recherche en Informatique et en Automatique (INRIA)
  Copyright (c) 2026 Georgia Tech Research Institute

  Derivative work: Lean 4 translation and adaptation of CompCert's cfrontend semantics.

  This file is distributed under the terms of the GNU Lesser General Public License
  as published by the Free Software Foundation, either version 2.1 of the License,
  or (at your option) any later version.

  SPDX-License-Identifier: LGPL-2.1-or-later
-/

import CLightLean.Exec.Control

/-!
Compositional soundness lemmas for the deterministic control-only executor
helper.  Each lemma exposes exactly one existing `step2` constructor; together
they are deliberately not a theorem for a future general dispatcher.
-/

namespace CLightLean.Exec

variable [Archi]

theorem stepControl_sequence_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f (.Ssequence s1 s2) k e le m) = Except.ok s') :
    step2 ge (.State f (.Ssequence s1 s2) k e le m) Events.E0 s' := by
  change Except.ok (.State f s1 (.Kseq s2 k) e le m) = Except.ok s' at h
  cases h
  exact .step_seq f s1 s2 k e le m

theorem stepControl_skip_seq_sound
    (ge : genv) (f : function) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sskip (.Kseq s k) e le m) = Except.ok s') :
    step2 ge (.State f .Sskip (.Kseq s k) e le m) Events.E0 s' := by
  change Except.ok (.State f s k e le m) = Except.ok s' at h
  cases h
  exact .step_skip_seq f s k e le m

theorem stepControl_continue_seq_sound
    (ge : genv) (f : function) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Scontinue (.Kseq s k) e le m) = Except.ok s') :
    step2 ge (.State f .Scontinue (.Kseq s k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Scontinue k e le m) = Except.ok s' at h
  cases h
  exact .step_continue_seq f s k e le m

theorem stepControl_break_seq_sound
    (ge : genv) (f : function) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sbreak (.Kseq s k) e le m) = Except.ok s') :
    step2 ge (.State f .Sbreak (.Kseq s k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Sbreak k e le m) = Except.ok s' at h
  cases h
  exact .step_break_seq f s k e le m

theorem stepControl_label_sound
    (ge : genv) (f : function) (lbl : label) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f (.Slabel lbl s) k e le m) = Except.ok s') :
    step2 ge (.State f (.Slabel lbl s) k e le m) Events.E0 s' := by
  change Except.ok (.State f s k e le m) = Except.ok s' at h
  cases h
  exact .step_label f lbl s k e le m

theorem stepControl_goto_sound
    (ge : genv) (f : function) (lbl : label) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f (.Sgoto lbl) k e le m) = Except.ok s') :
    step2 ge (.State f (.Sgoto lbl) k e le m) Events.E0 s' := by
  unfold stepControl at h
  cases hfind : find_label lbl f.fn_body (call_cont k) with
  | none =>
      simp [hfind] at h
  | some target =>
      obtain ⟨targetStatement, targetCont⟩ := target
      simp only [hfind, Except.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact .step_goto f lbl k e le m targetStatement targetCont hfind

theorem stepControl_skip_switch_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sskip (.Kswitch k) e le m) = Except.ok s') :
    step2 ge (.State f .Sskip (.Kswitch k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Sskip k e le m) = Except.ok s' at h
  cases h
  exact .step_skip_break_switch f .Sskip k e le m (Or.inl rfl)

theorem stepControl_break_switch_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sbreak (.Kswitch k) e le m) = Except.ok s') :
    step2 ge (.State f .Sbreak (.Kswitch k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Sskip k e le m) = Except.ok s' at h
  cases h
  exact .step_skip_break_switch f .Sbreak k e le m (Or.inr rfl)

theorem stepControl_continue_switch_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Scontinue (.Kswitch k) e le m) = Except.ok s') :
    step2 ge (.State f .Scontinue (.Kswitch k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Scontinue k e le m) = Except.ok s' at h
  cases h
  exact .step_continue_switch f k e le m

theorem stepControl_loop_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f (.Sloop s1 s2) k e le m) = Except.ok s') :
    step2 ge (.State f (.Sloop s1 s2) k e le m) Events.E0 s' := by
  change Except.ok (.State f s1 (.Kloop1 s1 s2 k) e le m) = Except.ok s' at h
  cases h
  exact .step_loop f s1 s2 k e le m

theorem stepControl_skip_loop1_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sskip (.Kloop1 s1 s2 k) e le m) = Except.ok s') :
    step2 ge (.State f .Sskip (.Kloop1 s1 s2 k) e le m) Events.E0 s' := by
  change Except.ok (.State f s2 (.Kloop2 s1 s2 k) e le m) = Except.ok s' at h
  cases h
  exact .step_skip_or_continue_loop1 f s1 s2 k e le m .Sskip (Or.inl rfl)

theorem stepControl_continue_loop1_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Scontinue (.Kloop1 s1 s2 k) e le m) = Except.ok s') :
    step2 ge (.State f .Scontinue (.Kloop1 s1 s2 k) e le m) Events.E0 s' := by
  change Except.ok (.State f s2 (.Kloop2 s1 s2 k) e le m) = Except.ok s' at h
  cases h
  exact .step_skip_or_continue_loop1 f s1 s2 k e le m .Scontinue (Or.inr rfl)

theorem stepControl_break_loop1_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sbreak (.Kloop1 s1 s2 k) e le m) = Except.ok s') :
    step2 ge (.State f .Sbreak (.Kloop1 s1 s2 k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Sskip k e le m) = Except.ok s' at h
  cases h
  exact .step_break_loop1 f s1 s2 k e le m

theorem stepControl_skip_loop2_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sskip (.Kloop2 s1 s2 k) e le m) = Except.ok s') :
    step2 ge (.State f .Sskip (.Kloop2 s1 s2 k) e le m) Events.E0 s' := by
  change Except.ok (.State f (.Sloop s1 s2) k e le m) = Except.ok s' at h
  cases h
  exact .step_skip_loop2 f s1 s2 k e le m

theorem stepControl_break_loop2_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepControl (.State f .Sbreak (.Kloop2 s1 s2 k) e le m) = Except.ok s') :
    step2 ge (.State f .Sbreak (.Kloop2 s1 s2 k) e le m) Events.E0 s' := by
  change Except.ok (.State f .Sskip k e le m) = Except.ok s' at h
  cases h
  exact .step_break_loop2 f s1 s2 k e le m

end CLightLean.Exec
