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

import CLightLean.Exec.BasicSound
import CLightLean.Exec.CallSound
import CLightLean.Exec.ControlSound
import CLightLean.Exec.EntrySound
import CLightLean.Exec.ExprSound
import CLightLean.Exec.FunctionReturnSound
import CLightLean.Exec.ReturnSound
import CLightLean.Exec.StateSound
import CLightLean.Exec.Step

/-!
Soundness facts for the internal-only dispatcher.  The main theorem at the
end of this file turns every successful dispatcher result into the matching
authoritative trace-free `step2` transition.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Dispatcher soundness for a deterministic control transition. -/
theorem stepInternal_sequence_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f (.Ssequence s1 s2) k e le m) = .ok s') :
    step2 ge (.State f (.Ssequence s1 s2) k e le m) Events.E0 s' := by
  exact stepControl_sequence_sound ge f s1 s2 k e le m s' h

/-- The remaining control-only dispatcher cases are direct re-exports of the
corresponding `stepControl` soundness facts. -/
theorem stepInternal_skip_seq_sound
    (ge : genv) (f : function) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sskip (.Kseq s k) e le m) = .ok s') :
    step2 ge (.State f .Sskip (.Kseq s k) e le m) Events.E0 s' := by
  exact stepControl_skip_seq_sound ge f s k e le m s' h

theorem stepInternal_continue_seq_sound
    (ge : genv) (f : function) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Scontinue (.Kseq s k) e le m) = .ok s') :
    step2 ge (.State f .Scontinue (.Kseq s k) e le m) Events.E0 s' := by
  exact stepControl_continue_seq_sound ge f s k e le m s' h

theorem stepInternal_break_seq_sound
    (ge : genv) (f : function) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sbreak (.Kseq s k) e le m) = .ok s') :
    step2 ge (.State f .Sbreak (.Kseq s k) e le m) Events.E0 s' := by
  exact stepControl_break_seq_sound ge f s k e le m s' h

theorem stepInternal_label_sound
    (ge : genv) (f : function) (lbl : label) (s : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f (.Slabel lbl s) k e le m) = .ok s') :
    step2 ge (.State f (.Slabel lbl s) k e le m) Events.E0 s' := by
  exact stepControl_label_sound ge f lbl s k e le m s' h

theorem stepInternal_goto_sound
    (ge : genv) (f : function) (lbl : label) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f (.Sgoto lbl) k e le m) = .ok s') :
    step2 ge (.State f (.Sgoto lbl) k e le m) Events.E0 s' := by
  exact stepControl_goto_sound ge f lbl k e le m s' h

theorem stepInternal_skip_switch_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sskip (.Kswitch k) e le m) = .ok s') :
    step2 ge (.State f .Sskip (.Kswitch k) e le m) Events.E0 s' := by
  exact stepControl_skip_switch_sound ge f k e le m s' h

theorem stepInternal_break_switch_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sbreak (.Kswitch k) e le m) = .ok s') :
    step2 ge (.State f .Sbreak (.Kswitch k) e le m) Events.E0 s' := by
  exact stepControl_break_switch_sound ge f k e le m s' h

theorem stepInternal_continue_switch_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Scontinue (.Kswitch k) e le m) = .ok s') :
    step2 ge (.State f .Scontinue (.Kswitch k) e le m) Events.E0 s' := by
  exact stepControl_continue_switch_sound ge f k e le m s' h

theorem stepInternal_loop_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f (.Sloop s1 s2) k e le m) = .ok s') :
    step2 ge (.State f (.Sloop s1 s2) k e le m) Events.E0 s' := by
  exact stepControl_loop_sound ge f s1 s2 k e le m s' h

theorem stepInternal_skip_loop1_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sskip (.Kloop1 s1 s2 k) e le m) = .ok s') :
    step2 ge (.State f .Sskip (.Kloop1 s1 s2 k) e le m) Events.E0 s' := by
  exact stepControl_skip_loop1_sound ge f s1 s2 k e le m s' h

theorem stepInternal_continue_loop1_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Scontinue (.Kloop1 s1 s2 k) e le m) = .ok s') :
    step2 ge (.State f .Scontinue (.Kloop1 s1 s2 k) e le m) Events.E0 s' := by
  exact stepControl_continue_loop1_sound ge f s1 s2 k e le m s' h

theorem stepInternal_break_loop1_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sbreak (.Kloop1 s1 s2 k) e le m) = .ok s') :
    step2 ge (.State f .Sbreak (.Kloop1 s1 s2 k) e le m) Events.E0 s' := by
  exact stepControl_break_loop1_sound ge f s1 s2 k e le m s' h

theorem stepInternal_skip_loop2_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sskip (.Kloop2 s1 s2 k) e le m) = .ok s') :
    step2 ge (.State f .Sskip (.Kloop2 s1 s2 k) e le m) Events.E0 s' := by
  exact stepControl_skip_loop2_sound ge f s1 s2 k e le m s' h

theorem stepInternal_break_loop2_sound
    (ge : genv) (f : function) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.State f .Sbreak (.Kloop2 s1 s2 k) e le m) = .ok s') :
    step2 ge (.State f .Sbreak (.Kloop2 s1 s2 k) e le m) Events.E0 s' := by
  exact stepControl_break_loop2_sound ge f s1 s2 k e le m s' h

/-- Dispatcher soundness for an assignment, with the lvalue, expression, cast,
and assignment premises required by the existing compositional theorem. -/
theorem stepInternal_assign_sound
    (ge : genv) (f : function) (a1 a2 : expr) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (loc : Lvalue) (v2 v : val)
    (m' : Memory.mem) (s' : state)
    (hloc : eval_lvalue ge e le m a1 loc.block loc.offset loc.bitfield)
    (hloc_exec : evalLvalue ge e le m a1 = .ok loc)
    (hvalue : eval_expr ge e le m a2 v2)
    (hvalue_exec : evalExpr ge e le m a2 = .ok v2)
    (hcast : sem_cast v2 (typeof a2) (typeof a1) m = some v)
    (hassign : assign_loc ge.genv_cenv (typeof a1) m loc.block loc.offset loc.bitfield v m')
    (hassign_exec : assignLoc ge.genv_cenv (typeof a1) m loc.block loc.offset loc.bitfield v = .ok m')
    (h : stepInternal ge (.State f (.Sassign a1 a2) k e le m) = .ok s') :
    step2 ge (.State f (.Sassign a1 a2) k e le m) Events.E0 s' := by
  exact stepAssign_sound ge f a1 a2 k e le m loc v2 v m' s' hloc hloc_exec hvalue hvalue_exec
    hcast hassign hassign_exec h

/-- Dispatcher soundness for a set transition, given the expression premise
needed by the existing `stepSet_sound` lemma. -/
theorem stepInternal_set_sound
    (ge : genv) (f : function) (id : ident) (a : expr) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (v : val) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (h : stepInternal ge (.State f (.Sset id a) k e le m) = .ok s') :
    step2 ge (.State f (.Sset id a) k e le m) Events.E0 s' := by
  exact stepSet_sound ge f id a k e le m v s' hvalue hvalue_exec h

/-- Dispatcher soundness for an `if` transition, given its expression and
boolean-interpretation premises. -/
theorem stepInternal_if_sound
    (ge : genv) (f : function) (a : expr) (s1 s2 : statement) (k : cont)
    (e : env) (le : temp_env) (m : Memory.mem) (v : val) (b : Bool) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (hbool : bool_val v (typeof a) m = some b)
    (h : stepInternal ge (.State f (.Sifthenelse a s1 s2) k e le m) = .ok s') :
    step2 ge (.State f (.Sifthenelse a s1 s2) k e le m) Events.E0 s' := by
  exact stepIf_sound ge f a s1 s2 k e le m v b s' hvalue hvalue_exec hbool h

/-- Dispatcher soundness for a switch transition, given the expression and
switch-argument premises required by the existing compositional theorem. -/
theorem stepInternal_switch_sound
    (ge : genv) (f : function) (a : expr) (sl : labeled_statements) (k : cont)
    (e : env) (le : temp_env) (m : Memory.mem) (v : val) (n : Nat) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (hswitch : sem_switch_arg v (typeof a) = some n)
    (h : stepInternal ge (.State f (.Sswitch a sl) k e le m) = .ok s') :
    step2 ge (.State f (.Sswitch a sl) k e le m) Events.E0 s' := by
  exact stepSwitch_sound ge f a sl k e le m v n s' hvalue hvalue_exec hswitch h

/-- Dispatcher soundness for an ordinary call, with the relational function
classification and expression-list premises required by `stepCall_sound`. -/
theorem stepInternal_call_sound
    (ge : genv) (f : function) (optid : Option ident) (a : expr) (al : List expr)
    (k : cont) (e : env) (le : temp_env) (m : Memory.mem)
    (tyargs : List type) (tyres : type) (cconv : calling_convention)
    (vf : val) (vargs : List val) (fd : fundef_type function)
    (hclass : classify_fun (typeof a) = .fun_case_f tyargs tyres cconv)
    (heval : eval_expr ge e le m a vf)
    (heval_exec : evalExpr ge e le m a = .ok vf)
    (hargs : eval_exprlist ge e le m al tyargs vargs)
    (hargs_exec : evalExprList ge e le m al tyargs = .ok vargs)
    (h : stepInternal ge (.State f (.Scall optid a al) k e le m) =
      .ok (.Callstate fd vargs (.Kcall optid f e le k) m)) :
    step2 ge (.State f (.Scall optid a al) k e le m) Events.E0
      (.Callstate fd vargs (.Kcall optid f e le k) m) := by
  exact stepCall_sound ge f optid a al k e le m tyargs tyres cconv vf vargs fd hclass heval
    heval_exec hargs hargs_exec h

/-- Dispatcher soundness for a void function return, with its required local
deallocation premise. -/
theorem stepInternal_return_void_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m m' : Memory.mem) (s' : state)
    (hfree : Memory.free_list m (blocks_of_env ge e) = some m')
    (h : stepInternal ge (.State f (.Sreturn none) k e le m) = .ok s') :
    step2 ge (.State f (.Sreturn none) k e le m) Events.E0 s' := by
  exact stepReturnVoid_sound ge f k e le m m' s' hfree h

/-- Dispatcher soundness for a valued function return, with its expression,
cast, and deallocation premises. -/
theorem stepInternal_return_value_sound
    (ge : genv) (f : function) (a : expr) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (v v' : val) (m' : Memory.mem) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (hcast : sem_cast v (typeof a) f.fn_return m = some v')
    (hfree : Memory.free_list m (blocks_of_env ge e) = some m')
    (h : stepInternal ge (.State f (.Sreturn (some a)) k e le m) = .ok s') :
    step2 ge (.State f (.Sreturn (some a)) k e le m) Events.E0 s' := by
  exact stepReturnValue_sound ge f a k e le m v v' m' s' hvalue hvalue_exec hcast hfree h

/-- Dispatcher soundness for an internal call-state entry, given the
authoritative function-entry premise. -/
theorem stepInternal_internal_entry_sound
    (ge : genv) (f : function) (args : List val) (k : cont) (m : Memory.mem)
    (entry : FunctionEntryState)
    (h : stepInternal ge (.Callstate (.Internal f) args k m) =
      .ok (.State f f.fn_body k entry.env entry.temps entry.memory))
    (hentry : function_entry2 ge f args m entry.env entry.temps entry.memory) :
    step2 ge (.Callstate (.Internal f) args k m) Events.E0
      (.State f f.fn_body k entry.env entry.temps entry.memory) := by
  exact enterInternalFunction_sound ge f args k m entry h hentry

/-- Dispatcher soundness for resuming a return through a call continuation. -/
theorem stepInternal_returnstate_sound
    (ge : genv) (v : val) (optid : Option ident) (f : function) (e : env)
    (le : temp_env) (k : cont) (m : Memory.mem) (s' : state)
    (h : stepInternal ge (.Returnstate v (.Kcall optid f e le k) m) = .ok s') :
    step2 ge (.Returnstate v (.Kcall optid f e le k) m) Events.E0 s' := by
  change Except.ok (resumeReturn v optid f e le k m) = Except.ok s' at h
  cases h
  exact resumeReturn_sound ge v optid f e le k m

/-- Dispatcher soundness for `Sskip` at a call continuation, given the
deallocation premise of the authoritative rule. -/
theorem stepInternal_skip_call_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m m' : Memory.mem) (s' : state)
    (hcall : is_call_cont k)
    (hfree : Memory.free_list m (blocks_of_env ge e) = some m')
    (h : stepInternal ge (.State f .Sskip k e le m) = .ok s') :
    step2 ge (.State f .Sskip k e le m) Events.E0 s' := by
  cases k <;> simp only [stepInternal] at h
  · exact stepSkipCall_sound ge f .Kstop e le m m' s' hcall hfree h
  · exact False.elim hcall
  · exact False.elim hcall
  · exact False.elim hcall
  · exact False.elim hcall
  · exact stepSkipCall_sound ge f (.Kcall _ _ _ _ _) e le m m' s' hcall hfree h

/-- Every successful transition produced by the internal-only dispatcher is
an authoritative, trace-free `step2` transition. -/
theorem stepInternal_sound
    (ge : genv) (s s' : state)
    (h : stepInternal ge s = .ok s') :
    step2 ge s Events.E0 s' := by
  cases s with
  | State f stmt k e le m =>
      cases stmt with
      | Sassign a1 a2 =>
          cases hloc : evalLvalue ge e le m a1 with
          | error err =>
              simp [stepInternal, stepAssign, hloc] at h
          | ok loc =>
              cases hvalue : evalExpr ge e le m a2 with
              | error err =>
                  simp [stepInternal, stepAssign, hloc, hvalue] at h
              | ok v2 =>
                  cases hcast : sem_cast v2 (typeof a2) (typeof a1) m with
                  | none =>
                      simp [stepInternal, stepAssign, hloc, hvalue, hcast] at h
                  | some v =>
                      cases hassign :
                          assignLoc ge.genv_cenv (typeof a1) m loc.block loc.offset
                            loc.bitfield v with
                      | error err =>
                          simp [stepInternal, stepAssign, hloc, hvalue, hcast, hassign] at h
                      | ok m' =>
                          exact stepAssign_sound ge f a1 a2 k e le m loc v2 v m' s'
                            (evalLvalue_sound ge e le m a1 loc hloc) hloc
                            (evalExpr_sound ge e le m a2 v2 hvalue) hvalue hcast
                            (assignLoc_sound ge.genv_cenv (typeof a1) m loc.block loc.offset
                              loc.bitfield v m' hassign)
                            hassign (by simpa only [stepInternal] using h)
      | Sset id a =>
          cases hvalue : evalExpr ge e le m a with
          | error err =>
              simp [stepInternal, stepSet, hvalue] at h
          | ok v =>
              exact stepSet_sound ge f id a k e le m v s'
                (evalExpr_sound ge e le m a v hvalue) hvalue
                (by simpa only [stepInternal] using h)
      | Scall optid a al =>
          cases hclass : classify_fun (typeof a) with
          | fun_default =>
              simp [stepInternal, stepCall, hclass] at h
          | fun_case_f tyargs tyres cconv =>
              cases heval : evalExpr ge e le m a with
              | error err =>
                  simp [stepInternal, stepCall, hclass, heval] at h
              | ok vf =>
                  cases hargs : evalExprList ge e le m al tyargs with
                  | error err =>
                      simp [stepInternal, stepCall, hclass, heval, hargs] at h
                  | ok vargs =>
                      cases hfind : Genv.find_funct ge.genv_genv vf with
                      | none =>
                          simp [stepInternal, stepCall, hclass, heval, hargs, hfind] at h
                      | some fd =>
                          by_cases htype : type_of_fundef fd = .Tfunction tyargs tyres cconv
                          · have hs : s' =
                              .Callstate fd vargs (.Kcall optid f e le k) m := by
                              simpa [stepInternal, stepCall, hclass, heval, hargs, hfind,
                                htype] using h.symm
                            subst s'
                            exact .step_call f optid a al k e le m tyargs tyres cconv vf vargs fd
                              hclass (evalExpr_sound ge e le m a vf heval)
                              (evalExprList_sound ge e le m al tyargs vargs hargs) hfind htype
                          · simp [stepInternal, stepCall, hclass, heval, hargs, hfind,
                              htype] at h
      | Sbuiltin optid ef tyargs al =>
          simp [stepInternal] at h
      | Ssequence s1 s2 =>
          exact stepControl_sequence_sound ge f s1 s2 k e le m s'
            (by simpa only [stepInternal] using h)
      | Sifthenelse a s1 s2 =>
          cases hvalue : evalExpr ge e le m a with
          | error err =>
              simp [stepInternal, stepIf, hvalue] at h
          | ok v =>
              cases hbool : bool_val v (typeof a) m with
              | none =>
                  simp [stepInternal, stepIf, hvalue, hbool] at h
              | some b =>
                  exact stepIf_sound ge f a s1 s2 k e le m v b s'
                    (evalExpr_sound ge e le m a v hvalue) hvalue hbool
                    (by simpa only [stepInternal] using h)
      | Sloop s1 s2 =>
          exact stepControl_loop_sound ge f s1 s2 k e le m s'
            (by simpa only [stepInternal] using h)
      | Sbreak =>
          cases k with
          | Kstop => simp [stepInternal, stepControl] at h
          | Kseq s k =>
              exact stepControl_break_seq_sound ge f s k e le m s'
                (by simpa only [stepInternal] using h)
          | Kloop1 s1 s2 k =>
              exact stepControl_break_loop1_sound ge f s1 s2 k e le m s'
                (by simpa only [stepInternal] using h)
          | Kloop2 s1 s2 k =>
              exact stepControl_break_loop2_sound ge f s1 s2 k e le m s'
                (by simpa only [stepInternal] using h)
          | Kswitch k =>
              exact stepControl_break_switch_sound ge f k e le m s'
                (by simpa only [stepInternal] using h)
          | Kcall optid f' e' le' k => simp [stepInternal, stepControl] at h
      | Scontinue =>
          cases k with
          | Kstop => simp [stepInternal, stepControl] at h
          | Kseq s k =>
              exact stepControl_continue_seq_sound ge f s k e le m s'
                (by simpa only [stepInternal] using h)
          | Kloop1 s1 s2 k =>
              exact stepControl_continue_loop1_sound ge f s1 s2 k e le m s'
                (by simpa only [stepInternal] using h)
          | Kloop2 s1 s2 k => simp [stepInternal, stepControl] at h
          | Kswitch k =>
              exact stepControl_continue_switch_sound ge f k e le m s'
                (by simpa only [stepInternal] using h)
          | Kcall optid f' e' le' k => simp [stepInternal, stepControl] at h
      | Sreturn oa =>
          cases oa with
          | none =>
              cases hfree : Memory.free_list m (blocks_of_env ge e) with
              | none =>
                  simp [stepInternal, stepReturnVoid, hfree] at h
              | some m' =>
                  exact stepReturnVoid_sound ge f k e le m m' s' hfree
                    (by simpa only [stepInternal] using h)
          | some a =>
              cases hvalue : evalExpr ge e le m a with
              | error err =>
                  simp [stepInternal, stepReturnValue, hvalue] at h
              | ok v =>
                  cases hcast : sem_cast v (typeof a) f.fn_return m with
                  | none =>
                      simp [stepInternal, stepReturnValue, hvalue, hcast] at h
                  | some v' =>
                      cases hfree : Memory.free_list m (blocks_of_env ge e) with
                      | none =>
                          simp [stepInternal, stepReturnValue, hvalue, hcast, hfree] at h
                      | some m' =>
                          exact stepReturnValue_sound ge f a k e le m v v' m' s'
                            (evalExpr_sound ge e le m a v hvalue) hvalue hcast hfree
                            (by simpa only [stepInternal] using h)
      | Sswitch a sl =>
          cases hvalue : evalExpr ge e le m a with
          | error err =>
              simp [stepInternal, stepSwitch, hvalue] at h
          | ok v =>
              cases hswitch : sem_switch_arg v (typeof a) with
              | none =>
                  simp [stepInternal, stepSwitch, hvalue, hswitch] at h
              | some n =>
                  exact stepSwitch_sound ge f a sl k e le m v n s'
                    (evalExpr_sound ge e le m a v hvalue) hvalue hswitch
                    (by simpa only [stepInternal] using h)
      | Slabel lbl body =>
          exact stepControl_label_sound ge f lbl body k e le m s'
            (by simpa only [stepInternal] using h)
      | Sgoto lbl =>
          exact stepControl_goto_sound ge f lbl k e le m s'
            (by simpa only [stepInternal] using h)
      | Sskip =>
          cases k with
          | Kstop =>
              cases hfree : Memory.free_list m (blocks_of_env ge e) with
              | none => simp [stepInternal, stepSkipCall, hfree] at h
              | some m' =>
                  exact stepSkipCall_sound ge f .Kstop e le m m' s' trivial hfree
                    (by simpa only [stepInternal] using h)
          | Kseq body k =>
              exact stepControl_skip_seq_sound ge f body k e le m s'
                (by simpa only [stepInternal] using h)
          | Kloop1 s1 s2 k =>
              exact stepControl_skip_loop1_sound ge f s1 s2 k e le m s'
                (by simpa only [stepInternal] using h)
          | Kloop2 s1 s2 k =>
              exact stepControl_skip_loop2_sound ge f s1 s2 k e le m s'
                (by simpa only [stepInternal] using h)
          | Kswitch k =>
              exact stepControl_skip_switch_sound ge f k e le m s'
                (by simpa only [stepInternal] using h)
          | Kcall optid f' e' le' k =>
              cases hfree : Memory.free_list m (blocks_of_env ge e) with
              | none => simp [stepInternal, stepSkipCall, hfree] at h
              | some m' =>
                  exact stepSkipCall_sound ge f (.Kcall optid f' e' le' k) e le m m' s'
                    trivial hfree (by simpa only [stepInternal] using h)
  | Callstate fd args k m =>
      cases fd with
      | Internal f =>
          cases hentry : functionEntry2 ge f args m with
          | error err =>
              simp [stepInternal, enterInternalFunction, hentry] at h
          | ok entry =>
              have hs : s' = .State f f.fn_body k entry.env entry.temps entry.memory := by
                simpa [stepInternal, enterInternalFunction, hentry] using h.symm
              subst s'
              exact .step_internal_function f args k m entry.env entry.temps entry.memory
                (functionEntry2_sound ge f args m entry hentry)
      | External ef tyargs tyres cconv =>
          simp [stepInternal] at h
  | Returnstate v k m =>
      cases k with
      | Kstop => simp [stepInternal] at h
      | Kseq body k => simp [stepInternal] at h
      | Kloop1 s1 s2 k => simp [stepInternal] at h
      | Kloop2 s1 s2 k => simp [stepInternal] at h
      | Kswitch k => simp [stepInternal] at h
      | Kcall optid f e le k =>
          change Except.ok (resumeReturn v optid f e le k m) = Except.ok s' at h
          cases h
          exact resumeReturn_sound ge v optid f e le k m

end CLightLean.Exec
