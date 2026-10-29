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

import CLightLean.Exec.Basic

/-!
Direct compositional soundness lemmas for the basic statement-transition
helpers.  Each theorem takes the authoritative relational operand premises and
the matching successful functional computations explicitly; this is not a
generic functional-step correspondence theorem.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A successful assignment helper transition is admitted by the authoritative
`step2` assignment rule when its resolved lvalue, evaluated source, cast, and
functional location-store result have their matching relational premises. -/
theorem stepAssign_sound
    (ge : genv) (f : function) (a1 a2 : expr) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (loc : Lvalue) (v2 v : val) (m' : Memory.mem) (s' : state)
    (hloc : eval_lvalue ge e le m a1 loc.block loc.offset loc.bitfield)
    (hloc_exec : evalLvalue ge e le m a1 = .ok loc)
    (hvalue : eval_expr ge e le m a2 v2)
    (hvalue_exec : evalExpr ge e le m a2 = .ok v2)
    (hcast : sem_cast v2 (typeof a2) (typeof a1) m = some v)
    (hassign : assign_loc ge.genv_cenv (typeof a1) m loc.block loc.offset loc.bitfield v m')
    (hassign_exec : assignLoc ge.genv_cenv (typeof a1) m loc.block loc.offset loc.bitfield v = .ok m')
    (h : stepAssign ge f a1 a2 k e le m = .ok s') :
    step2 ge (.State f (.Sassign a1 a2) k e le m) Events.E0 s' := by
  unfold stepAssign at h
  simp only [hloc_exec, hvalue_exec, hcast, hassign_exec, Except.ok.injEq] at h
  cases h
  exact .step_assign f a1 a2 k e le m loc.block loc.offset loc.bitfield v2 v m'
    hloc hvalue hcast hassign

/-- A successful temporary-set helper transition is admitted by the
authoritative `step2` set rule when its expression result has the supplied
relational derivation. -/
theorem stepSet_sound
    (ge : genv) (f : function) (id : ident) (a : expr) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (v : val) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (h : stepSet ge f id a k e le m = .ok s') :
    step2 ge (.State f (.Sset id a) k e le m) Events.E0 s' := by
  unfold stepSet at h
  rw [hvalue_exec] at h
  simp only [Except.ok.injEq] at h
  cases h
  exact .step_set f id a k e le m v hvalue

/-- A successful conditional helper transition is admitted by the
authoritative `step2` conditional rule when its expression result and boolean
interpretation have the supplied relational/computational premises. -/
theorem stepIf_sound
    (ge : genv) (f : function) (a : expr) (s1 s2 : statement) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) (v : val) (b : Bool) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (hbool : bool_val v (typeof a) m = some b)
    (h : stepIf ge f a s1 s2 k e le m = .ok s') :
    step2 ge (.State f (.Sifthenelse a s1 s2) k e le m) Events.E0 s' := by
  unfold stepIf at h
  simp only [hvalue_exec, hbool, Except.ok.injEq] at h
  cases h
  exact .step_ifthenelse f a s1 s2 k e le m v b hvalue hbool

/-- A successful switch helper transition is admitted by the authoritative
`step2` switch rule when its selector evaluation and switch-argument
conversion have the supplied matching premises. -/
theorem stepSwitch_sound
    (ge : genv) (f : function) (a : expr) (sl : labeled_statements) (k : cont)
    (e : env) (le : temp_env) (m : Memory.mem) (v : val) (n : Nat) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (hswitch : sem_switch_arg v (typeof a) = some n)
    (h : stepSwitch ge f a sl k e le m = .ok s') :
    step2 ge (.State f (.Sswitch a sl) k e le m) Events.E0 s' := by
  unfold stepSwitch at h
  simp only [hvalue_exec, hswitch, Except.ok.injEq] at h
  cases h
  exact .step_switch f a sl k e le m v n hvalue hswitch

end CLightLean.Exec
