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

import CLightLean.Exec.FunctionReturn

/-!
Direct compositional soundness lemmas for function-body returns and the
call-continuation `Sskip` transition.  The relational `step2` semantics is
authoritative; these lemmas require its evaluation, cast, and deallocation
premises explicitly rather than proving a generic step correspondence theorem.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A successful void-return helper result is the authoritative
`step_return_0` transition when its local-block deallocation has the supplied
relational result. -/
theorem stepReturnVoid_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m m' : Memory.mem) (s' : state)
    (hfree : Memory.free_list m (blocks_of_env ge e) = some m')
    (h : stepReturnVoid ge f k e le m = .ok s') :
    step2 ge (.State f (.Sreturn none) k e le m) Events.E0 s' := by
  unfold stepReturnVoid at h
  simp only [hfree, Except.ok.injEq] at h
  cases h
  exact .step_return_0 f k e le m m' hfree

/-- A successful valued-return helper result is the authoritative
`step_return_1` transition when the expression evaluation, return-type cast,
and local-block deallocation have the supplied relational premises. -/
theorem stepReturnValue_sound
    (ge : genv) (f : function) (a : expr) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (v v' : val) (m' : Memory.mem) (s' : state)
    (hvalue : eval_expr ge e le m a v)
    (hvalue_exec : evalExpr ge e le m a = .ok v)
    (hcast : sem_cast v (typeof a) f.fn_return m = some v')
    (hfree : Memory.free_list m (blocks_of_env ge e) = some m')
    (h : stepReturnValue ge f a k e le m = .ok s') :
    step2 ge (.State f (.Sreturn (some a)) k e le m) Events.E0 s' := by
  unfold stepReturnValue at h
  simp only [hvalue_exec, hcast, hfree, Except.ok.injEq] at h
  cases h
  exact .step_return_1 f a k e le m v v' m' hvalue hcast hfree

/-- A successful call-continuation `Sskip` helper result is the authoritative
`step_skip_call` transition when the continuation and local-block
deallocation premises are supplied. -/
theorem stepSkipCall_sound
    (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m m' : Memory.mem) (s' : state)
    (hcall : is_call_cont k)
    (hfree : Memory.free_list m (blocks_of_env ge e) = some m')
    (h : stepSkipCall ge f k e le m = .ok s') :
    step2 ge (.State f .Sskip k e le m) Events.E0 s' := by
  cases k <;> simp only [stepSkipCall] at h
  · simp only [hfree, Except.ok.injEq] at h
    cases h
    exact .step_skip_call f .Kstop e le m m' hcall hfree
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp only [hfree, Except.ok.injEq] at h
    cases h
    exact .step_skip_call f (.Kcall _ _ _ _ _) e le m m' hcall hfree

end CLightLean.Exec
