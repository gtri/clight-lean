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

import CLightLean.Exec.Call

/-!
Compositional soundness for the pure `Scall` transition helper.

The existing `step2` relation remains authoritative.  This theorem only joins
successful functional computation with the corresponding relational expression
premises; it is not a general executor-step theorem.
-/

namespace CLightLean.Exec

variable [Archi]

/-- If the pure call helper succeeds with the values supplied by matching
functional and relational expression evaluations, its exact call-state
successor is admitted by the authoritative `step2` call rule. -/
theorem stepCall_sound
    (ge : genv) (f : function) (optid : Option ident) (a : expr) (al : List expr)
    (k : cont) (e : env) (le : temp_env) (m : Memory.mem)
    (tyargs : List type) (tyres : type) (cconv : calling_convention)
    (vf : val) (vargs : List val) (fd : fundef_type function)
    (hclass : classify_fun (typeof a) = .fun_case_f tyargs tyres cconv)
    (heval : eval_expr ge e le m a vf)
    (heval_exec : evalExpr ge e le m a = .ok vf)
    (hargs : eval_exprlist ge e le m al tyargs vargs)
    (hargs_exec : evalExprList ge e le m al tyargs = .ok vargs)
    (h : stepCall ge f optid a al k e le m =
      .ok (.Callstate fd vargs (.Kcall optid f e le k) m)) :
    step2 ge (.State f (.Scall optid a al) k e le m)
      Events.E0 (.Callstate fd vargs (.Kcall optid f e le k) m) := by
  unfold stepCall at h
  rw [hclass, heval_exec] at h
  dsimp only [Bind.bind, Except.bind] at h
  rw [hargs_exec] at h
  cases hfind : Genv.find_funct ge.genv_genv vf with
  | none =>
      simp only [hfind] at h
      exact nomatch h
  | some found =>
      simp only [hfind] at h
      split at h
      · rename_i htype
        have hfd : found = fd := by
          have hresult : found = fd ∧ True ∧ True ∧ True := by
            simpa only [Except.ok.injEq, state.Callstate.injEq] using h
          exact hresult.1
        subst found
        exact step.step_call f optid a al k e le m tyargs tyres cconv vf vargs fd
          hclass heval hargs hfind htype
      · exact nomatch h

end CLightLean.Exec
