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

import CLightLean.Exec.Expr

/-!
Pure evaluation of the `Scall` transition prefix for the additive executor.

This module computes only the work represented by the authoritative
`step_call` rule: it does not enter a function, dispatch external calls, or
provide a general statement stepper.  The relational semantics in
`CLight.lean` remains authoritative.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Compute the successor of an ordinary Clight `Scall` statement through the
`step_call` rule's computational premises.  The resolved fundef is retained
unchanged in the resulting `Callstate`, exactly as in the relational rule;
whether it is internal or external is deliberately left for later call-state
handling.

An expression/type-list arity mismatch is `malformedCall`.  A callee that is
not function-typed, does not resolve to a global function, or resolves to a
different function signature is `invalidExpression`. -/
def stepCall (ge : genv) (f : function) (optid : Option ident) (a : expr)
    (al : List expr) (k : cont) (e : env) (le : temp_env) (m : Memory.mem) :
    Except ExecError state :=
  match classify_fun (typeof a) with
  | .fun_default => .error .invalidExpression
  | .fun_case_f tyargs tyres cconv =>
      match evalExpr ge e le m a with
      | .error err => .error err
      | .ok vf =>
          match evalExprList ge e le m al tyargs with
          | .error err => .error err
          | .ok vargs =>
              match Genv.find_funct ge.genv_genv vf with
              | none => .error .invalidExpression
              | some fd =>
                  if type_of_fundef fd = .Tfunction tyargs tyres cconv then
                    .ok (.Callstate fd vargs (.Kcall optid f e le k) m)
                  else
                    .error .invalidExpression

end CLightLean.Exec
