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

import CLightLean.Exec.State

/-!
Deterministic computational prefixes for four basic Clight statement
transitions in the additive executor.

Each helper mirrors one authoritative `step2` rule, but none dispatches over
general statements or replaces the relational semantics.  Functional failures
from expression evaluation and location assignment are propagated unchanged.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Compute the assignment transition prefix: resolve the destination,
evaluate and cast the source, then perform the existing functional location
assignment.  A failed cast has the same `invalidExpression` classification as
the expression evaluator's failed cast branch. -/
def stepAssign (ge : genv) (f : function) (a1 a2 : expr) (k : cont)
    (e : env) (le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match evalLvalue ge e le m a1 with
  | .error err => .error err
  | .ok loc =>
      match evalExpr ge e le m a2 with
      | .error err => .error err
      | .ok v2 =>
          match sem_cast v2 (typeof a2) (typeof a1) m with
          | none => .error .invalidExpression
          | some v =>
              match assignLoc ge.genv_cenv (typeof a1) m loc.block loc.offset loc.bitfield v with
              | .error err => .error err
              | .ok m' => .ok (.State f .Sskip k e le m')

/-- Compute the temporary-set transition prefix by evaluating its right-hand
side and updating the temporary environment. -/
def stepSet (ge : genv) (f : function) (id : ident) (a : expr) (k : cont)
    (e : env) (le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match evalExpr ge e le m a with
  | .error err => .error err
  | .ok v => .ok (.State f .Sskip k e (le.insert id v) m)

/-- Compute the conditional transition prefix.  A value that cannot be
interpreted at the condition's Clight type is an `invalidExpression`; no
arbitrary branch is selected. -/
def stepIf (ge : genv) (f : function) (a : expr) (s1 s2 : statement) (k : cont)
    (e : env) (le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match evalExpr ge e le m a with
  | .error err => .error err
  | .ok v =>
      match bool_val v (typeof a) m with
      | none => .error .invalidExpression
      | some b => .ok (.State f (if b then s1 else s2) k e le m)

/-- Compute the switch transition prefix.  The selector is converted by the
existing `sem_switch_arg` API; only a successful conversion may select a case.
The selected suffix is sequenced and executed under a `Kswitch` continuation,
exactly as in `step_switch`. -/
def stepSwitch (ge : genv) (f : function) (a : expr) (sl : labeled_statements)
    (k : cont) (e : env) (le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match evalExpr ge e le m a with
  | .error err => .error err
  | .ok v =>
      match sem_switch_arg v (typeof a) with
      | none => .error .invalidExpression
      | some n =>
          .ok (.State f (seq_of_labeled_statement (select_switch (n : Int) sl))
            (.Kswitch k) e le m)

end CLightLean.Exec
