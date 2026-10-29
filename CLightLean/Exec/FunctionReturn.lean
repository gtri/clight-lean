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
Pure function-body return and call-continuation transitions for the additive
executor.

Each helper mirrors exactly one authoritative `step2` rule.  They free only
the blocks named by the current local environment through `Memory.free_list`;
they neither dispatch arbitrary statements nor resume a caller after a
`Returnstate`.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Compute the `Sreturn none` transition.  A failed local-block deallocation
is reported as `memoryFailure`; otherwise the return value is `Vundef` and
administrative continuations are removed with `call_cont`. -/
def stepReturnVoid (ge : genv) (_f : function) (k : cont) (e : env)
    (_le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match Memory.free_list m (blocks_of_env ge e) with
  | some m' => .ok (.Returnstate .Vundef (call_cont k) m')
  | none => .error .memoryFailure

/-- Compute the `Sreturn (some a)` transition.  Expression errors are
propagated, a failed return-type cast is `invalidExpression`, and failed local
block deallocation is `memoryFailure`. -/
def stepReturnValue (ge : genv) (f : function) (a : expr) (k : cont) (e : env)
    (le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match evalExpr ge e le m a with
  | .error err => .error err
  | .ok v =>
      match sem_cast v (typeof a) f.fn_return m with
      | none => .error .invalidExpression
      | some v' =>
          match Memory.free_list m (blocks_of_env ge e) with
          | some m' => .ok (.Returnstate v' (call_cont k) m')
          | none => .error .memoryFailure

/-- Compute the `Sskip` function-exit transition when the continuation is a
call continuation (`Kstop` or `Kcall`).  Other continuations do not admit this
authoritative transition and are explicitly reported as `stuck`. -/
def stepSkipCall (ge : genv) (_f : function) (k : cont) (e : env)
    (_le : temp_env) (m : Memory.mem) : Except ExecError state :=
  match k with
  | .Kstop | .Kcall _ _ _ _ _ =>
      match Memory.free_list m (blocks_of_env ge e) with
      | some m' => .ok (.Returnstate .Vundef k m')
      | none => .error .memoryFailure
  | _ => .error .stuck

end CLightLean.Exec
