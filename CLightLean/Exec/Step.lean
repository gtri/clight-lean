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
import CLightLean.Exec.Call
import CLightLean.Exec.Control
import CLightLean.Exec.Entry
import CLightLean.Exec.FunctionReturn
import CLightLean.Exec.Return

/-!
The internal-only, pure single-step dispatcher for the additive executor.

`stepInternal` is deliberately only a dispatcher: it selects among the
existing functional transition helpers and does not duplicate their semantics.
It supports the currently executable internal `step2` subset, and every
successful transition has trace `Events.E0`.  Builtins and external call
states are rejected explicitly; this module neither models external functions
nor emits traces.

The authoritative relational `step2` definition remains unchanged in
`CLight.lean`.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Attempt one internal, trace-free Clight transition.

The dispatch order follows the authoritative `step2` partition.  In
particular, `Sskip` at a `Kstop` or `Kcall` continuation exits the current
function through `stepSkipCall`; administrative sequence, switch, and loop
continuations remain the responsibility of `stepControl`.  A final
`Returnstate (Vint _) Kstop` is not a transition and is therefore reported as
`stuck`; a later runner will recognize final states before asking to step.

`Sbuiltin` and every external `Callstate` are intentionally rejected with
`unsupportedExternal`.  No external-call, runtime, trace, fuel, or IO model is
introduced here. -/
def stepInternal (ge : genv) : state → Except ExecError state
  | .State f (.Sassign a1 a2) k e le m =>
      stepAssign ge f a1 a2 k e le m
  | .State f (.Sset id a) k e le m =>
      stepSet ge f id a k e le m
  | .State f (.Scall optid a al) k e le m =>
      stepCall ge f optid a al k e le m
  | .State _ (.Sbuiltin _ _ _ _) _ _ _ _ =>
      .error (.unsupportedExternal "builtin")
  | .State f (.Sifthenelse a s1 s2) k e le m =>
      stepIf ge f a s1 s2 k e le m
  | .State f (.Sswitch a sl) k e le m =>
      stepSwitch ge f a sl k e le m
  | .State f (.Sreturn none) k e le m =>
      stepReturnVoid ge f k e le m
  | .State f (.Sreturn (some a)) k e le m =>
      stepReturnValue ge f a k e le m
  | state@(.State f .Sskip k e le m) =>
      match k with
      | .Kstop | .Kcall _ _ _ _ _ => stepSkipCall ge f k e le m
      | _ => stepControl state
  | state@(.State _ (.Ssequence _ _) _ _ _ _) =>
      stepControl state
  | state@(.State _ (.Sloop _ _) _ _ _ _) =>
      stepControl state
  | state@(.State _ .Sbreak _ _ _ _) =>
      stepControl state
  | state@(.State _ .Scontinue _ _ _ _) =>
      stepControl state
  | state@(.State _ (.Slabel _ _) _ _ _ _) =>
      stepControl state
  | state@(.State _ (.Sgoto _) _ _ _ _) =>
      stepControl state
  | .Callstate (.Internal f) args k m =>
      enterInternalFunction ge f args k m
  | .Callstate (.External _ _ _ _) _ _ _ =>
      .error (.unsupportedExternal "external-call")
  | .Returnstate v (.Kcall optid f e le k) m =>
      .ok (resumeReturn v optid f e le k m)
  | .Returnstate _ _ _ =>
      .error .stuck

end CLightLean.Exec
