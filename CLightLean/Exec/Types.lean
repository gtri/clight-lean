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

import CLightLean.Exec.Core
import CLightLean.CLight
import CLightLean.Events

/-!
Clight-semantic result types shared by the additive CLight executor.

The relational CLight semantics remains authoritative.  These types only carry
the concrete executor's state, structured failures, and outcomes; they do not
define or replace any relational semantic function.
-/

namespace CLightLean.Exec

variable [Archi]

/-- One attempted concrete CLight transition. -/
inductive StepResult where
  | advanced (runtime : Runtime) (trace : Events.trace) (state : state)
  | completed (runtime : Runtime) (exit : CompCert.Int)
  | error (runtime : Runtime) (error : ExecError)

/-- Terminal classifications used by the pure fuelled and future IO runners. -/
inductive OutcomeStatus where
  | completed
  | fuelExhausted
  | unsupported
  | stuck
deriving DecidableEq, Repr

namespace OutcomeStatus

/-- Stable machine-oriented outcome code for a later runner envelope. -/
def code : OutcomeStatus → String
  | .completed => "completed"
  | .fuelExhausted => "fuel_exhausted"
  | .unsupported => "unsupported"
  | .stuck => "stuck"

end OutcomeStatus

/--
The result of a bounded execution, or of a future unbounded IO execution.

`steps` counts successfully advanced concrete CLight transitions.  `trace` is
the exact accumulated CompCert trace.  Stdout remains available only through
the associated `Runtime.stdout` bytes; it is deliberately not serialized here.
-/
inductive RunResult where
  | completed
      (runtime : Runtime) (trace : Events.trace) (exit : CompCert.Int) (steps : Nat)
  | fuelExhausted
      (runtime : Runtime) (trace : Events.trace) (state : state) (steps : Nat)
  | unsupported
      (runtime : Runtime) (trace : Events.trace) (error : ExecError) (steps : Nat)
  | stuck
      (runtime : Runtime) (trace : Events.trace) (error : ExecError) (steps : Nat)

namespace RunResult

/-- Classify a result without inspecting modeled stdout. -/
def status : RunResult → OutcomeStatus
  | .completed .. => .completed
  | .fuelExhausted .. => .fuelExhausted
  | .unsupported .. => .unsupported
  | .stuck .. => .stuck

/-- The runtime, including raw stdout bytes, for every result. -/
def runtime : RunResult → Runtime
  | .completed runtime .. => runtime
  | .fuelExhausted runtime .. => runtime
  | .unsupported runtime .. => runtime
  | .stuck runtime .. => runtime

/-- Number of successfully advanced transitions. -/
def steps : RunResult → Nat
  | .completed _ _ _ steps => steps
  | .fuelExhausted _ _ _ steps => steps
  | .unsupported _ _ _ steps => steps
  | .stuck _ _ _ steps => steps

/-- The C `main` return value, if execution completed normally. -/
def exit? : RunResult → Option CompCert.Int
  | .completed _ _ exit _ => some exit
  | _ => none

/-- The executor error, if execution reported unsupported or stuck behavior. -/
def error? : RunResult → Option ExecError
  | .unsupported _ _ error _ => some error
  | .stuck _ _ error _ => some error
  | _ => none

/-- Stable status token suitable for a later machine-readable runner envelope. -/
def statusCode (result : RunResult) : String :=
  result.status.code

end RunResult

end CLightLean.Exec
