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

import CLightLean.Exec.Step

/-!
Pure bounded execution for the currently internal-only executor subset.

This module is deliberately an iterator over `stepInternal`, not a replacement
for Clight's authoritative relational `step2`, `final_state`, or
`Smallstep.star` definitions.  It accepts an already constructed Clight
`state`; constructing a whole-program initial state is outside this milestone.

## Fuel convention

`runFromFuel ge fuel runtime state` checks for a recognized final state before
checking fuel.  Otherwise, each successful `stepInternal` transition consumes
one unit of fuel and increments `steps` by one.  Thus a final state reached by
the nth successful transition completes with exactly n units of fuel, and an
already-final state completes with zero fuel and zero steps.

## Trace and runtime boundary

The admitted `stepInternal` subset is silent: it has no external semantics and
every successful transition corresponds to `Events.E0`.  Accordingly, this
runner keeps `runtime` unchanged and returns `Events.E0` in every `RunResult`.
This is not a general trace-accumulation model and does not characterize future
external calls or stdout effects.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Recognize exactly the authoritative Clight final-state shape accepted by
this internal runner: an integer return value at `Kstop`.  In particular,
`Vundef`, non-integer values, and return states with a call continuation are
not recognized as final. -/
def finalReturn? : state → Option CompCert.Int
  | .Returnstate (.Vint r) .Kstop _ => some r
  | _ => none

/-- Internal tail-recursive worker for `runFromFuel`.  `steps` is the number of
successful transitions already taken.  It is intentionally private so public
callers cannot supply an inconsistent starting count. -/
private def runLoop (ge : genv) : Nat → Runtime → state → Nat → RunResult
  | fuel, runtime, currentState, steps =>
      match finalReturn? currentState with
      | some result => .completed runtime Events.E0 result steps
      | none =>
          match fuel with
          | 0 => .fuelExhausted runtime Events.E0 currentState steps
          | fuel + 1 =>
              match stepInternal ge currentState with
              | .ok nextState => runLoop ge fuel runtime nextState (steps + 1)
              | .error error =>
                  match error with
                  | .unsupportedExternal _ => .unsupported runtime Events.E0 error steps
                  | _ => .stuck runtime Events.E0 error steps

/-- Run the internal-only executor from an existing Clight state with an
explicit executor runtime.

The outcome mapping is exact for this subset:

* `finalReturn? currentState = some r` maps to
  `RunResult.completed runtime Events.E0 r steps`;
* no final result with zero remaining fuel maps to
  `RunResult.fuelExhausted runtime Events.E0 currentState steps`;
* `stepInternal` errors of the form `ExecError.unsupportedExternal _` map to
  `RunResult.unsupported runtime Events.E0 error steps`; and
* all other `stepInternal` errors map to
  `RunResult.stuck runtime Events.E0 error steps`.

See the module documentation for the final-before-fuel and successful-step fuel
convention. -/
def runFromFuel (ge : genv) (fuel : Nat) (runtime : Runtime) (initialState : state) :
    RunResult :=
  runLoop ge fuel runtime initialState 0

/-- Run the internal-only executor from an existing Clight state with a fresh,
empty executor runtime.  This is the convenience wrapper around
`runFromFuel`; it does not construct an initial state from a program. -/
def runFuel (ge : genv) (fuel : Nat) (initialState : state) : RunResult :=
  runFromFuel ge fuel Runtime.empty initialState

end CLightLean.Exec
