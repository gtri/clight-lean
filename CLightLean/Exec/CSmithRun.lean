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

import CLightLean.Exec.CSmithStep
import CLightLean.Exec.Program

/-!
Bounded execution for the additive CSmith fixed-signature checksum path.

This runner uses the same final-before-fuel convention as `runFromFuel`, but
threads the executor runtime and appends each transition's CompCert trace.
The currently admitted checksum helper emits `Events.E0`; retaining generic
trace accumulation here keeps the runner's result policy accurate if later
owned CSmith actions have specified traces.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Internal implementation helper for `runCSmithFromFuel`.  It is public so
correspondence proofs can induct over its structural fuel recursion; callers
should use `runCSmithFromFuel` instead. `steps` counts successful transitions
already taken, and `trace` is their left-to-right append. -/
def runCSmithLoop (ge : genv) :
    Nat → Runtime → Events.trace → state → Nat → RunResult
  | fuel, runtime, trace, currentState, steps =>
      match finalReturn? currentState with
      | some result => .completed runtime trace result steps
      | none =>
          match fuel with
          | 0 => .fuelExhausted runtime trace currentState steps
          | fuel + 1 =>
              match stepCSmith ge runtime currentState with
              | .ok transition =>
                  runCSmithLoop ge fuel transition.runtime (trace ++ transition.trace)
                    transition.state (steps + 1)
              | .error error =>
                  match error with
                  | .unsupportedExternal _ => .unsupported runtime trace error steps
                  | _ => .stuck runtime trace error steps

/--
Run the CSmith-aware executor from an existing state and runtime with bounded
fuel. Final states are recognized before fuel is checked. Each successful
transition consumes one fuel unit, appends its exact trace, and supplies its
successor runtime to the next iteration.
-/
def runCSmithFromFuel (ge : genv) (fuel : Nat) (runtime : Runtime) (initialState : state) :
    RunResult :=
  runCSmithLoop ge fuel runtime Events.E0 initialState 0

/-- Fresh-runtime convenience wrapper for `runCSmithFromFuel`. -/
def runCSmithFuel (ge : genv) (fuel : Nat) (initialState : state) : RunResult :=
  runCSmithFromFuel ge fuel Runtime.empty initialState

/--
Construct the ordinary whole-program initial state, then run it through the
CSmith-aware bounded executor. Initialization errors remain distinct from
execution outcomes exactly as in `runProgramFuel`.
-/
def runCSmithProgramFuel (p : program_type function) (fuel : Nat) :
    Except ExecError RunResult :=
  match initialState p with
  | .error error => .error error
  | .ok initialState => .ok (runCSmithFuel (globalenv p) fuel initialState)

end CLightLean.Exec
