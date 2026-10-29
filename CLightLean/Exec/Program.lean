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

import CLightLean.Exec.Run

/-!
Whole-program initialization and bounded execution for the currently
silent/internal executor subset.

This module computes the same data selected by Clight's authoritative
`initial_state` relation.  It does not alter that relation, add external-call
semantics, or make the internal-only runner capable of observable traces.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Construct the whole-program initial call state accepted by the authoritative
`initial_state` relation.

The computation builds `globalenv p`, initializes global memory with
`Genv.init_mem (program_of_program function p)`, resolves `p.prog_main` in
that global environment, and accepts precisely the main signature
`Tfunction [] type_int32s cc_default`.  Initialization failure is reported as
`memoryFailure`; a missing main symbol/function or an unsuitable main
signature is reported as `malformedCall`.  On success the returned state is
exactly `Callstate fd [] Kstop m0`.

The resulting fundef need not be internal: as in the authoritative relation,
this constructor checks only the entry-point signature.  The internal-only
runner may subsequently reject an external main call state. -/
def initialState (p : program_type function) : Except ExecError state :=
  let ge := globalenv p
  match Genv.init_mem (program_of_program function p) with
  | none => .error .memoryFailure
  | some m0 =>
      match Genv.find_symbol ge.genv_genv p.prog_main with
      | none => .error .malformedCall
      | some b =>
          match Genv.find_funct_ptr ge.genv_genv b with
          | none => .error .malformedCall
          | some fd =>
              if type_of_fundef fd = .Tfunction [] type_int32s cc_default then
                .ok (.Callstate fd [] .Kstop m0)
              else
                .error .malformedCall

/-- Construct a whole-program initial state, then run the existing silent,
internal-only fuelled executor from that state with a fresh runtime.

The outer `Except` keeps initialization failure distinct from `RunResult`:
`initialState p = .error error` maps to `.error error`, while
`initialState p = .ok state` maps to
`.ok (runFuel (globalenv p) fuel state)`.  In particular, no artificial
runtime, trace, step count, or runner classification is invented for a
program that cannot be initialized. -/
def runProgramFuel (p : program_type function) (fuel : Nat) : Except ExecError RunResult :=
  match initialState p with
  | .error error => .error error
  | .ok state => .ok (runFuel (globalenv p) fuel state)

end CLightLean.Exec
