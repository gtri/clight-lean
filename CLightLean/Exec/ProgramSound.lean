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

import CLightLean.Exec.Program

/-!
Soundness for functional whole-program initial-state construction.

This is intentionally limited to construction of the initial Clight state.
It does not claim a whole-run correspondence theorem for the current
internal-only executor.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A successful functional initial-state construction is admitted by Clight's
authoritative whole-program `initial_state` relation.  The required global
memory initialization, main-symbol lookup, function-pointer lookup, and exact
main-signature facts are recovered from the successful computation itself. -/
theorem initialState_sound (p : program_type function) (s : state)
    (h : initialState p = .ok s) :
    initial_state p s := by
  unfold initialState at h
  dsimp only at h
  split at h
  next hmem => contradiction
  next m0 hmem =>
    split at h
    next hsymbol => contradiction
    next b hsymbol =>
      split at h
      next hfunction => contradiction
      next fd hfunction =>
        split at h
        next htype =>
          simp only [Except.ok.injEq] at h
          cases h
          exact .initial_state_intro b fd m0 hmem hsymbol hfunction htype
        next htype => contradiction

end CLightLean.Exec
