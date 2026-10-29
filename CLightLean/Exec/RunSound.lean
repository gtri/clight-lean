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
Direct proof facts for the bounded runner.

The final-state recognizer is proved against the authoritative Clight
`final_state` relation.  No general `runFromFuel`-to-`Smallstep.star` theorem
is claimed here: the current `stepInternal` soundness surface is intentionally
compositional and requires case-specific relational premises, so it is not yet
strong enough to justify a blanket bounded-run theorem.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A recognized final return is an authoritative Clight `final_state`. -/
theorem finalReturn?_sound {s : state} {r : CompCert.Int}
    (h : finalReturn? s = some r) :
    final_state s r := by
  cases s with
  | State f statement k e le m =>
      simp [finalReturn?] at h
  | Callstate fd args k m =>
      simp [finalReturn?] at h
  | Returnstate result k m =>
      cases result with
      | Vundef => simp [finalReturn?] at h
      | Vint i =>
          cases k with
          | Kstop =>
              have hir : i = r := Option.some.inj h
              subst i
              exact .final_state_intro r m
          | Kseq statement k => simp [finalReturn?] at h
          | Kloop1 statement1 statement2 k => simp [finalReturn?] at h
          | Kloop2 statement1 statement2 k => simp [finalReturn?] at h
          | Kswitch k => simp [finalReturn?] at h
          | Kcall optid f e le k => simp [finalReturn?] at h
      | Vlong i => simp [finalReturn?] at h
      | Vfloat f => simp [finalReturn?] at h
      | Vsingle f => simp [finalReturn?] at h
      | Vptr b ofs => simp [finalReturn?] at h

/-- The executable recognizer accepts exactly the states admitted by
the authoritative `final_state` relation. -/
theorem finalReturn?_iff (s : state) (r : CompCert.Int) :
    finalReturn? s = some r ↔ final_state s r := by
  constructor
  · exact finalReturn?_sound
  · intro h
    cases h
    rfl

end CLightLean.Exec
