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

import CLightLean.Builtins0
import CLightLean.Builtins1

/-!
# Known built-in functions

Port of `common/Builtins.v`. Thin glue combining the architecture-independent
`standard_builtin`s (`Builtins0.lean`) with the architecture-specific
platform builtins (`Builtins1.lean`, via the `PlatformBuiltins` typeclass)
into a single `builtin_function` type.
-/

namespace Builtins

variable [Archi] [Builtins1.PlatformBuiltins]

/-- A known built-in function is either one of the standard,
    architecture-independent builtins, or a platform-specific one. -/
inductive builtin_function : Type where
  | BI_standard (b : Builtins0.standard_builtin)
  | BI_platform (b : Builtins1.PlatformBuiltins.PBuiltin)

instance : DecidableEq builtin_function
  | .BI_standard b1, .BI_standard b2 =>
      if h : b1 = b2 then .isTrue (by rw [h]) else .isFalse (by intro he; injection he; contradiction)
  | .BI_standard _, .BI_platform _ => .isFalse (by intro h; injection h)
  | .BI_platform _, .BI_standard _ => .isFalse (by intro h; injection h)
  | .BI_platform b1, .BI_platform b2 =>
      if h : b1 = b2 then .isTrue (by rw [h]) else .isFalse (by intro he; injection he; contradiction)

def builtin_function_sig (b : builtin_function) : signature :=
  match b with
  | .BI_standard b => Builtins0.standard_builtin_sig b
  | .BI_platform b => Builtins1.PlatformBuiltins.sig b

def builtin_function_sem (b : builtin_function) :
    Builtins0.builtin_sem (builtin_function_sig b).sig_res :=
  match b with
  | .BI_standard b => Builtins0.standard_builtin_sem b
  | .BI_platform b => Builtins1.PlatformBuiltins.sem b

theorem builtin_function_sem_inject {b : builtin_function} {vargs : List val} {vres : val}
    {f : meminj} {vargs' : List val}
    (H : builtin_function_sem b vargs = some vres)
    (Hinj : Val.inject_list f vargs vargs') :
    ∃ vres', builtin_function_sem b vargs' = some vres' ∧ Val.inject f vres vres' := by
  have J := (builtin_function_sem b).bs_inject f vargs vargs' Hinj
  rw [H] at J
  cases hb : builtin_function_sem b vargs' with
  | none => rw [hb] at J; exact J.elim
  | some vres' =>
      refine ⟨vres', rfl, ?_⟩
      rw [hb] at J
      exact J

theorem builtin_function_sem_lessdef {b : builtin_function} {vargs : List val} {vres : val}
    {vargs' : List val}
    (H : builtin_function_sem b vargs = some vres)
    (Hld : Val.lessdef_list vargs vargs') :
    ∃ vres', builtin_function_sem b vargs' = some vres' ∧ Val.lessdef vres vres' := by
  obtain ⟨vres', A, B⟩ := builtin_function_sem_inject H ((val_inject_list_lessdef _ _).mp Hld)
  exact ⟨vres', A, (val_inject_lessdef _ _).mpr B⟩

def lookup_builtin_function (name : String) (sg : signature) : Option builtin_function :=
  match Builtins0.lookup_builtin Builtins0.standard_builtin_sig name sg
      Builtins0.standard_builtin_table with
  | some b => some (.BI_standard b)
  | none =>
      match Builtins0.lookup_builtin Builtins1.PlatformBuiltins.sig name sg
          Builtins1.PlatformBuiltins.table with
      | some b => some (.BI_platform b)
      | none => none

theorem lookup_builtin_function_sig {name : String} {sg : signature} {b : builtin_function}
    (H : lookup_builtin_function name sg = some b) : builtin_function_sig b = sg := by
  unfold lookup_builtin_function at H
  cases hE : Builtins0.lookup_builtin Builtins0.standard_builtin_sig name sg
      Builtins0.standard_builtin_table with
  | some bs =>
      rw [hE] at H
      injection H with H
      subst H
      show Builtins0.standard_builtin_sig bs = sg
      exact Builtins0.lookup_builtin_sig _ _ _ hE
  | none =>
      rw [hE] at H
      cases hE' : Builtins0.lookup_builtin Builtins1.PlatformBuiltins.sig name sg
          Builtins1.PlatformBuiltins.table with
      | some bp =>
          rw [hE'] at H
          injection H with H
          subst H
          show Builtins1.PlatformBuiltins.sig bp = sg
          exact Builtins0.lookup_builtin_sig _ _ _ hE'
      | none => rw [hE'] at H; exact absurd H (by simp)

end Builtins
