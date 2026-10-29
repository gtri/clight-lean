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

-- Architecture-dependent parameters for x86 in 64-bit mode

/- WARNING: This diverges from the CompCert/VST approach quite a bit. It seemed more idiomatic to define Archi as a typeclass. -/

class Archi where
  ptr64 : Bool
  big_endian : Bool
  align_int64 : Nat
  align_float64 : Nat
  splitlong : Bool := !ptr64
  splitlong_ptr32 : splitlong = true → ptr64 = false -- an obligation for Archi instances

  -- NaN behavior
  default_nan_64 : Bool × Nat
  default_nan_32 : Bool × Nat
  choose_nan_64 : List (Bool × Nat) → (Bool × Nat)
  choose_nan_32 : List (Bool × Nat) → (Bool × Nat)
  fma_order : {α : Type} → α → α → α → (α × α × α)
  fma_invalid_mul_is_nan : Bool
  float_of_single_preserves_sNaN : Bool
  float_conversion_default_nan : Bool

  -- obligations on float behavior
  choose_nan_64_idem : ∀ n, choose_nan_64 [n, n] = choose_nan_64 [n]
  choose_nan_32_idem : ∀ n, choose_nan_32 [n, n] = choose_nan_32 [n]
  align_int64_two_p : ∃ n : Nat, align_int64 = 2^n
  align_float64_two_p : ∃ n : Nat, align_float64 = 2^n
  align_float64_bound : align_float64 ∣ 8
  align_int64_bound : align_int64 ∣ 8

-- Neither of the two below is a global `instance`: `Archi` is a zero-parameter
-- class, so two unconditional global instances are structurally ambiguous
-- (nothing lets typeclass search pick between them; ties silently resolve by
-- declaration order). Every consumer must opt in to exactly one, explicitly,
-- via `attribute [instance] x86_64` (as clightgen's own generated files
-- already do), `attribute [local instance] x86_64` for a section/file, or
-- `haveI : Archi := x86_64` for a single proof -- never implicitly.
--
-- Marked `@[reducible]`: once a consumer opts in via `attribute [instance]`,
-- tactics like `simp`/`rfl`/typeclass-driven unification need to unfold this
-- definition at "instances" transparency to see through to its fields (e.g.
-- `Archi.ptr64`). Plain `def`s default to non-reducible, which leaves goals
-- like `Archi.ptr64 = true` stuck even with the instance in scope.
@[reducible] def x86_64 : Archi where
  ptr64 := true
  big_endian := false
  align_int64 := 8
  align_float64 := 8
  splitlong_ptr32 := by simp
  default_nan_64 := (true, 1 <<< 51)
  default_nan_32 := (true, 1 <<< 22)
  choose_nan_64 := λ | [] => (true, 1 <<< 51) | n :: _ => n
  choose_nan_32 := λ | [] => (true, 1 <<< 22) | n :: _ => n
  fma_order := λ x y z => (x, y, z)
  fma_invalid_mul_is_nan := false
  float_of_single_preserves_sNaN := false
  float_conversion_default_nan := false
  choose_nan_64_idem := by intro; rfl
  choose_nan_32_idem := by intro; rfl
  align_int64_two_p := by exact ⟨3, by simp⟩
  align_float64_two_p := by exact ⟨3, by simp⟩
  align_float64_bound := by simp
  align_int64_bound := by simp


@[reducible] def x86_32 : Archi where
  ptr64 := false
  big_endian := false
  align_int64 := 4
  align_float64 := 4
  splitlong_ptr32 := by simp
  default_nan_64 := (true, 1 <<< 51)
  default_nan_32 := (true, 1 <<< 22)
  choose_nan_64 := λ | [] => (true, 1 <<< 51) | n :: _ => n
  choose_nan_32 := λ | [] => (true, 1 <<< 22) | n :: _ => n
  fma_order := λ x y z => (x, y, z)
  fma_invalid_mul_is_nan := false
  float_of_single_preserves_sNaN := false
  float_conversion_default_nan := false
  choose_nan_64_idem := by intro; rfl
  choose_nan_32_idem := by intro; rfl
  align_int64_two_p := by exact ⟨2, by simp⟩
  align_float64_two_p := by exact ⟨2, by simp⟩
  align_float64_bound := by simp
  align_int64_bound := by simp
