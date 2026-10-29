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

import FloatLib.Floats
import FloatLib.Floats.Formats.IEEE754.Native
import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
import CLightLean.Lib.Integers

/-!
# CompCert-compatible float types, backed by FloatLib

`CompCert.Float64` / `CompCert.Float32` are FloatLib's IEEE binary64 / binary32
(`ExecFloat.Binary`). Arithmetic is round-to-nearest-even, as in CompCert's
`Floats.v`.

Float-to-integer conversions truncate toward zero and return `none` on NaN,
infinity, or an out-of-range result, matching CompCert's `Float.to_int` etc.

Expected behavior on boundary inputs is checked against a hardware oracle in
`Test/Exec/FloatApiTest.lean` (generated from `Test/FloatOracle/float_oracle.c`).
-/

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange

abbrev CompCert.Float64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
abbrev CompCert.Float32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

instance : DecidableEq CompCert.Float32 := inferInstance
instance : DecidableEq CompCert.Float64 := inferInstance

/-- Result of a float arithmetic operation. Only the value is modeled;
CompCert's semantics does not observe IEEE status flags. -/
structure CompCert.FloatResult (α : Type) where
  value : α

namespace CompCert.FloatConv

/-- Truncate a finite float toward zero; `none` for NaN and infinity. -/
def truncToInt? {fmt : FloatFormat} (x : Model fmt) : Option _root_.Int :=
  match Model.exactValue x with
  | .finite d => some (Model.roundDyadicToInt .towardZero d)
  | _ => none

/-- Signed truncation into `[-2^(w-1), 2^(w-1))`, else `none`. -/
def toSigned? {fmt : FloatFormat} (w : Nat) (x : Model fmt) : Option _root_.Int :=
  (truncToInt? x).bind fun n =>
    if -(2 ^ (w - 1) : _root_.Int) ≤ n ∧ n < 2 ^ (w - 1) then some n else none

/-- Unsigned truncation into `[0, 2^w)`, else `none`. -/
def toUnsigned? {fmt : FloatFormat} (w : Nat) (x : Model fmt) : Option _root_.Int :=
  (truncToInt? x).bind fun n =>
    if 0 ≤ n ∧ n < 2 ^ w then some n else none

end CompCert.FloatConv

namespace CompCert.Float32
  def zero : CompCert.Float32 := ExecFloat.Binary.ofBits32 0
  def one : CompCert.Float32 := ExecFloat.Binary.ofBits32 0x3F800000

  def add (x y : CompCert.Float32) : CompCert.FloatResult CompCert.Float32 := ⟨x + y⟩
  def sub (x y : CompCert.Float32) : CompCert.FloatResult CompCert.Float32 := ⟨x - y⟩
  def mul (x y : CompCert.Float32) : CompCert.FloatResult CompCert.Float32 := ⟨x * y⟩
  def div (x y : CompCert.Float32) : CompCert.FloatResult CompCert.Float32 := ⟨x / y⟩

  def neg (x : CompCert.Float32) : CompCert.Float32 := -x
  def abs (x : CompCert.Float32) : CompCert.Float32 := ExecFloat.Binary.abs x

  /-- IEEE-754 comparisons: `+0 = -0`; every comparison with NaN is false
  except `Cne`. -/
  def cmp (c : comparison) (x y : CompCert.Float32) : Bool :=
    match c with
    | .Ceq => x == y
    | .Cne => !(x == y)
    | .Clt => decide (x < y)
    | .Cle => decide (x ≤ y)
    | .Cgt => decide (y < x)
    | .Cge => decide (y ≤ x)

  /-- Float from its exact 32-bit pattern (used for clightgen float literals). -/
  def of_bits (b : CompCert.Int) : CompCert.Float32 := ExecFloat.Binary.ofBits32 b

  /-- Default quiet NaN, `0x7FC00000`. -/
  def default_nan : CompCert.Float32 := ExecFloat.Binary.ofBits32 0x7FC00000

  private def ofIntRN (n : _root_.Int) : CompCert.Float32 :=
    ((ExecFloat.convert (target := CompCert.Float32) n).value?).getD zero

  def of_int (x : CompCert.Int) : CompCert.Float32 := ofIntRN x.signed
  def of_intu (x : CompCert.Int) : CompCert.Float32 := ofIntRN (x.unsigned : _root_.Int)
  def of_long (x : CompCert.Int64) : CompCert.Float32 := ofIntRN x.signed
  def of_longu (x : CompCert.Int64) : CompCert.Float32 := ofIntRN (x.unsigned : _root_.Int)

  def to_int (x : CompCert.Float32) : Option CompCert.Int :=
    (CompCert.FloatConv.toSigned? 32 (ExecFloat.Binary.toModel x)).map CompCert.Int.repr
  def to_intu (x : CompCert.Float32) : Option CompCert.Int :=
    (CompCert.FloatConv.toUnsigned? 32 (ExecFloat.Binary.toModel x)).map CompCert.Int.repr
  def to_long (x : CompCert.Float32) : Option CompCert.Int64 :=
    (CompCert.FloatConv.toSigned? 64 (ExecFloat.Binary.toModel x)).map CompCert.Int64.repr
  def to_longu (x : CompCert.Float32) : Option CompCert.Int64 :=
    (CompCert.FloatConv.toUnsigned? 64 (ExecFloat.Binary.toModel x)).map CompCert.Int64.repr
end CompCert.Float32

namespace CompCert.Float64
  def zero : CompCert.Float64 := ExecFloat.Binary.ofBits64 0
  def one : CompCert.Float64 := ExecFloat.Binary.ofBits64 0x3FF0000000000000

  def add (x y : CompCert.Float64) : CompCert.FloatResult CompCert.Float64 := ⟨x + y⟩
  def sub (x y : CompCert.Float64) : CompCert.FloatResult CompCert.Float64 := ⟨x - y⟩
  def mul (x y : CompCert.Float64) : CompCert.FloatResult CompCert.Float64 := ⟨x * y⟩
  def div (x y : CompCert.Float64) : CompCert.FloatResult CompCert.Float64 := ⟨x / y⟩

  def neg (x : CompCert.Float64) : CompCert.Float64 := -x
  def abs (x : CompCert.Float64) : CompCert.Float64 := ExecFloat.Binary.abs x

  /-- IEEE-754 comparisons: `+0 = -0`; every comparison with NaN is false
  except `Cne`. -/
  def cmp (c : comparison) (x y : CompCert.Float64) : Bool :=
    match c with
    | .Ceq => x == y
    | .Cne => !(x == y)
    | .Clt => decide (x < y)
    | .Cle => decide (x ≤ y)
    | .Cgt => decide (y < x)
    | .Cge => decide (y ≤ x)

  /-- binary32 → binary64 (exact). -/
  def of_single (x : CompCert.Float32) : CompCert.Float64 :=
    ExecFloat.Binary.ofModel
      (Model.cast FloatFormat.binary32 FloatFormat.binary64 (ExecFloat.Binary.toModel x))
  /-- binary64 → binary32 (round-to-nearest-even; overflow gives ±∞). -/
  def to_single (x : CompCert.Float64) : CompCert.Float32 :=
    ExecFloat.Binary.ofModel
      (Model.cast FloatFormat.binary64 FloatFormat.binary32 (ExecFloat.Binary.toModel x))

  private def ofIntRN (n : _root_.Int) : CompCert.Float64 :=
    ((ExecFloat.convert (target := CompCert.Float64) n).value?).getD zero

  def of_int (x : CompCert.Int) : CompCert.Float64 := ofIntRN x.signed
  def of_intu (x : CompCert.Int) : CompCert.Float64 := ofIntRN (x.unsigned : _root_.Int)
  def of_long (x : CompCert.Int64) : CompCert.Float64 := ofIntRN x.signed
  def of_longu (x : CompCert.Int64) : CompCert.Float64 := ofIntRN (x.unsigned : _root_.Int)

  def to_int (x : CompCert.Float64) : Option CompCert.Int :=
    (CompCert.FloatConv.toSigned? 32 (ExecFloat.Binary.toModel x)).map CompCert.Int.repr
  def to_intu (x : CompCert.Float64) : Option CompCert.Int :=
    (CompCert.FloatConv.toUnsigned? 32 (ExecFloat.Binary.toModel x)).map CompCert.Int.repr
  def to_long (x : CompCert.Float64) : Option CompCert.Int64 :=
    (CompCert.FloatConv.toSigned? 64 (ExecFloat.Binary.toModel x)).map CompCert.Int64.repr
  def to_longu (x : CompCert.Float64) : Option CompCert.Int64 :=
    (CompCert.FloatConv.toUnsigned? 64 (ExecFloat.Binary.toModel x)).map CompCert.Int64.repr

  /-- Float from its exact 64-bit pattern (used for clightgen float literals). -/
  def of_bits (b : CompCert.Int64) : CompCert.Float64 :=
    ExecFloat.Binary.ofBits64 b

  /-- Default quiet NaN, `0x7FF8000000000000`. -/
  def default_nan : CompCert.Float64 := ExecFloat.Binary.ofBits64 0x7FF8000000000000

  /-- IEEE `≤` is `<` or `==`. -/
  theorem le_eq_lt_or_eq (x y : CompCert.Float64) :
      decide (x ≤ y) = (decide (x < y) || (x == y)) := by
    show decide (ExecFloat.compareLessEqual x y = true) =
      (decide (ExecFloat.compareLess x y = true) || ExecFloat.compareEqual x y)
    unfold ExecFloat.compareLessEqual ExecFloat.compareLess ExecFloat.compareEqual
    cases ExecFloat.compare x y with
    | none => rfl
    | some o => cases o <;> rfl

  /-- IEEE `==` is symmetric (NaN is unequal to everything in both orders). -/
  theorem beq_comm (x y : CompCert.Float64) : (x == y) = (y == x) := by
    show ExecFloat.compareEqual x y = ExecFloat.compareEqual y x
    unfold ExecFloat.compareEqual
    rw [ExecFloat.Binary.compare_eq_compare_toModel, ExecFloat.Binary.compare_eq_compare_toModel]
    set a := ExecFloat.Binary.toModel x
    set b := ExecFloat.Binary.toModel y
    by_cases hab : Model.isNaN a = true ∨ Model.isNaN b = true
    · rw [(Model.compare_eq_none_iff a b).2 hab, (Model.compare_eq_none_iff b a).2 hab.symm]
    · push Not at hab
      obtain ⟨ea, ha⟩ := Model.exists_toEReal?_of_isNaN_eq_false a (by simpa using hab.1)
      obtain ⟨eb, hb⟩ := Model.exists_toEReal?_of_isNaN_eq_false b (by simpa using hab.2)
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      rw [Model.compare_eq_some_eq_iff_toEReal_eq ha hb,
        Model.compare_eq_some_eq_iff_toEReal_eq hb ha]
      exact eq_comm

  /-- Float from its two 32-bit halves (`hi` = upper word). -/
  def from_words (hi lo : CompCert.Int) : CompCert.Float64 :=
    ExecFloat.Binary.ofBits64 (UInt64.ofNat ((hi.unsigned <<< 32) ||| lo.unsigned))
end CompCert.Float64
