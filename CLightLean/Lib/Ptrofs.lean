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

/- Pointer-sized modular integers (`Ptrofs`).

  This is the CompCert `ptrofs` type: a modular integer whose width depends on the
  architecture (`Archi.ptr64`): 64-bit when `ptr64`, else 32-bit.

  We use "Option B" from the refactor design: a structure carrying the modular
  invariant `val < modulus`.  This gives `DecidableEq` for free (proof irrelevance
  on the `isLt` field), which is what `Vptr`'s `deriving DecidableEq` needs.

  The operations are faithfully modular (`repr` reduces mod `modulus`), so the
  pointer-arithmetic lemmas (`sub_add_opp`, `sub_add_l`, `sub_add_r`) hold
  unconditionally — unlike the old exact-`Int` model, which failed at `INT_MIN`.
-/

import CLightLean.AST
import CLightLean.Lib.Integers

variable [Archi]
namespace Ptrofs

/-- Word size in bits: 64 on a 64-bit target, 32 otherwise. -/
def wordsize : Nat := if Archi.ptr64 then 64 else 32

/-- The modulus `2 ^ wordsize`. -/
def modulus : Nat := 2 ^ wordsize

theorem modulus_pos : 0 < modulus := Nat.pow_pos (by decide)

theorem modulus_pos_int : (0 : Int) < (modulus : Int) := by
  have := @modulus_pos ‹Archi›; exact_mod_cast this

end Ptrofs

/-- Pointer-sized offset: a natural number below `Ptrofs.modulus`. -/
structure Ptrofs [Archi] where
  val : Nat
  isLt : val < Ptrofs.modulus
deriving DecidableEq

namespace Ptrofs

theorem eq_of_val {x y : Ptrofs} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

/-- Reduce an integer modulo `modulus`, producing a canonical `Ptrofs`. -/
def repr (z : Int) : Ptrofs :=
  ⟨(z % (modulus : Int)).toNat, by
    have hpos : (0 : Int) < (modulus : Int) := modulus_pos_int
    have hlt : z % (modulus : Int) < (modulus : Int) := Int.emod_lt_of_pos _ (by omega)
    have hnn : (0 : Int) ≤ z % (modulus : Int) := Int.emod_nonneg _ (by omega)
    omega⟩

/-- The unsigned interpretation: the underlying natural number, as an integer. -/
def unsigned (p : Ptrofs) : Int := (p.val : Int)

/-- The signed (two's-complement) interpretation. -/
def signed (p : Ptrofs) : Int := Int.bmod p.val modulus

def max_unsigned : Int := (modulus : Int) - 1

/-- Half the modulus (`2 ^ (wordsize - 1)`); used to define `max_signed`/`min_signed`. -/
def half_modulus : Int := modulus / 2

def max_signed : Int := half_modulus - 1
def min_signed : Int := - half_modulus

def zero : Ptrofs := repr 0
def one : Ptrofs := repr 1

def add (x y : Ptrofs) : Ptrofs := repr (x.unsigned + y.unsigned)
def sub (x y : Ptrofs) : Ptrofs := repr (x.unsigned - y.unsigned)
def mul (x y : Ptrofs) : Ptrofs := repr (x.unsigned * y.unsigned)
def neg (x : Ptrofs) : Ptrofs := repr (- x.unsigned)

/-- Signed division (truncated toward zero, matching CompCert's `Z.quot`). -/
def divs (x y : Ptrofs) : Ptrofs := repr (Int.tdiv x.signed y.signed)

/-- Build a `Ptrofs` from a 32-bit int, using its signed value (CompCert `of_int`). -/
def of_int (i : CompCert.Int) : Ptrofs := repr i.signed
/-- Build a `Ptrofs` from a 32-bit int, using its unsigned value. -/
def of_intu (i : CompCert.Int) : Ptrofs := repr i.unsigned
/-- Build a `Ptrofs` from a 64-bit int, using its signed value (CompCert `of_int64`). -/
def of_int64 (i : CompCert.Int64) : Ptrofs := repr i.signed
/-- Build a `Ptrofs` from a 64-bit int, using its unsigned value. -/
def of_int64u (i : CompCert.Int64) : Ptrofs := repr i.unsigned

/-- Convert to a 32-bit int (reduces mod 2^32). -/
def to_int (p : Ptrofs) : CompCert.Int := CompCert.Int.repr p.unsigned
/-- Convert to a 64-bit int (reduces mod 2^64). -/
def to_int64 (p : Ptrofs) : CompCert.Int64 := CompCert.Int64.repr p.unsigned

/-- Unsigned comparison. -/
def cmpu (c : comparison) (x y : Ptrofs) : Bool :=
  match c with
  | .Ceq => x.unsigned == y.unsigned
  | .Cne => x.unsigned != y.unsigned
  | .Clt => x.unsigned < y.unsigned
  | .Cle => x.unsigned ≤ y.unsigned
  | .Cgt => x.unsigned > y.unsigned
  | .Cge => x.unsigned ≥ y.unsigned

theorem cmpu_swap (c : comparison) (x y : Ptrofs) :
    cmpu (swap_comparison c) x y = cmpu c y x := by
  rcases c with _ | _ | _ | _ | _ | _
  all_goals simp only [cmpu, swap_comparison]
  · cases h : (x.unsigned == y.unsigned) <;> cases h' : (y.unsigned == x.unsigned) <;> simp_all
  · cases h : (x.unsigned != y.unsigned) <;> cases h' : (y.unsigned != x.unsigned) <;> simp_all

theorem cmpu_negate (c : comparison) (x y : Ptrofs) :
    cmpu (negate_comparison c) x y = !(cmpu c x y) := by
  rcases c with _ | _ | _ | _ | _ | _
  all_goals simp only [cmpu, negate_comparison]
  all_goals (try rfl)
  · cases h : (x.unsigned == y.unsigned) <;> cases h' : (x.unsigned != y.unsigned) <;> simp_all
  · cases h : decide (x.unsigned < y.unsigned) <;> cases h' : decide (x.unsigned ≥ y.unsigned) <;>
      simp_all [decide_eq_true_eq]; omega
  · cases h : decide (x.unsigned ≤ y.unsigned) <;> cases h' : decide (x.unsigned > y.unsigned) <;>
      simp_all [decide_eq_true_eq]; omega
  · cases h : decide (x.unsigned > y.unsigned) <;> cases h' : decide (x.unsigned ≤ y.unsigned) <;>
      simp_all [decide_eq_true_eq]; omega
  · cases h : decide (x.unsigned ≥ y.unsigned) <;> cases h' : decide (x.unsigned < y.unsigned) <;>
      simp_all [decide_eq_true_eq]; omega

/-! ### Section 3 lemma surface -/

/-- `unsigned` lands in `[0, modulus)`. -/
theorem unsigned_range (x : Ptrofs) : 0 ≤ unsigned x ∧ unsigned x < (modulus : Int) := by
  refine ⟨by simp [unsigned], ?_⟩
  have := x.isLt
  simp only [unsigned]
  exact_mod_cast this

theorem unsigned_nonneg (x : Ptrofs) : 0 ≤ unsigned x := (unsigned_range x).1

/-- General bridge: `unsigned (repr z) = z % modulus`. -/
@[simp] theorem unsigned_repr_eq (z : Int) : unsigned (repr z) = z % (modulus : Int) := by
  simp only [unsigned, repr]
  have hnn : (0 : Int) ≤ z % (modulus : Int) :=
    Int.emod_nonneg _ (by have := modulus_pos_int; omega)
  rw [Int.toNat_of_nonneg hnn]

/-- `unsigned x` is already reduced. -/
theorem unsigned_emod (x : Ptrofs) : unsigned x % (modulus : Int) = unsigned x := by
  have ⟨h0, h1⟩ := unsigned_range x
  exact Int.emod_eq_of_lt h0 h1

/-- Two `Ptrofs` are equal iff their `unsigned` values agree. -/
theorem eq_iff_unsigned {x y : Ptrofs} : x = y ↔ unsigned x = unsigned y := by
  constructor
  · intro h; rw [h]
  · intro h; apply eq_of_val; simpa [unsigned] using h

/-- `repr a = repr b` iff `a ≡ b [mod modulus]`. -/
theorem repr_eq_iff {a b : Int} : repr a = repr b ↔ a % (modulus : Int) = b % (modulus : Int) := by
  rw [eq_iff_unsigned, unsigned_repr_eq, unsigned_repr_eq]

/-- `repr (unsigned x) = x`: the canonical round-trip. -/
@[simp] theorem repr_unsigned (x : Ptrofs) : repr (unsigned x) = x := by
  rw [eq_iff_unsigned, unsigned_repr_eq, unsigned_emod]

/-- `unsigned (repr z) = z` when `z` is already in range. -/
theorem unsigned_repr (z : Int) (h : 0 ≤ z ∧ z ≤ max_unsigned) : unsigned (repr z) = z := by
  obtain ⟨h0, h1⟩ := h
  rw [unsigned_repr_eq]
  simp only [max_unsigned] at h1
  exact Int.emod_eq_of_lt h0 (by omega)

/-- `repr` is a `+`-homomorphism. -/
theorem repr_add (a b : Int) : repr (a + b) = add (repr a) (repr b) := by
  rw [add, eq_iff_unsigned]
  simp only [unsigned_repr_eq]
  exact Int.add_emod a b modulus

theorem repr_sub (a b : Int) : repr (a - b) = sub (repr a) (repr b) := by
  rw [sub, eq_iff_unsigned]
  simp only [unsigned_repr_eq]
  exact Int.sub_emod a b modulus

theorem repr_neg (a : Int) : repr (-a) = neg (repr a) := by
  rw [neg, eq_iff_unsigned]
  simp only [unsigned_repr_eq]
  -- Need: (-a) % m = (-(a % m)) % m
  have key : -a = -(a / (modulus : Int)) * (modulus : Int) + (-(a % (modulus : Int))) := by
    have h : a % (modulus : Int) = a - (modulus : Int) * (a / (modulus : Int)) := Int.emod_def a (modulus : Int)
    rw [h]; ring
  rw [key]
  rw [show -(a / (modulus : Int)) * (modulus : Int) + -(a % (modulus : Int)) =
          -(a % (modulus : Int)) + -(a / (modulus : Int)) * (modulus : Int) by ring]
  rw [Int.add_mul_emod_self_right]

@[simp] theorem add_commut (x y : Ptrofs) : add x y = add y x := by
  simp only [add]; rw [Int.add_comm]

theorem add_assoc (x y z : Ptrofs) : add (add x y) z = add x (add y z) := by
  rw [← repr_unsigned x, ← repr_unsigned y, ← repr_unsigned z]
  simp only [← repr_add]
  rw [Int.add_assoc]

@[simp] theorem add_zero (x : Ptrofs) : add x zero = x := by
  conv_lhs => rw [zero, ← repr_unsigned x, ← repr_add]
  rw [Int.add_zero, repr_unsigned]

@[simp] theorem zero_add (x : Ptrofs) : add zero x = x := by
  rw [add_commut, add_zero]

/-- The pointer-arithmetic blocker, now TRUE: `sub x y = add x (neg y)`. -/
theorem sub_add_opp (x y : Ptrofs) : sub x y = add x (neg y) := by
  rw [← repr_unsigned x, ← repr_unsigned y]
  rw [← repr_neg, ← repr_sub, ← repr_add]
  congr 1


@[simp] theorem neg_involutive (x : Ptrofs) : neg (neg x) = x := by
  rw [← repr_unsigned x, ← repr_neg, ← repr_neg]
  simp [neg_neg]

theorem neg_repr (z : Int) : neg (repr z) = repr (-z) := (repr_neg z).symm

/-- `add`-rearrangement: `sub (add x (repr i)) y = add (sub x y) (repr i)`. -/
theorem sub_add_l (x y : Ptrofs) (i : Int) :
    sub (add x (repr i)) y = add (sub x y) (repr i) := by
  rw [← repr_unsigned x, ← repr_unsigned y]
  simp only [← repr_add, ← repr_sub]
  rw [repr_eq_iff]
  congr 1
  ring

/-- `add`-rearrangement: `sub x (add y (repr i)) = add (sub x y) (repr (-i))`. -/
theorem sub_add_r (x y : Ptrofs) (i : Int) :
    sub x (add y (repr i)) = add (sub x y) (repr (-i)) := by
  rw [← repr_unsigned x, ← repr_unsigned y]
  simp only [← repr_add, ← repr_sub]
  rw [repr_eq_iff]
  congr 1
  ring

/-- Cancel common offset: `sub (add x (repr i)) (add y (repr i)) = sub x y`. -/
theorem sub_add_cancel (x y : Ptrofs) (i : Int) :
    sub (add x (repr i)) (add y (repr i)) = sub x y := by
  rw [← repr_unsigned x, ← repr_unsigned y]
  simp only [← repr_add, ← repr_sub]
  rw [repr_eq_iff]
  ring_nf

/-! ### Bridge to `CompCert.Int` / `CompCert.Int64` offsets

  These relate building a `Ptrofs` from an integer's signed value to `repr` of
  that signed value.  The pointer-arithmetic proofs in `Values.lean` need to move
  `.signed` in and out of `repr`.
-/

/-- `add x (of_int i) = repr (unsigned x + i.signed)`. -/
theorem add_of_int (x : Ptrofs) (i : CompCert.Int) :
    add x (of_int i) = repr (unsigned x + i.signed) := by
  rw [of_int, ← repr_unsigned x, ← repr_add, repr_eq_iff]
  simp only [unsigned_repr_eq]
  have : x.unsigned % (modulus : Int) = x.unsigned := unsigned_emod x
  rw [this]

theorem sub_of_int (x : Ptrofs) (i : CompCert.Int) :
    sub x (of_int i) = repr (unsigned x - i.signed) := by
  rw [of_int, ← repr_unsigned x, ← repr_sub, repr_eq_iff]
  simp only [unsigned_repr_eq]
  have : x.unsigned % (modulus : Int) = x.unsigned := unsigned_emod x
  rw [this]

theorem add_of_int64 (x : Ptrofs) (i : CompCert.Int64) :
    add x (of_int64 i) = repr (unsigned x + i.signed) := by
  rw [of_int64, ← repr_unsigned x, ← repr_add, repr_eq_iff]
  simp only [unsigned_repr_eq]
  have : x.unsigned % (modulus : Int) = x.unsigned := unsigned_emod x
  rw [this]

theorem sub_of_int64 (x : Ptrofs) (i : CompCert.Int64) :
    sub x (of_int64 i) = repr (unsigned x - i.signed) := by
  rw [of_int64, ← repr_unsigned x, ← repr_sub, repr_eq_iff]
  simp only [unsigned_repr_eq]
  have : x.unsigned % (modulus : Int) = x.unsigned := unsigned_emod x
  rw [this]

/-! ### Modulus width facts (by architecture) -/

theorem wordsize_eq_32 (h : Archi.ptr64 = false) : wordsize = 32 := by
  simp [wordsize, h]

theorem wordsize_eq_64 (h : Archi.ptr64 = true) : wordsize = 64 := by
  simp [wordsize, h]

theorem modulus_eq_pow32 (h : Archi.ptr64 = false) : (modulus : Int) = (2 ^ 32 : Int) := by
  simp [modulus, wordsize_eq_32 h]

theorem modulus_eq_pow64 (h : Archi.ptr64 = true) : (modulus : Int) = (2 ^ 64 : Int) := by
  simp [modulus, wordsize_eq_64 h]

/-- `2^32` always divides the modulus (which is `2^32` or `2^64`). -/
theorem pow32_dvd_modulus : (2 ^ 32 : Int) ∣ (modulus : Int) := by
  by_cases h : Archi.ptr64
  · rw [modulus_eq_pow64 h]; exact ⟨2 ^ 32, by norm_num⟩
  · simp only [Bool.not_eq_true] at h; rw [modulus_eq_pow32 h]

/-- `2^64` always divides the modulus when `ptr64` (modulus is exactly `2^64`). -/
theorem pow64_dvd_modulus (h : Archi.ptr64 = true) : (2 ^ 64 : Int) ∣ (modulus : Int) := by
  rw [modulus_eq_pow64 h]

/-! ### Bridges used by pointer arithmetic in `Values.lean` -/

/-- Under 32-bit pointers, `of_int` commutes with negation. -/
theorem of_int_neg (h : Archi.ptr64 = false) (y : CompCert.Int) :
    of_int (CompCert.Int.neg y) = neg (of_int y) := by
  rw [of_int, of_int, ← repr_neg, repr_eq_iff]
  rw [modulus_eq_pow32 h]
  have := CompCert.Int.neg_signed_mod y
  simpa using this

/-- Under 64-bit pointers, `of_int64` commutes with negation. -/
theorem of_int64_neg (h : Archi.ptr64 = true) (y : CompCert.Int64) :
    of_int64 (CompCert.Int64.neg y) = neg (of_int64 y) := by
  rw [of_int64, of_int64, ← repr_neg, repr_eq_iff]
  rw [modulus_eq_pow64 h]
  have := CompCert.Int64.neg_signed_mod y
  simpa using this

/-- Under 32-bit pointers, `of_int` commutes with addition. -/
theorem of_int_add (h : Archi.ptr64 = false) (i j : CompCert.Int) :
    of_int (CompCert.Int.add i j) = add (of_int i) (of_int j) := by
  rw [of_int, of_int, of_int, ← repr_add, repr_eq_iff]
  rw [modulus_eq_pow32 h]
  have := CompCert.Int.add_signed_mod i j
  simpa using this

/-- Under 64-bit pointers, `of_int64` commutes with addition. -/
theorem of_int64_add (h : Archi.ptr64 = true) (i j : CompCert.Int64) :
    of_int64 (CompCert.Int64.add i j) = add (of_int64 i) (of_int64 j) := by
  rw [of_int64, of_int64, of_int64, ← repr_add, repr_eq_iff]
  rw [modulus_eq_pow64 h]
  have := CompCert.Int64.add_signed_mod i j
  simpa using this

/-- Under no-overflow, `unsigned (add ofs (repr δ)) = unsigned ofs + δ`. -/
theorem unsigned_add_repr_of_no_overflow (ofs : Ptrofs) (delta : Int)
    (h : 0 ≤ unsigned ofs + delta ∧ unsigned ofs + delta ≤ max_unsigned) :
    unsigned (add ofs (repr delta)) = unsigned ofs + delta := by
  obtain ⟨hlo, hhi⟩ := h
  rw [add, unsigned_repr_eq, unsigned_repr_eq]
  -- goal: (unsigned ofs + delta % modulus) % modulus = unsigned ofs + delta
  have hstep : (unsigned ofs + delta % (modulus : Int)) % (modulus : Int)
             = (unsigned ofs + delta) % (modulus : Int) := by
    conv_rhs => rw [Int.add_emod]
    conv_lhs => rw [Int.add_emod]
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [hstep]
  have hmax : max_unsigned = (modulus : Int) - 1 := rfl
  rw [hmax] at hhi
  exact Int.emod_eq_of_lt hlo (by omega)

/-- Adding the same in-range delta to both offsets preserves unsigned comparison. -/
theorem cmpu_add_shift (c : comparison) (ofs1 ofs2 : Ptrofs) (delta : Int)
    (h1 : 0 ≤ unsigned ofs1 + delta ∧ unsigned ofs1 + delta ≤ max_unsigned)
    (h2 : 0 ≤ unsigned ofs2 + delta ∧ unsigned ofs2 + delta ≤ max_unsigned) :
    cmpu c (add ofs1 (repr delta)) (add ofs2 (repr delta)) = cmpu c ofs1 ofs2 := by
  have e1 : unsigned (add ofs1 (repr delta)) = unsigned ofs1 + delta :=
    unsigned_add_repr_of_no_overflow ofs1 delta h1
  have e2 : unsigned (add ofs2 (repr delta)) = unsigned ofs2 + delta :=
    unsigned_add_repr_of_no_overflow ofs2 delta h2
  rcases c with _ | _ | _ | _ | _ | _ <;>
    simp only [cmpu, e1, e2, decide_eq_decide] <;>
    (try omega) <;>
    (try (rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, bne_iff_ne]; omega))

theorem to_int_add_of_int (p : Ptrofs) (i : CompCert.Int) :
    to_int (add p (of_int i)) = to_int p + i := by
  rw [to_int, to_int, add_of_int, unsigned_repr_eq]
  rw [CompCert.Int.repr_congr
      (show (unsigned p + i.signed) % (modulus : Int) % (2 ^ 32 : Int)
          = (unsigned p + i.signed) % (2 ^ 32 : Int) from
        Int.emod_emod_of_dvd _ pow32_dvd_modulus)]
  exact CompCert.Int.repr_add_signed (unsigned p) i

/-- `to_int64` of a shifted pointer offset. -/
theorem to_int64_add_of_int64 (h : Archi.ptr64 = true) (p : Ptrofs) (i : CompCert.Int64) :
    to_int64 (add p (of_int64 i)) = to_int64 p + i := by
  rw [to_int64, to_int64, add_of_int64, unsigned_repr_eq]
  rw [CompCert.Int64.repr_congr
      (show (unsigned p + i.signed) % (modulus : Int) % (2 ^ 64 : Int)
          = (unsigned p + i.signed) % (2 ^ 64 : Int) from
        Int.emod_emod_of_dvd _ (pow64_dvd_modulus h))]
  exact CompCert.Int64.repr_add_signed (unsigned p) i

end Ptrofs
