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

/- Thin wrappers around Lean's native fixed-width integer types to provide
   CompCert-compatible API. Uses native UInt32/UInt64 underneath for performance. -/

import Std.Tactic.BVDecide
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise

/-- Power of 2: two_p n = 2^n -/
def two_p (n : Nat) : Int := 2^n

-- Comparison operators
inductive comparison : Type where
  | Ceq  -- equal
  | Cne  -- not equal
  | Clt  -- less than
  | Cle  -- less than or equal
  | Cgt  -- greater than
  | Cge  -- greater than or equal
  deriving DecidableEq, Repr

-- Negate a comparison (flip the boolean result)
def negate_comparison (c : comparison) : comparison :=
  match c with
  | .Ceq => .Cne
  | .Cne => .Ceq
  | .Clt => .Cge
  | .Cle => .Cgt
  | .Cgt => .Cle
  | .Cge => .Clt

-- Swap operands of a comparison (flip < and >)
def swap_comparison (c : comparison) : comparison :=
  match c with
  | .Ceq => .Ceq
  | .Cne => .Cne
  | .Clt => .Cgt
  | .Cle => .Cge
  | .Cgt => .Clt
  | .Cge => .Cle

-- Type aliases
abbrev CompCert.Int := UInt32
abbrev CompCert.Int64 := UInt64

-- DecidableEq instances (inherited from UInt32/UInt64)
instance : DecidableEq CompCert.Int := inferInstance
instance : DecidableEq CompCert.Int64 := inferInstance

-- Helper lemmas for BitVec
theorem BitVec.rotateLeft_zero {w : Nat} (x : BitVec w) : x.rotateLeft 0 = x := by
  unfold BitVec.rotateLeft
  simp
  unfold BitVec.rotateLeftAux
  simp
  rw [BitVec.ushiftRight_eq_zero]
  simp
  apply Nat.le_refl

namespace CompCert.Int
  -- Conversion operations
  def unsigned (x : CompCert.Int) : Nat := x.toNat
  def signed (x : CompCert.Int) : _root_.Int := x.toBitVec.toInt
  def repr (z : _root_.Int) : CompCert.Int := UInt32.ofInt z

  -- Constants
  def zero : CompCert.Int := 0
  def one : CompCert.Int := 1
  def mone : CompCert.Int := UInt32.ofInt (-1)
  def iwordsize : CompCert.Int := 32
  def min_signed : _root_.Int := -2147483648
  def max_signed : _root_.Int := 2147483647
  def max_unsigned : _root_.Int := 4294967295

  -- Arithmetic operations (direct delegation)
  def add := UInt32.add
  def sub := UInt32.sub
  def mul := UInt32.mul
  def neg (x : CompCert.Int) : CompCert.Int := UInt32.ofInt (-(x.toNat : _root_.Int))

  -- Advanced arithmetic
  def mulhs (x y : CompCert.Int) : CompCert.Int :=
    -- Signed multiply high: (signed(x) * signed(y)) >> 32
    let prod := x.signed * y.signed
    repr (prod / 4294967296)

  def mulhu (x y : CompCert.Int) : CompCert.Int :=
    -- Unsigned multiply high: (unsigned(x) * unsigned(y)) >> 32
    let prod := (x.unsigned : _root_.Int) * (y.unsigned : _root_.Int)
    repr (prod / 4294967296)

  def divs (x y : CompCert.Int) : CompCert.Int :=
    -- Signed division (caller must check for div by zero and overflow)
    -- Uses tdiv (toward zero) to match CompCert semantics
    repr (Int.tdiv x.signed y.signed)

  theorem repr_signed (x : CompCert.Int) : repr (x.signed) = x := by
    unfold repr signed
    -- Goal: UInt32.ofInt (x.toBitVec.toInt) = x
    -- (UInt32.ofInt z).toBitVec = BitVec.ofInt 32 z, then BitVec.ofInt_toInt closes it.
    rw [UInt32.eq_iff_toBitVec_eq]
    have hbv : (UInt32.ofInt (x.toBitVec.toInt)).toBitVec = BitVec.ofInt 32 (x.toBitVec.toInt) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : (UInt32.ofInt (x.toBitVec.toInt)).toBitVec
                  = BitVec.ofNat 32 ((x.toBitVec.toInt % 2^32).toNat) := rfl
      simp only [h1, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    rw [hbv]
    exact BitVec.ofInt_toInt

  -- Helper lemmas for repr as a homomorphism mod 2^32
  theorem repr_sub_hom (a b : _root_.Int) :
      repr (a - b) = UInt32.sub (repr a) (repr b) := by
    unfold repr
    apply UInt32.toNat.inj
    -- Expand uint32_ofInt_toNat inline
    show (UInt32.ofInt (a - b)).toNat = (UInt32.ofInt a - UInt32.ofInt b).toNat
    have h1 : (UInt32.ofInt (a - b)).toNat = ((a - b) % (2^32 : _root_.Int)).toNat := by
      have hlt : ((a - b) % (2^32 : _root_.Int)) < (2^32 : _root_.Int) :=
        Int.emod_lt_of_pos _ (by omega)
      have hbound : ((a - b) % (2^32 : _root_.Int)).toNat < 2^32 := by omega
      show (UInt32.ofInt (a - b)).toBitVec.toNat = _
      have : (UInt32.ofInt (a - b)).toBitVec = BitVec.ofNat 32 (((a - b) % 2^32).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h2 : (UInt32.ofInt a).toNat = (a % (2^32 : _root_.Int)).toNat := by
      have hbound : (a % (2^32 : _root_.Int)).toNat < 2^32 := by
        have hlt : (a % (2^32 : _root_.Int)) < (2^32 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt32.ofInt a).toBitVec.toNat = _
      have : (UInt32.ofInt a).toBitVec = BitVec.ofNat 32 ((a % 2^32).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h3 : (UInt32.ofInt b).toNat = (b % (2^32 : _root_.Int)).toNat := by
      have hbound : (b % (2^32 : _root_.Int)).toNat < 2^32 := by
        have hlt : (b % (2^32 : _root_.Int)) < (2^32 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt32.ofInt b).toBitVec.toNat = _
      have : (UInt32.ofInt b).toBitVec = BitVec.ofNat 32 ((b % 2^32).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    rw [h1, UInt32.toNat_sub, h2, h3]
    have ha : 0 ≤ a % (2^32 : _root_.Int) := Int.emod_nonneg _ (by omega)
    have hb : 0 ≤ b % (2^32 : _root_.Int) := Int.emod_nonneg _ (by omega)
    have hac : a % (2^32 : _root_.Int) < 2^32 := Int.emod_lt_of_pos _ (by omega)
    have hbc : b % (2^32 : _root_.Int) < 2^32 := Int.emod_lt_of_pos _ (by omega)
    omega

  theorem repr_mul_hom (a b : _root_.Int) :
      repr (a * b) = UInt32.mul (repr a) (repr b) := by
    unfold repr
    apply UInt32.toNat.inj
    show (UInt32.ofInt (a * b)).toNat = (UInt32.ofInt a * UInt32.ofInt b).toNat
    have h1 : (UInt32.ofInt (a * b)).toNat = ((a * b) % (2^32 : _root_.Int)).toNat := by
      have hbound : ((a * b) % (2^32 : _root_.Int)).toNat < 2^32 := by
        have hlt : ((a * b) % (2^32 : _root_.Int)) < (2^32 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt32.ofInt (a * b)).toBitVec.toNat = _
      have : (UInt32.ofInt (a * b)).toBitVec = BitVec.ofNat 32 (((a * b) % 2^32).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h2 : (UInt32.ofInt a).toNat = (a % (2^32 : _root_.Int)).toNat := by
      have hbound : (a % (2^32 : _root_.Int)).toNat < 2^32 := by
        have hlt : (a % (2^32 : _root_.Int)) < (2^32 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt32.ofInt a).toBitVec.toNat = _
      have : (UInt32.ofInt a).toBitVec = BitVec.ofNat 32 ((a % 2^32).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h3 : (UInt32.ofInt b).toNat = (b % (2^32 : _root_.Int)).toNat := by
      have hbound : (b % (2^32 : _root_.Int)).toNat < 2^32 := by
        have hlt : (b % (2^32 : _root_.Int)) < (2^32 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt32.ofInt b).toBitVec.toNat = _
      have : (UInt32.ofInt b).toBitVec = BitVec.ofNat 32 ((b % 2^32).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    rw [h1, UInt32.toNat_mul, h2, h3]
    -- Goal: ((a * b) % 2^32).toNat = ((a % 2^32).toNat * (b % 2^32).toNat) % 2^32
    have ha : 0 ≤ a % (2^32 : _root_.Int) := Int.emod_nonneg _ (by omega)
    have hb : 0 ≤ b % (2^32 : _root_.Int) := Int.emod_nonneg _ (by omega)
    -- Key: (a * b) % 2^32 = (a%2^32) * (b%2^32) % 2^32
    have h_mod_mul : ((a * b) % (2^32 : _root_.Int)) = ((a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int))) % (2^32 : _root_.Int) := by
      rw [Int.mul_emod]
    rw [h_mod_mul]
    -- Now show ((...) % 2^32).toNat = ((a%2^32).toNat * (b%2^32).toNat) % 2^32
    have hprod_nn : 0 ≤ ((a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int))) % (2^32 : _root_.Int) :=
      Int.emod_nonneg _ (by omega)
    show ((a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int)) % (2^32 : _root_.Int)).toNat
          = ((a % (2^32 : _root_.Int)).toNat * (b % (2^32 : _root_.Int)).toNat) % 2^32
    -- Convert both products to Nat
    have ha_toNat_eq : (a % (2^32 : _root_.Int)).toNat = (a % (2^32 : _root_.Int)).toNat := rfl
    have hb_toNat_eq : (b % (2^32 : _root_.Int)).toNat = (b % (2^32 : _root_.Int)).toNat := rfl
    -- Use Int.toNat_mul for the product
    have h_prod : ((a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int))).toNat
                    = (a % (2^32 : _root_.Int)).toNat * (b % (2^32 : _root_.Int)).toNat := by
      exact Int.toNat_mul (by omega : 0 ≤ a % (2^32 : _root_.Int)) (by omega : 0 ≤ b % (2^32 : _root_.Int))
    -- Use Int.toNat_emod for the mod
    have : ((a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int)) % (2^32 : _root_.Int)).toNat
            = ((a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int))).toNat % 2^32 := by
      have hx : 0 ≤ (a % (2^32 : _root_.Int)) * (b % (2^32 : _root_.Int)) := Int.mul_nonneg ha hb
      have hy : 0 ≤ (2^32 : _root_.Int) := by decide
      exact Int.toNat_emod hx hy
    rw [this, h_prod]


  -- Private helper lemmas for bridging UInt32/Int/Nat conversions
  -- General bridge lemma: the Nat value of `UInt32.ofInt z` is `(z % 2^32).toNat`.
  -- This works because `UInt32.ofInt z` reduces to `BitVec.ofNat 32 ((z % 2^32).toNat)`,
  -- and `(z % 2^32).toNat < 2^32`, so the extra `% 2^32` is the identity.
  private lemma uint32_ofInt_toNat (z : _root_.Int) :
      (UInt32.ofInt z).toNat = (z % (2^32 : _root_.Int)).toNat := by
    have hlt : (z % (2^32 : _root_.Int)) < (2^32 : _root_.Int) :=
      Int.emod_lt_of_pos z (by omega)
    have hnn : (0 : _root_.Int) ≤ z % (2^32 : _root_.Int) :=
      Int.emod_nonneg z (by omega)
    -- toNat of the emod is < 2^32
    have hbound : (z % (2^32 : _root_.Int)).toNat < 2^32 := by
      omega
    show (UInt32.ofInt z).toBitVec.toNat = _
    have h1 : (UInt32.ofInt z).toBitVec = BitVec.ofNat 32 ((z % 2^32).toNat) := rfl
    rw [h1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hbound

  -- Bridge: `UInt32.ofInt z` and `BitVec.ofInt 32 z` agree at the `toBitVec` level.
  private lemma uint32_ofInt_toBitVec (z : _root_.Int) :
      (UInt32.ofInt z).toBitVec = BitVec.ofInt 32 z := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (UInt32.ofInt z).toBitVec = BitVec.ofNat 32 ((z % 2^32).toNat) := rfl
    simp only [h1, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

  -- The Nat value of `neg x` is `(-(x.toNat : Int) % 2^32).toNat`.
  private lemma neg_toNat (x : CompCert.Int) :
      (neg x).toNat = (-(x.toNat : _root_.Int) % (2^32 : _root_.Int)).toNat := by
    unfold neg
    exact uint32_ofInt_toNat _

  theorem divs_one (x : CompCert.Int) : divs x one = x := by
    unfold divs
    have h1 : (one : CompCert.Int).signed = 1 := by decide
    rw [h1, Int.tdiv_one, repr_signed]

  def mods (x y : CompCert.Int) : CompCert.Int :=
    -- Signed modulo (tmod, matches tdiv)
    repr (Int.tmod x.signed y.signed)

  theorem mods_divs_identity (x y : CompCert.Int) (_hy : y ≠ zero) :
      mods x y = sub x (mul (divs x y) y) := by
    unfold mods divs sub mul
    -- Goal: repr (x.signed.tmod y.signed) = UInt32.sub x (UInt32.mul (repr (x.signed.tdiv y.signed)) y)
    -- Use tdiv/tmod identity: x.signed.tmod y.signed = x.signed - y.signed * (x.signed.tdiv y.signed)
    have htdiv : Int.tmod x.signed y.signed = x.signed - y.signed * (Int.tdiv x.signed y.signed) := Int.tmod_def _ _
    rw [htdiv]
    -- Push repr through sub and mul using homomorphism lemmas
    rw [repr_sub_hom, repr_mul_hom]
    -- Now need to show UInt32.sub (repr x.signed) (UInt32.mul (repr y.signed) (repr (x.signed.tdiv y.signed)))
    --                = UInt32.sub x (UInt32.mul (repr (x.signed.tdiv y.signed)) y)
    -- Use repr_signed to simplify repr x.signed = x, repr y.signed = y
    rw [repr_signed, repr_signed]
    -- Now: UInt32.sub x (UInt32.mul y (repr (x.signed.tdiv y.signed))) = UInt32.sub x (UInt32.mul (repr (x.signed.tdiv y.signed)) y)
    -- Apply commutativity of UInt32.mul
    congr 1
    exact UInt32.mul_comm _ _
  def divu (x y : CompCert.Int) : CompCert.Int :=
    -- Unsigned division
    repr ((x.unsigned : _root_.Int) / (y.unsigned : _root_.Int))

  theorem repr_unsigned (x : CompCert.Int) : repr (x.unsigned) = x := by
    unfold repr unsigned
    apply UInt32.toNat.inj
    rw [uint32_ofInt_toNat]
    have h : x.toNat < 2^32 := x.toBitVec.isLt
    have hcast : ((x.toNat : _root_.Int) % (2^32 : _root_.Int)).toNat = x.toNat := by
      have : (x.toNat : _root_.Int) % (2^32 : _root_.Int) = (x.toNat : _root_.Int) := by
        apply Int.emod_eq_of_lt (by omega : (0 : _root_.Int) ≤ ↑(x.toNat)) (by exact_mod_cast h)
      rw [this]; exact Int.toNat_natCast _
    exact hcast

  theorem divu_one (x : CompCert.Int) : divu x one = x := by
    unfold divu
    have h1 : ((one : CompCert.Int).unsigned : _root_.Int) = 1 := by decide
    rw [h1, Int.ediv_one, repr_unsigned]

  def modu (x y : CompCert.Int) : CompCert.Int :=
    -- Unsigned modulo
    repr ((x.unsigned : _root_.Int) % (y.unsigned : _root_.Int))

  theorem modu_divu_identity (x y : CompCert.Int) (_hy : y ≠ zero) :
      modu x y = sub x (mul (divu x y) y) := by
    unfold modu divu sub mul
    -- Goal: repr ((x.unsigned : Int) % (y.unsigned : Int))
    --     = UInt32.sub x (UInt32.mul (repr ((x.unsigned : Int) / (y.unsigned : Int))) y)
    have heuc : (x.unsigned : _root_.Int) % (y.unsigned : _root_.Int)
                = (x.unsigned : _root_.Int) - (y.unsigned : _root_.Int) * ((x.unsigned : _root_.Int) / (y.unsigned : _root_.Int)) :=
      Int.emod_def _ _
    rw [heuc]
    rw [repr_sub_hom, repr_mul_hom]
    rw [repr_unsigned, repr_unsigned]
    congr 1
    exact UInt32.mul_comm _ _
  def add_carry (x y cin : CompCert.Int) : CompCert.Int :=
    -- Add with carry
    let sum := (x.unsigned : _root_.Int) + (y.unsigned : _root_.Int) + (cin.unsigned : _root_.Int)
    repr sum

  def sub_overflow (x y z : CompCert.Int) : CompCert.Int :=
    -- Subtraction overflow detection
    let res := x.signed - y.signed - z.signed
    if res < min_signed || res > max_signed then one else zero

  def negative (x : CompCert.Int) : CompCert.Int :=
    -- Test if negative (sign bit)
    if x.signed < 0 then one else zero

  -- Comparison operations
  def eq (x y : CompCert.Int) : Bool := x == y
  def lt (x y : CompCert.Int) : Bool := x.signed < y.signed  -- signed less than
  def ltu (x y : CompCert.Int) : Bool := x < y  -- unsigned less than

  def cmp (c : comparison) (x y : CompCert.Int) : Bool :=
    match c with
    | .Ceq => x.signed == y.signed
    | .Cne => x.signed != y.signed
    | .Clt => x.signed < y.signed
    | .Cle => x.signed <= y.signed
    | .Cgt => x.signed > y.signed
    | .Cge => x.signed >= y.signed

  theorem cmp_swap (c : comparison) (x y : CompCert.Int) :
      cmp (swap_comparison c) x y = cmp c y x := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmp, swap_comparison]
    -- Ceq
    · cases h : (x.signed == y.signed) <;> cases h' : (y.signed == x.signed) <;> simp_all
    -- Cne
    · cases h : (x.signed != y.signed) <;> cases h' : (y.signed != x.signed) <;> simp_all

  theorem cmp_negate (c : comparison) (x y : CompCert.Int) :
      cmp (negate_comparison c) x y = !(cmp c x y) := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmp, negate_comparison]
    all_goals (try rfl)
    -- Ceq
    · cases h : (x.signed == y.signed) <;> cases h' : (x.signed != y.signed) <;> simp_all
    -- Clt
    · cases h : decide (x.signed < y.signed) <;> cases h' : decide (x.signed ≥ y.signed) <;> simp_all [decide_eq_true_eq]; omega
    -- Cle
    · cases h : decide (x.signed ≤ y.signed) <;> cases h' : decide (x.signed > y.signed) <;> simp_all [decide_eq_true_eq]; omega
    -- Cgt
    · cases h : decide (x.signed > y.signed) <;> cases h' : decide (x.signed ≤ y.signed) <;> simp_all [decide_eq_true_eq]; omega
    -- Cge
    · cases h : decide (x.signed ≥ y.signed) <;> cases h' : decide (x.signed < y.signed) <;> simp_all [decide_eq_true_eq]; omega

  def cmpu (c : comparison) (x y : CompCert.Int) : Bool :=
    match c with
    | .Ceq => x.unsigned == y.unsigned
    | .Cne => x.unsigned != y.unsigned
    | .Clt => x.unsigned < y.unsigned
    | .Cle => x.unsigned <= y.unsigned
    | .Cgt => x.unsigned > y.unsigned
    | .Cge => x.unsigned >= y.unsigned

  theorem cmpu_swap (c : comparison) (x y : CompCert.Int) :
      cmpu (swap_comparison c) x y = cmpu c y x := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmpu, swap_comparison]
    -- Ceq
    · cases h : (x.unsigned == y.unsigned) <;> cases h' : (y.unsigned == x.unsigned) <;> simp_all
    -- Cne
    · cases h : (x.unsigned != y.unsigned) <;> cases h' : (y.unsigned != x.unsigned) <;> simp_all

  theorem cmpu_negate (c : comparison) (x y : CompCert.Int) :
      cmpu (negate_comparison c) x y = !(cmpu c x y) := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmpu, negate_comparison]
    all_goals (try rfl)
    -- Ceq
    · cases h : (x.unsigned == y.unsigned) <;> cases h' : (x.unsigned != y.unsigned) <;> simp_all
    -- Clt
    · cases h : decide (x.unsigned < y.unsigned) <;> cases h' : decide (x.unsigned ≥ y.unsigned) <;> simp_all [decide_eq_true_eq]; omega
    -- Cle
    · cases h : decide (x.unsigned ≤ y.unsigned) <;> cases h' : decide (x.unsigned > y.unsigned) <;> simp_all [decide_eq_true_eq]; omega
    -- Cgt
    · cases h : decide (x.unsigned > y.unsigned) <;> cases h' : decide (x.unsigned ≤ y.unsigned) <;> simp_all [decide_eq_true_eq]; omega
    -- Cge
    · cases h : decide (x.unsigned ≥ y.unsigned) <;> cases h' : decide (x.unsigned < y.unsigned) <;> simp_all [decide_eq_true_eq]; omega

  -- Bitwise operations
  def and := UInt32.land
  def or := UInt32.lor
  def xor := UInt32.xor
  def not (x : CompCert.Int) : CompCert.Int := xor x mone

  -- Shift operations
  def shl := UInt32.shiftLeft
  def shru := UInt32.shiftRight

  def shr (x y : CompCert.Int) : CompCert.Int :=
    -- Arithmetic shift right (sign-extending)
    let shamt := y.toNat % 32
    repr (x.signed >>> shamt)

  def shr_carry (x y : CompCert.Int) : CompCert.Int :=
    -- Carry bit for rounding: 1 iff x < 0 and some low bits are shifted out.
    if x.signed < 0 && (x.unsigned &&& ((1 <<< (y.toNat % 32)) - 1)) != 0 then one else zero

  def shrx (x y : CompCert.Int) : CompCert.Int :=
    -- Signed division by 2^y (rounding towards zero)
    let shamt := y.toNat
    if x.signed >= 0 then
      repr (x.signed >>> shamt)
    else
      -- Round towards zero for negative numbers
      let round := (1 <<< shamt) - 1
      repr ((x.signed + round) >>> shamt)

  -- Rotate operations
  def rol (x y : CompCert.Int) : CompCert.Int :=
    -- Rotate left
    let n := y.toNat % 32
    let bv := x.toBitVec
    UInt32.ofInt (bv.rotateLeft n |>.toInt)

  def ror (x y : CompCert.Int) : CompCert.Int :=
    -- Rotate right
    let n := y.toNat % 32
    let bv := x.toBitVec
    UInt32.ofInt (bv.rotateRight n |>.toInt)

  def rolm (x amount mask : CompCert.Int) : CompCert.Int :=
    -- Rotate left and mask
    and (rol x amount) mask

  theorem or_rolm (x n m1 m2 : CompCert.Int) :
      or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2) := by
    show or (and (rol x n) m1) (and (rol x n) m2) = and (rol x n) (or m1 m2)
    generalize rol x n = r
    unfold or and
    unfold UInt32.lor UInt32.land
    simp only [UInt32.ofBitVec_or, UInt32.ofBitVec_and, UInt32.ofBitVec_toBitVec]
    bv_decide

  -- Sign/zero extension operations
  def sign_ext (n : Nat) (x : CompCert.Int) : CompCert.Int :=
    UInt32.ofInt (x.toBitVec.signExtend (n.min 32) |>.toInt)

  def zero_ext (n : Nat) (x : CompCert.Int) : CompCert.Int :=
    UInt32.ofInt (((x.toBitVec).zeroExtend (n.min 32) |>.toNat : _root_.Int))

  -- Accessing bit fields
  def unsigned_bitfield_extract (pos width : _root_.Int) (n : CompCert.Int) : CompCert.Int :=
    zero_ext width.toNat (shru n (repr pos))

  def signed_bitfield_extract (pos width : _root_.Int) (n : CompCert.Int) : CompCert.Int :=
    sign_ext width.toNat (shru n (repr pos))

  def bitfield_insert (pos width : _root_.Int) (n p : CompCert.Int) : CompCert.Int :=
    let mask := shl (repr (two_p width.toNat - 1)) (repr pos)
    or (shl (zero_ext width.toNat p) (repr pos)) (and n (not mask))

  -- Check if x is a power of 2, return the log2 if so
  -- Check if x is a power of 2, return the log2 if so
  -- Uses the property: x is a power of 2 iff x != 0 && (x & (x-1)) == 0
  def is_power2 (x : CompCert.Int) : Option CompCert.Int :=
    if x == 0 then
      none
    else
      -- Check if x is a power of 2 using x & (x - 1) == 0
      let x_minus_1 := x - 1
      let and_result := x.land x_minus_1
      if and_result == 0 then
        -- x is a power of 2, find the bit position (log2)
        -- Count trailing zeros in the bit representation
        some (repr (x.toBitVec.toNat.log2 : _root_.Int))
      else
        none

  -- Helper: power of 2 characterization via bit trick
  -- For n ≠ 0, n.land (n-1) = 0 means n is a power of 2
  theorem nat_pow2_of_land_pred_eq_zero {n : Nat} (hn : n ≠ 0) (h : n &&& (n - 1) = 0) :
      ∃ k, n = 2^k := by
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn).mp h

  -- Key characterization: is_power2 n = some logn implies n = 2^logn (as shl one logn)
  theorem is_power2_pow (n logn : CompCert.Int)
      (H : is_power2 n = some logn) :
      n = shl one logn ∧ logn.toNat < 32 := by
    unfold is_power2 at H
    simp only [beq_iff_eq] at H
    split at H
    · contradiction
    · rename_i hn
      split at H
      · -- n ≠ 0 and n.land (n - 1) = 0
        rename_i hland
        have hn_ne : n ≠ 0 := hn
        -- Extract logn from H
        have hlogn : logn = repr (n.toBitVec.toNat.log2 : _root_.Int) := by
          injection H with h
          exact h.symm
        -- Now we know n.toNat is a power of 2
        have n_toNat_ne : n.toNat ≠ 0 := by
          intro h
          apply hn_ne
          apply UInt32.toNat.inj
          simp only [h]
          rfl
        -- Convert land condition to toNat
        have hland_toNat : n.toNat &&& (n.toNat - 1) = 0 := by
          have h1 : (n.land (n - 1)).toNat = 0 := by
            have : (n.land (n - 1) : CompCert.Int) = 0 := hland
            have : n.land (n - 1) = 0 := by exact this
            conv_lhs => rw [this]
            rfl
          have h2 : (n.land (n - 1)).toNat = n.toNat &&& (n - 1).toNat := by
            show (n.land (n - 1)).toBitVec.toNat = n.toNat &&& (n - 1).toNat
            have : (n.land (n - 1)).toBitVec = n.toBitVec &&& (n - 1).toBitVec := by rfl
            rw [this]
            exact BitVec.toNat_and _ _
          have h3 : (n - 1).toNat = n.toNat - 1 := by
            rw [UInt32.toNat_sub]
            have hn_pos : n.toNat ≥ 1 := by
              by_contra h
              simp only [not_le] at h
              have : n.toNat = 0 := by omega
              exact n_toNat_ne this
            have : (2^32 - 1 + n.toNat) % 2^32 = n.toNat - 1 := by
              have h_bound : n.toNat < 2^32 := n.toBitVec.isLt
              omega
            exact this
          rw [h2, h3] at h1
          exact h1
        -- Use nat_pow2_of_land_pred_eq_zero
        obtain ⟨k, hk⟩ := nat_pow2_of_land_pred_eq_zero n_toNat_ne hland_toNat
        -- Show k = n.toNat.log2
        have hk_log2 : k = n.toNat.log2 := by
          have : (2^k).log2 = k := Nat.log2_two_pow
          rw [← hk] at this
          exact this.symm
        -- Prove both parts
        -- Prove both parts
        have n_toNat_eq : n.toNat = n.toBitVec.toNat := by rfl
        constructor
        · -- Prove n = shl one logn
          apply UInt32.toNat.inj
          rw [hlogn]
          unfold shl repr
          -- Rewrite n.toBitVec.toNat to n.toNat
          conv_rhs => rw [← n_toNat_eq]
          have h_repr_toNat : (UInt32.ofInt (n.toNat.log2 : _root_.Int)).toNat = n.toNat.log2 := by
            have h_bound : n.toNat.log2 < 32 := by
              have h1 : n.toNat < 2^32 := n.toBitVec.isLt
              rw [Nat.log2_lt n_toNat_ne]
              exact h1
            have h_int_mod : ((n.toNat.log2 : _root_.Int) % (2^32 : _root_.Int)).toNat = n.toNat.log2 := by
              have h_pos : (0 : _root_.Int) ≤ (n.toNat.log2 : _root_.Int) := by omega
              have h_lt : (n.toNat.log2 : _root_.Int) < (2^32 : _root_.Int) := by omega
              rw [Int.emod_eq_of_lt h_pos h_lt]
              exact Int.toNat_natCast _
            show (UInt32.ofInt (n.toNat.log2 : _root_.Int)).toBitVec.toNat = n.toNat.log2
            have : (UInt32.ofInt (n.toNat.log2 : _root_.Int)).toBitVec.toNat =
                   (BitVec.ofNat 32 ((n.toNat.log2 : _root_.Int) % (2^32 : _root_.Int)).toNat).toNat := by rfl
            rw [this, BitVec.toNat_ofNat]
            have h_nat_mod : n.toNat.log2 % 2^32 = n.toNat.log2 := by
              exact Nat.mod_eq_of_lt (by omega : n.toNat.log2 < 2^32)
            rw [h_int_mod, h_nat_mod]
          have h_shl_eq : (UInt32.shiftLeft one (UInt32.ofInt (n.toNat.log2 : _root_.Int))).toNat =
                          2^n.toNat.log2 := by
            have : (UInt32.shiftLeft one (UInt32.ofInt (n.toNat.log2 : _root_.Int))).toNat =
                   (one <<< (UInt32.ofInt (n.toNat.log2 : _root_.Int))).toNat := by rfl
            rw [this, UInt32.toNat_shiftLeft]
            have h_one : (one : CompCert.Int).toNat = 1 := by rfl
            rw [h_one, h_repr_toNat]
            -- Now show (1 <<< (n.toNat.log2 % 32)) % 2^32 = 2^n.toNat.log2
            have h_log2_mod : n.toNat.log2 % 32 = n.toNat.log2 := by
              have : n.toNat.log2 < 32 := by
                have h1 : n.toNat < 2^32 := n.toBitVec.isLt
                rw [Nat.log2_lt n_toNat_ne]
                exact h1
              exact Nat.mod_eq_of_lt this
            rw [h_log2_mod]
            rw [Nat.shiftLeft_eq]
            have h_bound : 2^n.toNat.log2 < 2^32 := by
              have : n.toNat.log2 < 32 := by
                have h1 : n.toNat < 2^32 := n.toBitVec.isLt
                rw [Nat.log2_lt n_toNat_ne]
                exact h1
              exact Nat.pow_lt_pow_right (by omega : 1 < 2) this
            simp only [Nat.one_mul]
            exact Nat.mod_eq_of_lt h_bound
          rw [h_shl_eq]
          rw [← hk_log2, hk]
        · -- Prove logn.toNat < 32
          rw [hlogn]
          unfold repr
          have h_bound : n.toNat.log2 < 32 := by
            have h1 : n.toNat < 2^32 := n.toBitVec.isLt
            rw [Nat.log2_lt n_toNat_ne]
            exact h1
          have h_int_mod : ((n.toNat.log2 : _root_.Int) % (2^32 : _root_.Int)).toNat = n.toNat.log2 := by
            have h_pos : (0 : _root_.Int) ≤ (n.toNat.log2 : _root_.Int) := by omega
            have h_lt : (n.toNat.log2 : _root_.Int) < (2^32 : _root_.Int) := by omega
            rw [Int.emod_eq_of_lt h_pos h_lt]
            exact Int.toNat_natCast _
          show (UInt32.ofInt (n.toBitVec.toNat.log2 : _root_.Int)).toBitVec.toNat < 32
          have : n.toBitVec.toNat = n.toNat := by rfl
          rw [this]
          have : (UInt32.ofInt (n.toNat.log2 : _root_.Int)).toBitVec.toNat =
                 (BitVec.ofNat 32 ((n.toNat.log2 : _root_.Int) % (2^32 : _root_.Int)).toNat).toNat := by rfl
          rw [this, BitVec.toNat_ofNat]
          have h_nat_mod : n.toNat.log2 % 2^32 = n.toNat.log2 := by
            exact Nat.mod_eq_of_lt (by omega : n.toNat.log2 < 2^32)
          rw [h_int_mod, h_nat_mod]
          exact h_bound
      · contradiction


  theorem UInt32.ofInt_toBitVec_toInt (x : UInt32) :
    UInt32.ofInt x.toBitVec.toInt = x := by
    obtain ⟨⟨n, hn⟩⟩ := x
    simp only [UInt32.ofInt, BitVec.toInt, BitVec.toNat, UInt32.ofNat, BitVec.ofNat]
    split <;> · congr; apply Fin.ext; simp only [Fin.Internal.ofNat]; omega

  set_option pp.fieldNotation false in
  set_option pp.numericTypes false in
  theorem zero_ext_and (n : Nat) (x : CompCert.Int) :
      zero_ext n x = and x (repr (two_p n - 1)) := by
    -- Helper lemmas for the proof
    have ofInt_toBitVec_eq_ofInt : ∀ z : _root_.Int, (UInt32.ofInt z).toBitVec = BitVec.ofInt 32 z := by
      intro z
      apply BitVec.eq_of_toNat_eq
      have h1 : (UInt32.ofInt z).toBitVec = BitVec.ofNat 32 ((z % 2^32).toNat) := rfl
      simp only [h1, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    have BitVec_ofInt_natCast : ∀ n m : Nat, BitVec.ofInt n (m : _root_.Int) = BitVec.ofNat n m := by
      intros n m
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat]
    have two_pow_sub_one_nonneg : ∀ n : Nat, (2^n : _root_.Int) - 1 = ((2^n - 1 : Nat) : _root_.Int) := by
      intro n
      have : 1 ≤ 2^n := Nat.one_le_two_pow
      simp [_root_.Int.ofNat_sub this]
    have getLsbD_eq_testBit_toNat : ∀ {w : Nat} (v : BitVec w) (i : Nat),
        v.getLsbD i = v.toNat.testBit i := by intros; rfl

    -- Main proof
    rw [UInt32.eq_iff_toBitVec_eq]
    unfold zero_ext and repr two_p
    have rhs_eq : (UInt32.land x (UInt32.ofInt (2^n - 1))).toBitVec =
                   x.toBitVec &&& (UInt32.ofInt (2^n - 1)).toBitVec := rfl
    rw [rhs_eq]
    simp only [ofInt_toBitVec_eq_ofInt]
    rw [two_pow_sub_one_nonneg, BitVec_ofInt_natCast, BitVec_ofInt_natCast]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
    rw [← getLsbD_eq_testBit_toNat, BitVec.getLsbD_setWidth, Nat.testBit_two_pow_sub_one]
    have hi32 : decide (i < 32) = true := by simp [hi]
    rw [hi32]
    simp only [Bool.true_and]
    rw [Bool.and_comm]
    congr 1
    simp only [Nat.lt_min, decide_eq_decide]
    omega

  theorem add_commut (x y : CompCert.Int) : x + y = y + x := by
    -- Use ext to reduce to showing the underlying values are equal
    ext
    -- Now we need to show (x + y).val = (y + x).val
    -- This should follow from Nat commutativity
    ac_rfl

  theorem add_assoc (x y z : CompCert.Int) : (x + y) + z = x + (y + z) := by
    ext
    ac_rfl

  -- Helper lemma for modular arithmetic with Int.toNat
  private lemma uint32_ofNat_toBitVec_toNat (n : Nat) :
      (UInt32.ofNat n).toBitVec.toNat = n % (2^32) := by
    simp [UInt32.ofNat, BitVec.toNat_ofNat]

  private lemma uint32_toNat_eq_toBitVec_toNat (x : UInt32) :
      UInt32.toNat x = x.toBitVec.toNat := by
    rfl

  private lemma uint32_toBitVec_toNat_add (x y : UInt32) :
      (x + y).toBitVec.toNat = (UInt32.toNat x + UInt32.toNat y) % (2^32) := by
    rfl

  private lemma int_toNat_neg_add_mod (a b n : Nat) (hn : 0 < n) :
      (-(↑(a + b) : _root_.Int) % ↑n).toNat % n =
      ((-(↑a : _root_.Int) % ↑n).toNat + (-(↑b : _root_.Int) % ↑n).toNat) % n := by
    have hn' : (n : _root_.Int) ≠ 0 := by
      intro h
      have : n = 0 := Nat.cast_injective h
      omega
    have hnPos : (0 : _root_.Int) < ↑n := by omega
    -- All emod results are nonnegative
    have hA := Int.emod_nonneg (-(↑a : _root_.Int)) hn'
    have hB := Int.emod_nonneg (-(↑b : _root_.Int)) hn'
    have hC := Int.emod_nonneg (-(↑(a + b) : _root_.Int)) hn'
    -- All emod results are < n
    have hAlt : (-(↑a : _root_.Int) % ↑n) < ↑n := Int.emod_lt_of_pos _ hnPos
    have hBlt : (-(↑b : _root_.Int) % ↑n) < ↑n := Int.emod_lt_of_pos _ hnPos
    have hClt : (-(↑(a + b) : _root_.Int) % ↑n) < ↑n := Int.emod_lt_of_pos _ hnPos
    -- Prove equality by showing both sides equal as Ints after casting
    suffices h : (↑((-(↑(a + b) : _root_.Int) % ↑n).toNat % n) : _root_.Int) =
                  ↑(((-(↑a : _root_.Int) % ↑n).toNat + (-(↑b : _root_.Int) % ↑n).toNat) % n) by
      exact Nat.cast_injective h
    -- Use Int.natCast_mod: ↑(m % n) = ↑m % ↑n
    rw [Int.natCast_mod, Int.natCast_mod]
    -- Now convert toNat back to Int using Int.toNat_of_nonneg on RHS first
    conv_rhs => arg 1; rw [Nat.cast_add, Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    -- Then on LHS
    rw [Int.toNat_of_nonneg hC]
    -- Now both sides are Int mod expressions
    -- LHS: (-(↑(a+b)) % ↑n) % ↑n = -(↑(a+b)) % ↑n
    conv_lhs => rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    -- RHS: ((-(↑a) % ↑n) + (-(↑b) % ↑n)) % ↑n
    rw [Int.add_emod]
    conv_rhs => arg 1; arg 1; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    conv_rhs => arg 1; arg 2; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [← Int.add_emod]
    -- Now prove -(↑(a+b)) % ↑n = (-(↑a) + -(↑b)) % ↑n
    simp only [Nat.cast_add, Int.neg_add]

  theorem neg_add_distr (x y : CompCert.Int) : neg (x + y) = neg x + neg y := by
    ext
    unfold neg
    -- Both sides use UInt32.ofInt which wraps to UInt32.ofNat ∘ Int.toNat
    show (UInt32.ofInt (-(↑(x + y).toNat : _root_.Int))).toNat =
         (UInt32.ofInt (-(↑x.toNat : _root_.Int)) + UInt32.ofInt (-(↑y.toNat : _root_.Int))).toNat
    -- Unfold UInt32.ofInt / UInt32.toNat so the goal is stated over BitVec.toNat
    simp only [UInt32.ofInt, UInt32.toNat]
    -- Now apply our helper lemma
    have h32 : (2 : Nat) ^ 32 > 0 := by omega
    convert int_toNat_neg_add_mod x.toNat y.toNat (2^32) h32 using 1
    · -- Goal 1: case e'_2
      rw [uint32_ofNat_toBitVec_toNat]
      rw [uint32_toBitVec_toNat_add]
      congr 1
      rw [Int.natCast_mod]
      -- Need: (-(m % n) % n).toNat = (-m % n).toNat
      simp only [Int.neg_emod]
      split
      · split <;> omega
      · split
        · omega
        · simp [Int.emod_emod_of_dvd _ (dvd_refl _)]
    · -- Goal 2: case e'_3
      -- LHS: (A + B).toBitVec.toNat where A, B are UInt32.ofNat (...)
      -- Use the fact that (a+b).toBitVec.toNat = (a.toNat + b.toNat) % 2^32
      rw [uint32_toBitVec_toNat_add]
      -- Now apply the helper lemmas
      simp only [UInt32.toNat]
      rw [uint32_ofNat_toBitVec_toNat, uint32_ofNat_toBitVec_toNat]
      rw [← uint32_toNat_eq_toBitVec_toNat x, ← uint32_toNat_eq_toBitVec_toNat y]
      -- Now LHS: ((-↑(UInt32.toNat x) % 2^32).toNat % 2^32 + (-↑(UInt32.toNat y) % 2^32).toNat % 2^32) % 2^32
      -- RHS: ((-↑(UInt32.toNat x) % ↑(2^32)).toNat + (-↑(UInt32.toNat y) % ↑(2^32)).toNat) % 2^32
      -- The key is: Int.toNat is already bounded by the Int value, and Int.emod produces values in [0, n)
      -- So (... % n).toNat is already < n, hence (... % n).toNat % n = (... % n).toNat
      simp

  -- General bridge lemma: the Nat value of `UInt32.ofInt z` is `(z % 2^32).toNat`.
  -- This works because `UInt32.ofInt z` reduces to `BitVec.ofNat 32 ((z % 2^32).toNat)`,
  -- and `(z % 2^32).toNat < 2^32`, so the extra `% 2^32` is the identity.

  theorem sub_add_opp (x y : CompCert.Int) : sub x y = x + neg y := by
    apply UInt32.toNat.inj
    -- LHS: (sub x y).toNat = (2^32 - y.toNat + x.toNat) % 2^32   [UInt32.toNat_sub]
    -- RHS: (x + neg y).toNat = (x.toNat + (neg y).toNat) % 2^32
    have hy : y.toNat < 2^32 := y.toBitVec.isLt
    -- `sub` is definitionally `UInt32.sub`, and `UInt32.sub x y = x - y`, so restate
    -- the LHS using the `-` operator so that `UInt32.toNat_sub` applies.
    show (x - y).toNat = (x + neg y).toNat
    rw [UInt32.toNat_add, neg_toNat, UInt32.toNat_sub]
    -- Goal (Nat-level, both mod 2^32):
    --   (2^32 - y.toNat + x.toNat) % 2^32 = (x.toNat + (-(y.toNat) % 2^32).toNat) % 2^32
    -- Key: (-(y.toNat : Int) % 2^32).toNat = (2^32 - y.toNat) % 2^32.
    have hkey : (-(y.toNat : _root_.Int) % (2^32 : _root_.Int)).toNat
                  = (2^32 - y.toNat) % 2^32 := by
      have hnn : (0 : _root_.Int) ≤ -(y.toNat : _root_.Int) % (2^32 : _root_.Int) :=
        Int.emod_nonneg _ (by omega)
      -- Cast both sides to Int and use natCast/emod facts.
      have : ((-(y.toNat : _root_.Int) % (2^32 : _root_.Int)).toNat : _root_.Int)
               = (((2^32 - y.toNat) % 2^32 : Nat) : _root_.Int) := by
        rw [Int.toNat_of_nonneg hnn]
        push_cast [Nat.mod_eq_of_lt (a := 2^32 - y.toNat)]
        omega
      exact_mod_cast this
    rw [hkey]
    -- Pure Nat modular arithmetic with a fixed literal modulus: omega handles this.
    omega

  theorem neg_involutive (x : CompCert.Int) : neg (neg x) = x := by
    apply UInt32.toNat.inj
    have hx : x.toNat < 2^32 := x.toBitVec.isLt
    rw [neg_toNat, neg_toNat]
    -- Goal: (-(((-(x.toNat:Int)) % 2^32).toNat : Int) % 2^32).toNat = x.toNat
    -- Let inner = -(x.toNat) % 2^32, which is in [0, 2^32), so its toNat casts back to itself.
    have hnn : (0 : _root_.Int) ≤ -(x.toNat : _root_.Int) % (2^32 : _root_.Int) :=
      Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hnn]
    -- Goal: (-(-(x.toNat:Int) % 2^32) % 2^32).toNat = x.toNat
    -- Rewrite -(a % n) % n = -a % n, then -(-x) % n = x % n = x (since 0 ≤ x < 2^32).
    have hneg : (-(-(x.toNat : _root_.Int) % (2^32 : _root_.Int)) % (2^32 : _root_.Int))
                  = (x.toNat : _root_.Int) := by
      have h1 : (-(-(x.toNat : _root_.Int) % (2^32 : _root_.Int)) % (2^32 : _root_.Int))
                  = (-(-(x.toNat : _root_.Int)) % (2^32 : _root_.Int)) := by
        omega
      rw [h1, neg_neg]
      apply Int.emod_eq_of_lt (by omega)
      exact_mod_cast hx
    rw [hneg]
    exact Int.toNat_natCast _

  theorem sub_add_l (a b i : CompCert.Int) :
      sub (a + i) b = sub a b + i := by
    rw [sub_add_opp, sub_add_opp]
    ac_rfl

  theorem sub_add_r (a b i : CompCert.Int) :
      sub a (b + i) = sub a b + neg i := by
    rw [sub_add_opp, sub_add_opp, neg_add_distr]
    ac_rfl

  -- The signed interpretation is congruent to the unsigned value modulo 2^32.
  -- This is the *true* content behind the (false, at INT_MIN) equality `neg_signed`.
  theorem signed_mod_eq_toNat_mod (i : CompCert.Int) :
      i.signed % (2^32 : _root_.Int) = (i.toNat : _root_.Int) % (2^32 : _root_.Int) := by
    unfold signed
    rw [show i.toNat = i.toBitVec.toNat from rfl]
    rw [BitVec.toInt_eq_toNat_bmod]
    unfold Int.bmod
    simp only []
    split
    · simp
    · have h_bound : i.toBitVec.toNat < 2^32 := i.toBitVec.isLt
      omega

  -- NOTE: The naive equality `(neg x).signed = -(x.signed)` is FALSE at x = 2^31
  -- (INT_MIN), because `neg` of INT_MIN overflows back to INT_MIN in two's complement.
  -- The correct, provable statement is the congruence modulo 2^32 below, which is all
  -- that modular pointer arithmetic (Ptrofs) actually requires.
  theorem neg_signed_mod (x : CompCert.Int) :
      (neg x).signed % (2^32 : _root_.Int) = (-(x.signed)) % (2^32 : _root_.Int) := by
    rw [signed_mod_eq_toNat_mod, neg_toNat]
    -- (neg x).toNat = (-(x.toNat) % 2^32).toNat ; relate to -(x.signed) mod 2^32
    have hx : x.toNat < 2^32 := x.toBitVec.isLt
    have hnn : (0 : _root_.Int) ≤ -(x.toNat : _root_.Int) % (2^32 : _root_.Int) :=
      Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hnn]
    -- Goal: (-(x.toNat) % 2^32) % 2^32 = (-(x.signed)) % 2^32
    have hsig : x.signed % (2^32 : _root_.Int) = (x.toNat : _root_.Int) % (2^32 : _root_.Int) :=
      signed_mod_eq_toNat_mod x
    omega

  theorem repr_add_signed (x : _root_.Int) (i : CompCert.Int) :
      repr (x + i.signed) = repr x + i := by
    rw [UInt32.eq_iff_toBitVec_eq]
    apply BitVec.eq_of_toNat_eq
    unfold repr signed
    simp only [uint32_ofInt_toBitVec, BitVec.toNat_ofInt]
    have h_add : (UInt32.ofInt x + i).toBitVec.toNat
                  = ((UInt32.ofInt x).toBitVec + i.toBitVec).toNat := rfl
    rw [h_add]
    simp only [BitVec.toNat_add, uint32_ofInt_toBitVec, BitVec.toNat_ofInt]
    have h_i_nat : i.toNat = i.toBitVec.toNat := rfl
    rw [← h_i_nat]
    have h_signed := signed_mod_eq_toNat_mod i
    unfold signed at h_signed
    have h_add_mod : (x + i.toBitVec.toInt) % ↑(2^32 : Nat) = (x + ↑i.toNat) % ↑(2^32 : Nat) := by
      omega
    rw [h_add_mod]
    have h_expand : (x + ↑i.toNat) % ↑(2^32 : Nat)
                      = (x % ↑(2^32 : Nat) + ↑i.toNat) % ↑(2^32 : Nat) := by
      omega
    rw [h_expand]
    have h_i_lt : i.toNat < 2^32 := i.toBitVec.isLt
    omega

  -- Addition is congruent modulo 2^32 on the signed interpretation.
  theorem add_signed_mod (i j : CompCert.Int) :
      CompCert.Int.signed (add i j) % (2^32 : _root_.Int)
        = (i.signed + j.signed) % (2^32 : _root_.Int) := by
    rw [signed_mod_eq_toNat_mod]
    have hij : (add i j).toNat = (i.toNat + j.toNat) % (2^32) := by
      change (i + j).toNat = _
      rw [uint32_toNat_eq_toBitVec_toNat, uint32_toBitVec_toNat_add,
          uint32_toNat_eq_toBitVec_toNat, uint32_toNat_eq_toBitVec_toNat]
    rw [hij]
    have hi := signed_mod_eq_toNat_mod i
    have hj := signed_mod_eq_toNat_mod j
    have hi_lt : i.toNat < 2^32 := i.toBitVec.isLt
    have hj_lt : j.toNat < 2^32 := j.toBitVec.isLt
    omega

  -- When the true signed sum is in range, `add` does not overflow.
  theorem add_signed_eq_of_range (i j : CompCert.Int)
      (hlo : -(2^31 : _root_.Int) ≤ i.signed + j.signed)
      (hhi : i.signed + j.signed < (2^31 : _root_.Int)) :
      CompCert.Int.signed (add i j) = i.signed + j.signed := by
    have hmod := add_signed_mod i j
    have hlo2 : -(2^31 : _root_.Int) ≤ CompCert.Int.signed (add i j) := by
      have := @BitVec.le_toInt 32 (add i j).toBitVec
      simpa [signed] using this
    have hhi2 : CompCert.Int.signed (add i j) < (2^31 : _root_.Int) := by
      have := @BitVec.toInt_lt 32 (add i j).toBitVec
      simpa [signed] using this
    omega

  theorem mul_commut (x y : CompCert.Int) : x * y = y * x := by
    ext
    ac_rfl

  theorem mul_assoc (x y z : CompCert.Int) : (x * y) * z = x * (y * z) := by
    ext
    ac_rfl

  theorem mul_add_distr_l (x y z : CompCert.Int) : (x + y) * z = x * z + y * z := by
    -- This is a ring property - should be derivable from the CommRing instance
    -- But let's prove it step by step at the Nat level
    ext
    congr
    grind

  theorem mul_add_distr_r (x y z : CompCert.Int) : x * (y + z) = x * y + x * z := by
    ext
    congr
    grind

  theorem and_commut (x y : CompCert.Int) : and x y = and y x := by
    unfold and
    unfold UInt32.land
    simp
    ac_rfl

  theorem and_assoc (x y z : CompCert.Int) : and (and x y) z = and x (and y z) := by
    unfold and
    unfold UInt32.land
    simp
    ac_rfl

  theorem and_self (x : CompCert.Int) : and x x = x := by
    unfold and
    unfold UInt32.land
    simp

  theorem zero_ext_idem (n : Nat) (x : CompCert.Int) :
      zero_ext n (zero_ext n x) = zero_ext n x := by
    rw [zero_ext_and n (zero_ext n x), zero_ext_and n x, and_assoc, and_self]

  theorem sign_ext_idem (n : Nat) (x : CompCert.Int) :
      sign_ext n (sign_ext n x) = sign_ext n x := by
    unfold sign_ext
    congr 1
    rw [uint32_ofInt_toBitVec]
    have hle : n.min 32 ≤ 32 := Nat.min_le_right n 32
    rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ hle, BitVec.toInt_ofInt]
    -- Generalize the inner BitVec to a fresh `y : BitVec (n.min 32)`.
    generalize hy : x.toBitVec.signExtend (n.min 32) = y
    -- Goal: (y.toInt.bmod (2^32)).bmod (2^(n.min 32)) = y.toInt
    have h_cancel : y.toInt.bmod (2^(n.min 32)) = y.toInt := BitVec.toInt_bmod_cancel y
    have lower : -(2^((n.min 32)-1) : _root_.Int) ≤ y.toInt := BitVec.le_toInt y
    have upper : y.toInt < (2^((n.min 32)-1) : _root_.Int) := @BitVec.toInt_lt (n.min 32) y
    have lower32 : -(2^31 : _root_.Int) ≤ y.toInt := by
      have : (2^((n.min 32)-1) : _root_.Int) ≤ (2^31 : _root_.Int) := by
        have hm1 : ((n.min 32) - 1) ≤ 31 := by omega
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hm1
      omega
    have upper32 : y.toInt < (2^31 : _root_.Int) := by
      have : (2^((n.min 32)-1) : _root_.Int) ≤ (2^31 : _root_.Int) := by
        have hm1 : ((n.min 32) - 1) ≤ 31 := by omega
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hm1
      omega
    -- Prove that y.toInt.bmod (2^32) = y.toInt using the bounds
    have hbmod32 : y.toInt.bmod (2^32) = y.toInt := by
      have hl : (-2147483648 : _root_.Int) ≤ y.toInt := by
        have : (2^31 : _root_.Int) = 2147483648 := by norm_num
        omega
      have hu : y.toInt < (2147483648 : _root_.Int) := by
        have : (2^31 : _root_.Int) = 2147483648 := by norm_num
        omega
      unfold _root_.Int.bmod
      norm_num
      split_ifs <;> omega
    rw [hbmod32, h_cancel]

  theorem or_commut (x y : CompCert.Int) : or x y = or y x := by
    unfold or
    unfold UInt32.lor
    simp
    ac_rfl

  theorem or_assoc (x y z : CompCert.Int) : or (or x y) z = or x (or y z) := by
    unfold or
    unfold UInt32.lor
    simp
    ac_rfl

  theorem xor_commut (x y : CompCert.Int) : xor x y = xor y x := by
    unfold xor
    unfold UInt32.xor
    simp
    ac_rfl

  theorem xor_assoc (x y z : CompCert.Int) : xor (xor x y) z = xor x (xor y z) := by
    unfold xor
    unfold UInt32.xor
    simp
    ac_rfl

  theorem rol_zero (x : CompCert.Int) : rol x zero = x := by
    unfold rol zero
    simp
    rw [BitVec.rotateLeft_zero]
    apply UInt32.ofInt_toBitVec_toInt

  theorem repr_congr {a b : _root_.Int} (h : a % (2^32 : _root_.Int) = b % (2^32 : _root_.Int)) :
      repr a = repr b := by
    apply UInt32.toNat.inj
    show (UInt32.ofInt a).toNat = (UInt32.ofInt b).toNat
    rw [uint32_ofInt_toNat, uint32_ofInt_toNat, h]

  -- Helper lemmas for rotate-and-mask composition
  -- These are needed for val-level rolm_rolm theorem
  -- Note: Rotate distribution over AND works because rotateLeft is a bit permutation

  -- The toBitVec of a rotate is just the BitVec rotateLeft (the ofInt∘toInt round-trip is identity).
  theorem rol_toBitVec (x n : CompCert.Int) :
      (rol x n).toBitVec = x.toBitVec.rotateLeft (n.toNat % 32) := by
    unfold rol
    -- Goal: (UInt32.ofInt ((x.toBitVec.rotateLeft (n.toNat % 32)).toInt)).toBitVec
    --     = x.toBitVec.rotateLeft (n.toNat % 32)
    -- Strategy: show (UInt32.ofInt bv.toInt).toBitVec = BitVec.ofInt 32 bv.toInt = bv
    have h1 : ∀ (bv : BitVec 32), (UInt32.ofInt bv.toInt).toBitVec = bv := by
      intro bv
      have h_eq : (UInt32.ofInt bv.toInt).toBitVec = BitVec.ofInt 32 bv.toInt := by
        apply BitVec.eq_of_toNat_eq
        have : (UInt32.ofInt bv.toInt).toBitVec = BitVec.ofNat 32 ((bv.toInt % 2^32).toNat) := rfl
        simp only [this, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
        omega
      rw [h_eq]
      exact BitVec.ofInt_toInt
    exact h1 _

  set_option linter.unusedTactic false in
  theorem rol_and (a b n : CompCert.Int) :
      rol (and a b) n = and (rol a n) (rol b n) := by
    rw [UInt32.eq_iff_toBitVec_eq]
    rw [rol_toBitVec]
    show (a.land b).toBitVec.rotateLeft (n.toNat % 32) = ((rol a n).land (rol b n)).toBitVec
    have land_eq1 : (a.land b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
    have land_eq2 : ((rol a n).land (rol b n)).toBitVec = (rol a n).toBitVec &&& (rol b n).toBitVec := rfl
    rw [land_eq1, land_eq2, rol_toBitVec, rol_toBitVec]
    -- Goal: (a.toBitVec &&& b.toBitVec).rotateLeft k = (a.toBitVec.rotateLeft k) &&& (b.toBitVec.rotateLeft k)
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_and]
    intro hi
    -- Now the goal is a Bool equality involving `bif` expressions
    -- The key insight: (a && b) rotated = (a rotated) && (b rotated) bit-by-bit
    by_cases h : i < n.toNat % 32
    · simp [h, hi]
    · simp [h, hi]

  -- Rotate composition: rol (rol x n1) n2 = rol x (n1 + n2)
  theorem rol_rol (x n1 n2 : CompCert.Int) :
      rol (rol x n1) n2 = rol x (add n1 n2) := by
    rw [UInt32.eq_iff_toBitVec_eq]
    rw [rol_toBitVec, rol_toBitVec, rol_toBitVec]
    -- LHS: (x.toBitVec.rotateLeft (n1.toNat % 32)).rotateLeft (n2.toNat % 32)
    -- RHS: x.toBitVec.rotateLeft ((add n1 n2).toNat % 32)
    -- add n1 n2 is UInt32.add, so (add n1 n2).toNat = (n1.toNat + n2.toNat) % 2^32
    have h_add : (add n1 n2).toNat = (n1.toNat + n2.toNat) % 2^32 := by
      unfold add
      rfl
    rw [h_add]
    -- Use that 32 divides 2^32
    have : (n1.toNat + n2.toNat) % 2^32 % 32 = (n1.toNat + n2.toNat) % 32 := by
      have h_dvd : 32 ∣ 2^32 := by norm_num
      exact Nat.mod_mod_of_dvd (n1.toNat + n2.toNat) h_dvd
    rw [this]
    -- Prove BitVec equality via getLsbD
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_rotateLeft, Nat.mod_mod]
    intro hi
    -- After unfolding, we need to show the nested accesses are equal
    -- The key is that the index arithmetic satisfies: ((i + n2%32) % 32 + n1%32) % 32 = (i + (n1+n2)%32) % 32
    by_cases h : i < n2.toNat % 32
    · simp [h, hi]
      by_cases h2 : 32 - n2.toNat % 32 + i < n1.toNat % 32
      · simp [h2]
        by_cases h3 : i < (n1.toNat + n2.toNat) % 32
        · simp [h3]
          congr 1
          -- Need: 32 - n1 % 32 + (32 - n2 % 32 + i) = 32 - (n1 + n2) % 32 + i
          have : n1.toNat % 32 < 32 := Nat.mod_lt _ (by norm_num : 0 < 32)
          have : n2.toNat % 32 < 32 := Nat.mod_lt _ (by norm_num : 0 < 32)
          have : (n1.toNat + n2.toNat) % 32 < 32 := Nat.mod_lt _ (by norm_num : 0 < 32)
          omega
        · simp [h3]
          congr 1
          omega
      · simp [h2]
        by_cases h3 : 32 - n2.toNat % 32 + i < 32
        · simp [h3]
          by_cases h4 : i < (n1.toNat + n2.toNat) % 32
          · simp [h4]
            congr 1
            omega
          · simp [h4]
            congr 1
            omega
        · -- Contradiction: i < 32, i < n2 % 32, but 32 - n2 % 32 + i >= 32
          have : n2.toNat % 32 < 32 := Nat.mod_lt _ (by norm_num : 0 < 32)
          omega
    · simp [h, hi]
      by_cases h2 : i - n2.toNat % 32 < n1.toNat % 32
      · simp [h2]
        by_cases h3 : i < (n1.toNat + n2.toNat) % 32
        · simp [h3]
          congr 1
          omega
        · simp [h3]
          congr 1
          omega
      · by_cases h3 : i - n2.toNat % 32 < 32
        · simp [h2, h3]
          by_cases h4 : i < (n1.toNat + n2.toNat) % 32
          · simp [h4]
            congr 1
            omega
          · simp [h4]
            congr 1
            omega
        · have : n2.toNat % 32 < 32 := Nat.mod_lt _ (by norm_num : 0 < 32)
          omega

  -- rol only depends on rotate amount mod 32
  theorem rol_mod (x k : CompCert.Int) :
      rol x (modu k iwordsize) = rol x k := by
    rw [UInt32.eq_iff_toBitVec_eq]
    rw [rol_toBitVec, rol_toBitVec]
    congr 1
    show (modu k iwordsize).toNat % 32 = k.toNat % 32
    have hmod : (modu k iwordsize).toNat = k.toNat % 32 := by
      unfold modu
      show (repr ((k.unsigned : _root_.Int) % (iwordsize.unsigned : _root_.Int))).toNat = k.toNat % 32
      have hun : (iwordsize.unsigned : _root_.Int) = 32 := by decide
      have hku : (k.unsigned : _root_.Int) = (k.toNat : _root_.Int) := rfl
      rw [hun, hku]
      show (UInt32.ofInt ((k.toNat : _root_.Int) % 32)).toNat = k.toNat % 32
      rw [uint32_ofInt_toNat]
      have h1 : ((k.toNat : _root_.Int) % 32) % (2^32 : _root_.Int) = (k.toNat : _root_.Int) % 32 := by
        have hlt : (k.toNat : _root_.Int) % 32 < (2^32 : _root_.Int) := by
          have := Int.emod_lt_of_pos (k.toNat : _root_.Int) (show (0 : _root_.Int) < 32 by decide)
          omega
        have hnn : (0 : _root_.Int) ≤ (k.toNat : _root_.Int) % 32 :=
          Int.emod_nonneg _ (show (32 : _root_.Int) ≠ 0 by decide)
        exact Int.emod_eq_of_lt hnn hlt
      rw [h1]
      rw [show ((k.toNat : _root_.Int) % 32) = ((k.toNat % 32 : Nat) : _root_.Int) from by
        rw [Int.natCast_mod]; norm_num]
      exact Int.toNat_natCast _
    rw [hmod, Nat.mod_mod]

  -- Main lemma: rolm composition
  theorem rolm_rolm (x n1 m1 n2 m2 : CompCert.Int) :
      rolm (rolm x n1 m1) n2 m2 = rolm x (modu (add n1 n2) iwordsize) (and (rol m1 n2) m2) := by
    unfold rolm
    rw [rol_and]
    rw [rol_rol]
    rw [← and_assoc]
    rw [rol_mod]

  -- Sign-bit extraction: rolm x 1 1 extracts bit 31 (sign bit) = signed-negativity indicator.
  theorem rolm_one_one_eq_lt (x : CompCert.Int) :
      rolm x one one = if x.signed < 0 then one else zero := by
    -- rolm x 1 1 = (rol x 1) & 1 extracts bit 0 of (rol x 1) = bit 31 of x.
    have hbit : (rolm x one one) = if x.toBitVec.getLsbD 31 then one else zero := by
      unfold rolm and
      rw [UInt32.eq_iff_toBitVec_eq]
      -- Now prove: (UInt32.land (rol x one) one).toBitVec = (if x.toBitVec.getLsbD 31 then one else zero).toBitVec
      have land_eq : (UInt32.land (rol x one) one).toBitVec = (rol x one).toBitVec &&& one.toBitVec := rfl
      rw [land_eq, rol_toBitVec]
      -- Simplify one.toNat % 32 = 1
      have one_mod : (one : CompCert.Int).toNat % 32 = 1 := by decide
      rw [one_mod]
      -- RHS: (if x.toBitVec.getLsbD 31 then one else zero).toBitVec
      --    = if x.toBitVec.getLsbD 31 then 1#32 else 0#32
      have one_bv : (one : CompCert.Int).toBitVec = 1#32 := rfl
      have zero_bv : (zero : CompCert.Int).toBitVec = 0#32 := rfl
      simp only [one_bv]
      -- Goal: x.toBitVec.rotateLeft 1 &&& 1#32 = if x.toBitVec.getLsbD 31 then 1#32 else 0#32
      -- This is a concrete BitVec equality that bv_decide should be able to handle
      bv_decide
    rw [hbit]
    -- x.signed < 0 ↔ msb (bit 31) set
    have hsign : (x.signed < 0) ↔ x.toBitVec.getLsbD 31 := by
      unfold signed
      -- x.toBitVec.toInt < 0 ↔ x.toBitVec.msb ↔ x.toBitVec.getLsbD 31
      constructor
      · intro h_neg
        have : x.toBitVec.msb = true := by
          rw [← BitVec.slt_zero_eq_msb]
          simp only [BitVec.slt, decide_eq_true_eq]
          exact h_neg
        rw [BitVec.msb_eq_getLsbD_last] at this
        simp only [Nat.reduceSub] at this
        exact this
      · intro h_bit31
        have : x.toBitVec.msb = true := by
          rw [BitVec.msb_eq_getLsbD_last]
          simp only [Nat.reduceSub]
          exact h_bit31
        rw [← BitVec.slt_zero_eq_msb] at this
        simp only [BitVec.slt, decide_eq_true_eq] at this
        exact this
    by_cases h : x.signed < 0
    · have : x.toBitVec.getLsbD 31 = true := hsign.mp h
      simp [h, this]
    · have : x.toBitVec.getLsbD 31 = false := by
        by_contra h_false
        have h_true : x.toBitVec.getLsbD 31 = true := by
          cases h_eq : x.toBitVec.getLsbD 31
          · exfalso
            apply h_false
            exact h_eq
          · rfl
        have : x.signed < 0 := hsign.mpr h_true
        contradiction
      simp only [this, h]
      rfl

  -- Shift-left equals rolm with appropriate mask
  theorem shl_rolm (x n : CompCert.Int) (H : ltu n iwordsize = true) :
      shl x n = rolm x n (shl mone n) := by
    have hn : n.toNat < 32 := by
      unfold ltu iwordsize at H
      have : n < (32 : UInt32) := by simpa using H
      have : n.toNat < (32 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp this
      simp at this
      exact this
    rw [UInt32.eq_iff_toBitVec_eq]
    show (x <<< n).toBitVec = ((rol x n).land (mone <<< n)).toBitVec
    have hshl : ∀ (a m : CompCert.Int), (a <<< m).toBitVec = a.toBitVec <<< (m.toNat % 32) := by
      intro a m; rfl
    rw [hshl]
    show x.toBitVec <<< (n.toNat % 32) = (rol x n).toBitVec &&& (mone <<< n).toBitVec
    rw [rol_toBitVec, hshl]
    have hmone : mone.toBitVec = BitVec.allOnes 32 := by decide
    rw [hmone]
    rw [Nat.mod_eq_of_lt hn]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 32
    · by_cases hin : i < n.toNat
      · have hmod : (i - n.toNat % 32) % 32 = i - n.toNat := by
          rw [Nat.mod_eq_of_lt hn]; exact Nat.mod_eq_of_lt (by omega)
        simp [hi, hin, Nat.mod_eq_of_lt hn]
      · have hmod : (i - n.toNat % 32) % 32 = i - n.toNat := by
          rw [Nat.mod_eq_of_lt hn]; exact Nat.mod_eq_of_lt (by omega)
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, BitVec.getLsbD_shiftLeft, hi, hin, Nat.mod_eq_of_lt hn,
          decide_true, decide_false, Bool.true_and]
        have hlt : i - n.toNat < 32 := by omega
        simp [hlt]
    · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]
      simp

  -- Shift-right-logical equals rolm with appropriate mask
  theorem shru_rolm (x n : CompCert.Int) (H : ltu n iwordsize = true) :
      shru x n = rolm x (sub iwordsize n) (shru mone n) := by
    have hn : n.toNat < 32 := by
      unfold ltu iwordsize at H
      have : n < (32 : UInt32) := by simpa using H
      have : n.toNat < (32 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp this
      simp at this
      exact this
    by_cases hn0 : n.toNat = 0
    · -- Special case: n = 0, so shru x 0 = x and rolm x 32 mone = x
      rw [UInt32.eq_iff_toBitVec_eq]
      show (x >>> n).toBitVec = ((rol x (sub iwordsize n)).land (mone >>> n)).toBitVec
      have hshru : ∀ (a m : CompCert.Int), (a >>> m).toBitVec = a.toBitVec >>> (m.toNat % 32) := by
        intro a m; rfl
      rw [hshru]
      show x.toBitVec >>> (n.toNat % 32) = (rol x (sub iwordsize n)).toBitVec &&& (mone >>> n).toBitVec
      rw [rol_toBitVec, hshru]
      have hmone : mone.toBitVec = BitVec.allOnes 32 := by decide
      rw [hmone, hn0]
      have hsub0 : (sub iwordsize n).toNat % 32 = 0 := by
        unfold sub iwordsize
        show ((32 : UInt32) - n).toNat % 32 = 0
        rw [UInt32.toNat_sub]
        have h32 : (32 : UInt32).toNat = 32 := by decide
        rw [h32, hn0]
      rw [hsub0]
      apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < 32
      · simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, hi, Nat.zero_mod, Nat.sub_zero,
          decide_true, Bool.true_and]
        intro _
        simp [hi]
      · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]
        simp
    -- Main case: n.toNat > 0
    -- (sub 32 n).toNat = 32 - n.toNat
    have hsub : (sub iwordsize n).toNat = 32 - n.toNat := by
      unfold sub iwordsize
      show ((32 : UInt32) - n).toNat = 32 - n.toNat
      rw [UInt32.toNat_sub]
      have h32 : (32 : UInt32).toNat = 32 := by decide
      rw [h32]
      have : (2^32 - n.toNat + 32) = 2^32 + (32 - n.toNat) := by omega
      rw [this, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt32.eq_iff_toBitVec_eq]
    show (x >>> n).toBitVec = ((rol x (sub iwordsize n)).land (mone >>> n)).toBitVec
    have hshru : ∀ (a m : CompCert.Int), (a >>> m).toBitVec = a.toBitVec >>> (m.toNat % 32) := by
      intro a m; rfl
    rw [hshru]
    show x.toBitVec >>> (n.toNat % 32) = (rol x (sub iwordsize n)).toBitVec &&& (mone >>> n).toBitVec
    rw [rol_toBitVec, hshru]
    have hmone : mone.toBitVec = BitVec.allOnes 32 := by decide
    rw [hmone, hsub, Nat.mod_eq_of_lt hn]
    have hsubmod : (32 - n.toNat) % 32 = 32 - n.toNat := by
      apply Nat.mod_eq_of_lt
      have : 0 < n.toNat := Nat.pos_of_ne_zero hn0
      exact Nat.sub_lt (by decide) this
    rw [hsubmod]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 32
    · by_cases hin : i < 32 - n.toNat
      · -- When i < 32 - n.toNat, we have i + n.toNat < 32
        have hip : i + n.toNat < 32 := by omega
        have hmod : (32 - n.toNat) % 32 = 32 - n.toNat := hsubmod
        -- rotateLeft: since i < r % 32, use first branch: 32 - r % 32 + i = n.toNat + i
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, hi, hmod]
        -- Simplify the if-then-else
        rw [if_pos hin]
        -- Now: x.getLsbD (32 - (32 - n.toNat) + i) && decide (n.toNat + i < 32) = x.getLsbD (n.toNat + i)
        have hidx : 32 - (32 - n.toNat) + i = n.toNat + i := by omega
        rw [hidx]
        have hip' : n.toNat + i < 32 := by omega
        rw [decide_eq_true hip']
        simp
      · -- When i >= 32 - n.toNat, we have i + n.toNat >= 32
        have hip : ¬ (i + n.toNat < 32) := by omega
        have hmod : (32 - n.toNat) % 32 = 32 - n.toNat := hsubmod
        -- rotateLeft: since i >= r % 32, use second branch: i - r % 32 = i - (32 - n.toNat)
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, hi, hmod]
        -- Simplify the if-then-else
        rw [if_neg hin]
        have hip' : ¬ (n.toNat + i < 32) := by omega
        rw [decide_eq_false hip']
        simp
        rw [BitVec.getLsbD_of_ge]
        omega
    · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]
      simp

  -- Multiplication by 2^n equals shift left by n
  theorem mul_pow2_shl (x n : CompCert.Int) (H : ltu n iwordsize = true) :
      mul x (shl one n) = shl x n := by
    have hn : n.toNat < 32 := by
      unfold ltu iwordsize at H
      have : n < (32 : UInt32) := by simpa using H
      have : n.toNat < (32 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp this
      simp at this
      exact this
    rw [UInt32.eq_iff_toBitVec_eq]
    unfold mul shl one
    show (x * (1 <<< n)).toBitVec = (x <<< n).toBitVec
    have hmul : ∀ (a b : CompCert.Int), (a * b).toBitVec = a.toBitVec * b.toBitVec := by
      intro a b; rfl
    have hshl : ∀ (a m : CompCert.Int), (a <<< m).toBitVec = a.toBitVec <<< (m.toNat % 32) := by
      intro a m; rfl
    rw [hmul, hshl, hshl]
    have hone : (1 : CompCert.Int).toBitVec = (1 : BitVec 32) := by decide
    rw [hone]
    rw [Nat.mod_eq_of_lt hn]
    -- Goal: x.toBitVec * (1#32 <<< n.toNat) = x.toBitVec <<< n.toNat
    have h_shift_eq_twoPow : (1 : BitVec 32) <<< n.toNat = BitVec.twoPow 32 n.toNat := by
      rfl
    rw [h_shift_eq_twoPow]
    exact BitVec.mul_twoPow_eq_shiftLeft _ _

  -- Corollary: n.toNat is exactly 2^logn.toNat
  theorem is_power2_toNat_pow (n logn : CompCert.Int) (H : is_power2 n = some logn) :
      n.toNat = 2 ^ logn.toNat := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2_pow n logn H
    calc n.toNat
      _ = (shl one logn).toNat := by rw [← hn_eq]
      _ = ((1:UInt32) <<< logn).toNat := by rfl
      _ = (1:UInt32).toNat <<< (logn.toNat % 32) % 2^32 := by exact UInt32.toNat_shiftLeft 1 logn
      _ = 1 <<< logn.toNat % 2^32 := by rw [show (1:UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt hlogn_lt]
      _ = 2 ^ logn.toNat % 2^32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
      _ = 2 ^ logn.toNat := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlogn_lt)

  -- Unsigned division by 2^n equals logical shift right by n
  theorem divu_pow2 (x n logn : CompCert.Int)
      (H : is_power2 n = some logn) :
      divu x n = shru x logn := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2_pow n logn H
    have hn_toNat : n.toNat = 2 ^ logn.toNat := is_power2_toNat_pow n logn H
    have hn_pos : 0 < n.toNat := by rw [hn_toNat]; exact Nat.two_pow_pos _
    apply UInt32.toNat.inj
    unfold divu shru
    -- LHS: (repr (x.toNat / n.toNat)).toNat = x.toNat / n.toNat
    have h_divu : (repr ((x.unsigned : _root_.Int) / (n.unsigned : _root_.Int))).toNat
                  = x.toNat / n.toNat := by
      unfold repr unsigned
      rw [uint32_ofInt_toNat]
      have hnn : (0 : _root_.Int) ≤ (x.toNat : _root_.Int) / (n.toNat : _root_.Int) :=
        Int.ediv_nonneg (by omega : (0:_root_.Int) ≤ x.toNat) (by omega : (0:_root_.Int) ≤ n.toNat)
      have hbd : (x.toNat : _root_.Int) / (n.toNat : _root_.Int) < 2 ^ 32 := by
        have hx : x.toNat < 2 ^ 32 := x.toBitVec.isLt
        have h1 : (x.toNat : _root_.Int) / (n.toNat : _root_.Int) ≤ (x.toNat : _root_.Int) :=
          Int.ediv_le_self _ (by omega : (0:_root_.Int) ≤ x.toNat)
        have h2 : (x.toNat : _root_.Int) < (2 ^ 32 : _root_.Int) := by omega
        omega
      rw [Int.emod_eq_of_lt hnn hbd]
      rw [show ((x.toNat : _root_.Int) / (n.toNat : _root_.Int))
            = ((x.toNat / n.toNat : Nat) : _root_.Int) from by
        exact (Int.natCast_div _ _).symm]
      exact Int.toNat_natCast _
    rw [h_divu]
    -- RHS: (x >>> logn).toNat = x.toNat >>> logn.toNat = x.toNat / 2^logn.toNat
    have h_shru : (x >>> logn).toBitVec.toNat = x.toNat >>> logn.toNat := by
      change (x >>> logn).toNat = x.toNat >>> logn.toNat
      have : (x >>> logn).toNat = x.toNat >>> (logn.toNat % 32) := UInt32.toNat_shiftRight x logn
      rw [this, Nat.mod_eq_of_lt hlogn_lt]
    show x.toNat / n.toNat = (x >>> logn).toBitVec.toNat
    rw [h_shru, Nat.shiftRight_eq_div_pow, hn_toNat]


  -- Unsigned modulo by 2^n equals AND with n-1
  theorem modu_pow2 (x n logn : CompCert.Int)
      (H : is_power2 n = some logn) :
      modu x n = and x (sub n one) := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2_pow n logn H
    have hn_toNat : n.toNat = 2 ^ logn.toNat := is_power2_toNat_pow n logn H
    have hn_pos : 0 < n.toNat := by rw [hn_toNat]; exact Nat.two_pow_pos _
    apply UInt32.toNat.inj
    unfold modu and sub one
    -- LHS: (repr (x.toNat % n.toNat)).toNat = x.toNat % n.toNat
    have h_modu : (repr ((x.toNat : _root_.Int) % (n.toNat : _root_.Int))).toNat =
                  x.toNat % n.toNat := by
      unfold repr
      have h_mod_pos : (x.toNat : _root_.Int) % (n.toNat : _root_.Int) ≥ 0 := by
        apply Int.emod_nonneg
        omega
      have h_mod_bound : (x.toNat : _root_.Int) % (n.toNat : _root_.Int) < 2^32 := by
        have : (x.toNat : _root_.Int) % (n.toNat : _root_.Int) < n.toNat := by
          apply Int.emod_lt_of_pos
          omega
        have : n.toNat < 2^32 := n.toBitVec.isLt
        omega
      have : ((x.toNat : _root_.Int) % (n.toNat : _root_.Int)) % (2^32 : _root_.Int) =
             (x.toNat : _root_.Int) % (n.toNat : _root_.Int) := by
        apply Int.emod_eq_of_lt h_mod_pos h_mod_bound
      show (UInt32.ofInt ((x.toNat : _root_.Int) % (n.toNat : _root_.Int))).toBitVec.toNat = x.toNat % n.toNat
      unfold UInt32.ofInt
      rw [this]
      -- Goal: (UInt32.ofNat ((x.toNat : Int) % (n.toNat : Int)).toNat).toBitVec.toNat = x.toNat % n.toNat
      change (BitVec.ofNat 32 ((x.toNat : _root_.Int) % (n.toNat : _root_.Int)).toNat).toNat = x.toNat % n.toNat
      rw [BitVec.toNat_ofNat]
      -- Goal: ((x.toNat : Int) % (n.toNat : Int)).toNat % 2^32 = x.toNat % n.toNat
      have h_toNat : ((x.toNat : _root_.Int) % (n.toNat : _root_.Int)).toNat = x.toNat % n.toNat :=
        (Int.toNat_emod (by omega : (0:_root_.Int) ≤ x.toNat) (by omega : (0:_root_.Int) ≤ n.toNat)).symm
      rw [h_toNat]
      exact Nat.mod_eq_of_lt (by have : x.toNat % n.toNat < n.toNat := Nat.mod_lt _ hn_pos; omega)
    -- After applying UInt32.toNat.inj, goal is: (modu x n).toNat = (and x (sub n one)).toNat
    show (modu x n).toNat = (and x (sub n one)).toNat
    -- Simplify LHS using h_modu
    unfold modu unsigned at *
    calc (repr ((x.toNat : _root_.Int) % (n.toNat : _root_.Int))).toNat
      _ = x.toNat % n.toNat := h_modu
      _ = x.toNat &&& (2^logn.toNat - 1) := by
        rw [hn_toNat]
        exact (Nat.and_two_pow_sub_one_eq_mod x.toNat logn.toNat).symm
      _ = x.toNat &&& (n - 1).toNat := by
        have hn_sub_one : (n - 1).toNat = 2^logn.toNat - 1 := by
          calc (n - 1).toNat
            _ = (2^32 - 1 + n.toNat) % 2^32 := UInt32.toNat_sub n 1
            _ = (2^32 - 1 + 2^logn.toNat) % 2^32 := by rw [hn_toNat]
            _ = 2^logn.toNat - 1 := by
              have h_pow_bound : 2^logn.toNat < 2^32 := Nat.pow_lt_pow_right (by omega : 1 < 2) hlogn_lt
              have h_pow_pos : 1 ≤ 2^logn.toNat := by
                have : 0 < 2^logn.toNat := Nat.two_pow_pos _
                omega
              have h_add_rearr : 2^32 - 1 + 2^logn.toNat = 2^32 + (2^logn.toNat - 1) := by omega
              rw [h_add_rearr]
              have h_mod_lt : 2^logn.toNat - 1 < 2^32 := by omega
              calc (2^32 + (2^logn.toNat - 1)) % 2^32
                _ = ((2^32 % 2^32) + (2^logn.toNat - 1) % 2^32) % 2^32 := Nat.add_mod _ _ _
                _ = (0 + (2^logn.toNat - 1)) % 2^32 := by simp
                _ = (2^logn.toNat - 1) % 2^32 := by simp
                _ = 2^logn.toNat - 1 := Nat.mod_eq_of_lt h_mod_lt
        rw [hn_sub_one]
      _ = (and x (sub n one)).toNat := by
        unfold and sub one
        calc x.toNat &&& (n - 1).toNat
          _ = x.toBitVec.toNat &&& (n - 1).toBitVec.toNat := by rfl
          _ = (x.toBitVec &&& (n - 1).toBitVec).toNat := (BitVec.toNat_and _ _).symm
          _ = (x &&& (n - 1)).toBitVec.toNat := by rfl
          _ = (x &&& (n - 1)).toNat := by rfl

  -- Helper: add x zero = x
  @[simp] theorem add_zero (x : CompCert.Int) : add x zero = x := by
    unfold add zero
    exact UInt32.add_zero x

  -- Floor-division rounding facts (generalized over a positive divisor d).
  -- When d divides a, adding d-1 does not change the floor quotient.
  private theorem ediv_add_pred_of_dvd (a : _root_.Int) (d : _root_.Int) (hd : 0 < d)
      (hdvd : a % d = 0) :
      (a + (d - 1)) / d = a / d := by
    obtain ⟨q, hq⟩ := _root_.Int.dvd_of_emod_eq_zero hdvd
    subst hq
    rw [_root_.Int.mul_ediv_cancel_left _ (by omega)]
    rw [show d * q + (d - 1) = q * d + (d - 1) by ring]
    rw [_root_.Int.mul_add_ediv_right _ _ (by omega : d ≠ 0)]
    have : (d - 1) / d = 0 := by
      apply _root_.Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega

  -- `1 <<< k - 1` elaborated at `Int` (as in `shrx`'s rounding term) is `2^k - 1`.
  theorem int_one_shiftLeft_sub_one (k : Nat) :
      ((1 : _root_.Int) <<< k - 1) = ((2 ^ k : Nat) : _root_.Int) - 1 := by
    rw [_root_.Int.shiftLeft_eq, _root_.Int.one_mul]
    push_cast
    rfl

  -- `simp`-normalized form of the same rounding term: `↑(1 <<< k) - 1 = ↑(2^k) - 1`.
  theorem natCast_one_shiftLeft_sub_one (k : Nat) :
      (((1 <<< k : Nat) : _root_.Int) - 1) = ((2 ^ k : Nat) : _root_.Int) - 1 := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]

  -- When d does NOT divide a, adding d-1 bumps the floor quotient up by one.
  private theorem ediv_add_pred_of_not_dvd (a : _root_.Int) (d : _root_.Int) (hd : 0 < d)
      (hnd : a % d ≠ 0) :
      (a + (d - 1)) / d = a / d + 1 := by
    have hdecomp : a = d * (a / d) + a % d := (_root_.Int.mul_ediv_add_emod a d).symm
    have hmod_lt : a % d < d := _root_.Int.emod_lt_of_pos a hd
    have hmod_nonneg : 0 ≤ a % d := _root_.Int.emod_nonneg a (by omega)
    have hmod_pos : 0 < a % d := by omega
    -- a + (d-1) = d*(a/d) + (a%d + d - 1); with 0 < a%d < d, floor is (a/d) + 1
    conv_lhs => rw [hdecomp]
    -- Now we have (d * (a / d) + a % d + (d - 1)) / d
    rw [show d * (a / d) + a % d + (d - 1) = (a % d + (d - 1)) + (a / d) * d by ring]
    rw [_root_.Int.add_mul_ediv_right _ _ (by omega : d ≠ 0)]
    have : (a % d + (d - 1)) / d = 1 := by
      have h3' : a % d + (d - 1) < d + d := by omega
      have : 1 * d ≤ a % d + (d - 1) ∧ a % d + (d - 1) < 1 * d + d := by
        simp; exact ⟨by omega, h3'⟩
      exact (_root_.Int.ediv_eq_iff_of_pos hd).mpr this
    omega

  -- Bridge: the masked low bits of x (as Nat) are nonzero iff x.signed is not divisible by 2^k,
  -- for k < 31 (so 2^k ∣ 2^32).
  private theorem shrx_low_bits_ne_iff (x : CompCert.Int) (k : Nat) (hk : k < 31) :
      (x.unsigned &&& ((1 <<< k) - 1) ≠ 0) ↔ x.signed % (2 ^ k : _root_.Int) ≠ 0 := by
    have hmask : (1 : Nat) <<< k - 1 = 2 ^ k - 1 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hmask]
    -- Nat and-mask = mod
    have hand : x.unsigned &&& (2 ^ k - 1) = x.unsigned % 2 ^ k :=
      Nat.and_two_pow_sub_one_eq_mod x.unsigned k
    rw [hand]
    -- x.unsigned % 2^k (Nat) = 0 ↔ x.signed % 2^k (Int) = 0
    constructor
    · intro h hc
      apply h
      -- from x.signed % 2^k = 0 (Int) deduce x.unsigned % 2^k = 0 (Nat)
      have hcong : (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int) = x.signed % (2 ^ k : _root_.Int) := by
        have hdvd : (2 ^ k : _root_.Int) ∣ (2 ^ 32 : _root_.Int) := pow_dvd_pow 2 (by omega)
        have hsig : x.signed % (2 ^ 32 : _root_.Int) = (x.unsigned : _root_.Int) % (2 ^ 32 : _root_.Int) := by
          have := signed_mod_eq_toNat_mod x
          simpa [unsigned] using this
        calc (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int)
            = ((x.unsigned : _root_.Int) % (2 ^ 32 : _root_.Int)) % (2 ^ k : _root_.Int) :=
              (Int.emod_emod_of_dvd _ hdvd).symm
          _ = (x.signed % (2 ^ 32 : _root_.Int)) % (2 ^ k : _root_.Int) := by rw [hsig]
          _ = x.signed % (2 ^ k : _root_.Int) := Int.emod_emod_of_dvd _ hdvd
      rw [hc] at hcong
      have : ((x.unsigned % 2 ^ k : Nat) : _root_.Int) = 0 := by
        rw [Int.natCast_mod]; exact hcong
      omega
    · intro h hc
      apply h
      have hcong : (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int) = x.signed % (2 ^ k : _root_.Int) := by
        have hdvd : (2 ^ k : _root_.Int) ∣ (2 ^ 32 : _root_.Int) := pow_dvd_pow 2 (by omega)
        have hsig : x.signed % (2 ^ 32 : _root_.Int) = (x.unsigned : _root_.Int) % (2 ^ 32 : _root_.Int) := by
          have := signed_mod_eq_toNat_mod x
          simpa [unsigned] using this
        calc (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int)
            = ((x.unsigned : _root_.Int) % (2 ^ 32 : _root_.Int)) % (2 ^ k : _root_.Int) :=
              (Int.emod_emod_of_dvd _ hdvd).symm
          _ = (x.signed % (2 ^ 32 : _root_.Int)) % (2 ^ k : _root_.Int) := by rw [hsig]
          _ = x.signed % (2 ^ k : _root_.Int) := Int.emod_emod_of_dvd _ hdvd
      -- Goal: x.signed % 2^k = 0
      -- We have hcong : (x.unsigned : Int) % 2^k = x.signed % 2^k
      -- and hc : x.unsigned % 2^k = 0 (Nat)
      rw [← hcong]
      have hc_int : ((x.unsigned % 2^k : Nat) : _root_.Int) = 0 := by omega
      rw [Int.natCast_mod] at hc_int
      exact hc_int

  -- `sub (shl one q) one` is the mask `2^q - 1`, with signed value `2^q - 1` for q < 31.
  theorem shl_one_sub_one_signed (q : CompCert.Int) (hq : q.toNat < 31) :
      CompCert.Int.signed (sub (shl one q) one) = (2 ^ q.toNat : _root_.Int) - 1 := by
    have hshl : (shl one q).toNat = 2 ^ q.toNat := by
      show (UInt32.shiftLeft 1 q).toNat = 2 ^ q.toNat
      rw [show (UInt32.shiftLeft 1 q) = (1 : UInt32) <<< q from rfl, UInt32.toNat_shiftLeft]
      have h1 : (1 : UInt32).toNat = 1 := by rfl
      rw [h1, Nat.mod_eq_of_lt (by omega : q.toNat < 32), Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    have hsub : (sub (shl one q) one).toNat = 2 ^ q.toNat - 1 := by
      show ((shl one q) - one).toNat = 2 ^ q.toNat - 1
      rw [UInt32.toNat_sub]
      have hone : (one : CompCert.Int).toNat = 1 := by rfl
      rw [hone, hshl]
      have hp : 2 ^ q.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) (by omega)
      have hp1 : (1 : Nat) ≤ 2 ^ q.toNat := Nat.one_le_two_pow
      have : (2 ^ 32 - 1 + 2 ^ q.toNat) % 2 ^ 32 = 2 ^ q.toNat - 1 := by omega
      exact this
    -- signed = toNat since 2^q - 1 < 2^31
    have hlt : 2 ^ q.toNat - 1 < 2 ^ 31 := by
      have : 2 ^ q.toNat < 2 ^ 31 := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hsigned : CompCert.Int.signed (sub (shl one q) one)
        = ((sub (shl one q) one).toNat : _root_.Int) := by
      unfold signed
      rw [show (sub (shl one q) one).toNat = (sub (shl one q) one).toBitVec.toNat from rfl] at hsub
      have h2n : 2 * (sub (shl one q) one).toBitVec.toNat < 2 ^ 32 := by
        rw [hsub]
        have : 2 ^ q.toNat < 2 ^ 31 := Nat.pow_lt_pow_right (by omega) (by omega)
        have hp1 : (1 : Nat) ≤ 2 ^ q.toNat := Nat.one_le_two_pow
        omega
      rw [BitVec.toInt_eq_toNat_of_lt h2n]
      rfl
    rw [hsigned, hsub]
    have hp1 : (1 : Nat) ≤ 2 ^ q.toNat := Nat.one_le_two_pow
    push_cast [Nat.cast_sub hp1]
    ring

  -- shrx for a negative argument equals shr of the rounded value `p + (2^q - 1)`.
  theorem shrx_shr_neg_eq (p q : CompCert.Int) (hp : p.signed < 0) (hq : q.toNat < 31) :
      shrx p q = shr (add p (sub (shl one q) one)) q := by
    have hmask : CompCert.Int.signed (sub (shl one q) one) = (2 ^ q.toNat : _root_.Int) - 1 :=
      shl_one_sub_one_signed q hq
    have hrange_lo : -(2^31 : _root_.Int) ≤ p.signed + CompCert.Int.signed (sub (shl one q) one) := by
      rw [hmask]
      have hplo : -(2^31 : _root_.Int) ≤ p.signed := by
        have := @BitVec.le_toInt 32 p.toBitVec
        simpa [signed] using this
      have hpk : (1 : _root_.Int) ≤ 2 ^ q.toNat := by
        exact_mod_cast Nat.one_le_two_pow
      omega
    have hrange_hi : p.signed + CompCert.Int.signed (sub (shl one q) one) < (2^31 : _root_.Int) := by
      rw [hmask]
      have hpk : (2 ^ q.toNat : _root_.Int) < 2 ^ 31 := by
        have : (2:Nat) ^ q.toNat < 2 ^ 31 := Nat.pow_lt_pow_right (by omega) (by omega)
        exact_mod_cast this
      omega
    have hadd : CompCert.Int.signed (add p (sub (shl one q) one))
              = p.signed + ((2 ^ q.toNat : _root_.Int) - 1) := by
      rw [add_signed_eq_of_range p (sub (shl one q) one) hrange_lo hrange_hi, hmask]
    unfold shrx shr
    simp only [show ¬(p.signed ≥ 0) by omega, if_false]
    rw [Nat.mod_eq_of_lt (by omega : q.toNat < 32)]
    rw [hadd]
    congr 2
    -- ↑(1 <<< q.toNat - 1 : Nat) = 2^q.toNat - 1
    have hpk : (1 : Nat) ≤ 1 <<< q.toNat := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.one_le_two_pow
    rw [Nat.cast_sub hpk]
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    push_cast
    ring

  -- Main theorem: shrx_carry identity
  theorem shrx_carry_eq (x y : CompCert.Int) (H : y.toNat < 31) :
      add (shr x y) (shr_carry x y) = shrx x y := by
    unfold shr shr_carry shrx add
    simp only []
    have shamt_eq : y.toNat % 32 = y.toNat := Nat.mod_eq_of_lt (by omega : y.toNat < 32)
    by_cases hx : x.signed ≥ 0
    case pos =>
      -- Case x.signed ≥ 0: shr_carry = zero, shrx = shr
      simp [hx, show ¬(x.signed < 0) by omega, shamt_eq]
      -- Goal: repr (x.signed >>> y.toNat) + zero = repr (x.signed >>> y.toNat)
      exact UInt32.add_zero _
    case neg =>
      -- Case x.signed < 0
      simp [show ¬(x.signed ≥ 0) by omega, shamt_eq]
      set shamt := y.toNat
      set low_bits := x.unsigned &&& ((1 <<< shamt) - 1)
      -- Simplify the condition
      have hxneg : x.signed < 0 := by omega
      by_cases hlow : low_bits ≠ 0
      case pos =>
        -- low_bits ≠ 0 AND x.signed < 0, so shr_carry = one
        simp [hxneg, hlow]
        -- Goal: repr (x.signed >>> shamt) + one = repr ((x.signed + (1 <<< shamt - 1)) >>> shamt)
        have hd : (0 : _root_.Int) < (2 ^ shamt : _root_.Int) := by
          have : 0 < 2 ^ shamt := Nat.two_pow_pos shamt
          exact Nat.cast_lt.mpr this
        have hcast : ((1 <<< shamt - 1 : Nat) : _root_.Int) = (2 ^ shamt : _root_.Int) - 1 := by
          have h1 : (1 : Nat) <<< shamt = 2 ^ shamt := by rw [Nat.shiftLeft_eq, Nat.one_mul]
          have hle : (1 : Nat) ≤ 2 ^ shamt := Nat.one_le_two_pow
          rw [show (1 <<< shamt - 1 : Nat) = 2 ^ shamt - 1 by rw [← h1]]
          rw [Nat.cast_sub hle]
          simp
        have hnd : x.signed % (2 ^ shamt : _root_.Int) ≠ 0 := by
          exact shrx_low_bits_ne_iff x shamt (by omega) |>.mp hlow
        rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, CompCert.Int.int_one_shiftLeft_sub_one]
        push_cast
        rw [ediv_add_pred_of_not_dvd x.signed (2 ^ shamt : _root_.Int) hd hnd]
        -- repr (q + 1) = repr q + one
        rw [show (x.signed / (2^shamt : _root_.Int) + 1)
              = (x.signed / (2^shamt : _root_.Int)) + 1 from rfl]
        show add (repr (x.signed / (2^shamt:_root_.Int))) one
           = repr ((x.signed / (2^shamt:_root_.Int)) + 1)
        -- Since add = UInt32.add and repr = UInt32.ofInt, and one = repr 1 = UInt32.ofInt 1
        -- we need: UInt32.add (UInt32.ofInt a) (UInt32.ofInt 1) = UInt32.ofInt (a + 1)
        unfold add one repr
        apply UInt32.toNat.inj
        change (UInt32.ofInt (x.signed / 2 ^ shamt) + (UInt32.ofInt 1)).toNat = (UInt32.ofInt (x.signed / 2 ^ shamt + 1)).toNat
        rw [UInt32.toNat_add]
        have h1 : (UInt32.ofInt (x.signed / 2 ^ shamt)).toNat = ((x.signed / 2 ^ shamt) % 2^32).toNat := uint32_ofInt_toNat _
        have h2 : (UInt32.ofInt 1).toNat = 1 := by decide
        have h3 : (UInt32.ofInt ((x.signed / 2 ^ shamt) + 1)).toNat = (((x.signed / 2 ^ shamt) + 1) % 2^32).toNat := uint32_ofInt_toNat _
        rw [h1, h2, h3]
        have ha : 0 ≤ (x.signed / 2 ^ shamt) % 2^32 := Int.emod_nonneg _ (by omega)
        have hb : (x.signed / 2 ^ shamt) % 2^32 < 2^32 := Int.emod_lt_of_pos _ (by omega)
        omega
      case neg =>
        -- low_bits = 0, so shr_carry = zero (the && short-circuits)
        have hlow0 : low_bits = 0 := by omega
        simp [hxneg, hlow0]
        show UInt32.add (repr (x.signed >>> shamt)) zero = repr ((x.signed + (1 <<< shamt - 1)) >>> shamt)
        conv_lhs => rw [show UInt32.add (repr (x.signed >>> shamt)) zero = repr (x.signed >>> shamt) by exact UInt32.add_zero _]
        have hd : (0 : _root_.Int) < (2 ^ shamt : _root_.Int) := by
          have : 0 < 2 ^ shamt := Nat.two_pow_pos shamt
          exact Nat.cast_lt.mpr this
        have hdvd : x.signed % (2 ^ shamt : _root_.Int) = 0 := by
          by_contra h
          exact hlow ((shrx_low_bits_ne_iff x shamt (by omega)).mpr h)
        rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, CompCert.Int.natCast_one_shiftLeft_sub_one]
        push_cast
        rw [ediv_add_pred_of_dvd x.signed (2 ^ shamt : _root_.Int) hd hdvd]

  -- Key lemma: for negative dividend and positive power-of-2 divisor,
  -- tdiv equals ediv with rounding correction
  -- This is the toward-zero division identity for powers of 2
  private theorem tdiv_pow2_neg_eq_ediv_round (a : _root_.Int) (k : Nat) (ha : a < 0) :
      Int.tdiv a (2^k : _root_.Int) = (a + (2^k : _root_.Int) - 1) / (2^k : _root_.Int) := by
    set d := (2^k : _root_.Int)
    have hd : 0 < d := by apply _root_.Int.pow_pos; omega
    -- Key: Int.tdiv_eq_ediv gives a.tdiv d = a / d + if (0 ≤ a ∨ d ∣ a) then 0 else d.sign
    -- Since a < 0, the condition simplifies to d ∣ a, and d.sign = 1 (since d > 0)
    rw [_root_.Int.tdiv_eq_ediv]
    have ha_neg : ¬(0 ≤ a) := by omega
    have hsign : d.sign = 1 := _root_.Int.sign_eq_one_iff_pos.mpr hd
    -- Simplify the conditional: since ¬(0 ≤ a), the condition becomes (d ∣ a)
    simp only [ha_neg, false_or]
    rw [hsign]
    -- Now split on divisibility
    by_cases hdvd : d ∣ a
    · -- Case: d divides a
      simp [hdvd]
      have h : a % d = 0 := _root_.Int.dvd_iff_emod_eq_zero.mp hdvd
      rw [show (a + d - 1) / d = (a + (d - 1)) / d by ring_nf]
      exact (ediv_add_pred_of_dvd a d hd h).symm
    · -- Case: d does not divide a
      simp [hdvd]
      have h : a % d ≠ 0 := by
        intro heq
        exact hdvd (_root_.Int.dvd_iff_emod_eq_zero.mpr heq)
      rw [show (a + d - 1) / d = (a + (d - 1)) / d by ring_nf]
      exact (ediv_add_pred_of_not_dvd a d hd h).symm

  -- Signed division by 2^n equals shrx n (for n < 31)
  -- This bridges tdiv semantics with the shrx implementation
  theorem divs_pow2_eq (x n logn : CompCert.Int)
      (H1 : is_power2 n = some logn)
      (H2 : logn.toNat < 31) :
      divs x n = shrx x logn := by
    -- From H1: n = 2^logn.toNat and n.signed = 2^logn.toNat (positive)
    have ⟨hn_eq, hlogn_lt⟩ := is_power2_pow n logn H1
    have hn_toNat : n.toNat = 2 ^ logn.toNat := is_power2_toNat_pow n logn H1
    have hn_pos : 0 < n.toNat := by rw [hn_toNat]; exact Nat.two_pow_pos _

    -- Key: n.toNat < 2^31, so n.signed = n.toNat (n is positive)
    have hn_signed_eq : n.signed = (n.toNat : _root_.Int) := by
      unfold signed
      have h_bound : n.toNat < 2^31 := by
        rw [hn_toNat]
        exact Nat.pow_lt_pow_right (by omega) H2
      have h_bound' : n.toNat < 2^32 := by omega
      -- For x.toNat < 2^31, x.toBitVec.toInt = x.toNat
      have : n.toBitVec.toInt = (n.toNat : _root_.Int) := by
        have h2n : 2 * n.toBitVec.toNat < 2^32 := by
          have : n.toBitVec.toNat = n.toNat := by rfl
          rw [this]
          have : n.toNat < 2^31 := h_bound
          omega
        exact BitVec.toInt_eq_toNat_of_lt h2n
      exact this

    -- Unfold definitions
    unfold divs shrx
    apply UInt32.toNat.inj

    -- Substitute the key facts: n.signed = 2^logn.toNat
    have hn_signed_pow : n.signed = (2 ^ logn.toNat : _root_.Int) := by
      rw [hn_signed_eq, hn_toNat]
      simp [Nat.cast_pow]

    rw [hn_signed_pow]

    -- Split on x.signed ≥ 0
    by_cases hx : x.signed ≥ 0
    case pos =>
      simp only [hx, ite_true]
      have htdiv_eq : x.signed.tdiv (2^logn.toNat : _root_.Int) = x.signed / (2^logn.toNat : _root_.Int) := by
        exact Int.tdiv_eq_ediv_of_nonneg hx
      rw [htdiv_eq]
      have hshr : (x.signed >>> logn.toNat) = x.signed / (↑(2 ^ logn.toNat) : _root_.Int) := Int.shiftRight_eq_div_pow x.signed logn.toNat
      rw [hshr]
    case neg =>
      -- x.signed < 0: shrx = repr ((x.signed + (1 <<< logn.toNat - 1)) >>> logn.toNat)
      simp only [show ¬(x.signed ≥ 0) from by omega, ite_false]
      -- Goal: (repr (x.signed.tdiv (2^logn.toNat))).toNat = (repr ((x.signed + (1 <<< logn.toNat - 1)) >>> logn.toNat)).toNat
      rw [Int.shiftRight_eq_div_pow]

      -- Key identity: for a < 0, d = 2^k: a.tdiv d = (a + d - 1) / d (ediv)
      have hcast : ((1 <<< logn.toNat - 1 : Nat) : _root_.Int) = (2 ^ logn.toNat : _root_.Int) - 1 := by
        have h1 : (1 : Nat) <<< logn.toNat = 2 ^ logn.toNat := by rw [Nat.shiftLeft_eq, Nat.one_mul]
        have hle : (1 : Nat) ≤ 2 ^ logn.toNat := Nat.one_le_two_pow
        rw [show (1 <<< logn.toNat - 1 : Nat) = 2 ^ logn.toNat - 1 from by rw [← h1]]
        rw [Nat.cast_sub hle]
        simp
      rw [hcast]
      push_cast

      -- Use the tdiv-to-ediv formula for negative numbers with power-of-2 divisor
      have htdiv_formula : x.signed.tdiv (2^logn.toNat : _root_.Int) = (x.signed + (2^logn.toNat : _root_.Int) - 1) / (2^logn.toNat : _root_.Int) := by
        exact tdiv_pow2_neg_eq_ediv_round x.signed logn.toNat (by omega)
      rw [htdiv_formula]
      -- The RHS has `(x.signed + (2^k - 1))` which equals `x.signed + 2^k - 1` by algebra
      have : x.signed + (2 ^ logn.toNat : _root_.Int) - 1 = x.signed + ((2 ^ logn.toNat : _root_.Int) - 1) := by ring
      rw [this]

  -- Helper: shr by 31 (sign bit position) produces 0 if non-negative, -1 if negative
  private theorem shr_31_eq (p : CompCert.Int) :
      shr p (repr 31) = if p.signed < 0 then mone else zero := by
    unfold shr repr mone zero
    simp only []
    have h31 : ((UInt32.ofInt 31).toNat : Nat) % 32 = 31 := by decide
    rw [h31]
    -- p.signed ∈ [-2^31, 2^31), so p.signed >>> 31 ∈ {-1, 0}
    have hrange_lo : -(2^31 : _root_.Int) ≤ p.signed := by
      have := @BitVec.le_toInt 32 p.toBitVec
      simpa [signed] using this
    have hrange_hi : p.signed < (2^31 : _root_.Int) := by
      have := @BitVec.toInt_lt 32 p.toBitVec
      simpa [signed] using this
    have : p.signed >>> 31 = if p.signed < 0 then -1 else 0 := by
      rw [Int.shiftRight_eq_div_pow]
      by_cases hn : p.signed < 0
      · simp [hn]
        -- p.signed ∈ [-2^31, 0), so p.signed / 2^31 = -1 (floor division)
        omega
      · simp [hn]
        -- p.signed ∈ [0, 2^31), so p.signed / 2^31 = 0
        omega
    rw [this]
    by_cases hp : p.signed < 0 <;> simp [hp]; rfl

  -- Key lemma: shru (shr p 31) (32-n) is the sign mask (0 or 2^n-1)
  theorem sign_mask_eq (p n : CompCert.Int) (hn0 : n.toNat ≠ 0) (hn : n.toNat < 31) :
      shru (shr p (repr 31)) (sub (repr 32) n)
        = if p.signed < 0 then sub (shl one n) one else zero := by
    rw [shr_31_eq]
    have hsub_calc : (UInt32.ofInt 32) - n = (UInt32.ofInt 32).sub n := rfl
    have hsub_toNat : ((UInt32.ofInt 32).sub n).toNat = 32 - n.toNat := by
      rw [← hsub_calc]
      have h32 : (UInt32.ofInt 32).toNat = 32 := by decide
      rw [UInt32.toNat_sub, h32]
      have hn32 : n.toNat < 32 := by omega
      have hnlt : n.toNat < 2^32 := n.toBitVec.isLt
      omega
    set k := 32 - n.toNat
    by_cases hp : p.signed < 0
    case pos =>
      -- p < 0: shru mone (sub (repr 32) n) = 2^n - 1 = sub (shl one n) one
      simp only [hp, if_true]
      have hallOnes_shift : ∀ m : Nat, m < 32 → m > 0 →
          (BitVec.allOnes 32 >>> m).toNat = 2^(32 - m) - 1 := by
        intro m hm1 hm2
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_allOnes]
        rw [Nat.shiftRight_eq_div_pow]
        have hsplit : (2:Nat)^32 = 2^(32 - m) * 2^m := by
          rw [← Nat.pow_add]; congr 1; omega
        have hpm : 0 < (2:Nat)^m := Nat.two_pow_pos m
        have hc : 0 < (2:Nat)^(32-m) := Nat.two_pow_pos (32-m)
        apply Nat.div_eq_of_lt_le
        · have : (2^(32-m) - 1) * 2^m = 2^32 - 2^m := by
            rw [Nat.sub_mul, Nat.one_mul, ← hsplit]
          omega
        · have : (2^(32-m) - 1 + 1) * 2^m = 2^32 := by
            rw [Nat.sub_add_cancel hc, ← hsplit]
          omega
      apply UInt32.toNat.inj
      -- LHS: (shru mone (sub (repr 32) n)).toNat
      have hlhs : (shru mone (sub (repr 32) n)).toNat = 2^n.toNat - 1 := by
        show ((mone : CompCert.Int) >>> (sub (repr 32) n)).toNat = 2^n.toNat - 1
        rw [show ((mone : CompCert.Int) >>> (sub (repr 32) n))
              = UInt32.ofBitVec ((mone : CompCert.Int).toBitVec >>> ((sub (repr 32) n).toNat % 32)) from rfl]
        rw [UInt32.toNat_ofBitVec]
        have hmone_bv : (mone : CompCert.Int).toBitVec = BitVec.allOnes 32 := by decide
        rw [hmone_bv]
        have hkmod : ((sub (repr 32) n).toNat % 32) = 32 - n.toNat := by
          rw [show (sub (repr 32) n) = (UInt32.ofInt 32).sub n from rfl] at *
          rw [hsub_toNat]; exact Nat.mod_eq_of_lt (by omega)
        rw [hkmod, hallOnes_shift (32 - n.toNat) (by omega) (by omega)]
        have hee : 32 - (32 - n.toNat) = n.toNat := by omega
        rw [hee]
      -- RHS: (sub (shl one n) one).toNat = 2^n.toNat - 1
      have hrhs : (sub (shl one n) one).toNat = 2^n.toNat - 1 := by
        show ((shl one n) - one).toNat = 2^n.toNat - 1
        rw [UInt32.toNat_sub]
        have hshl : (shl one n).toNat = 2^n.toNat := by
          show (UInt32.shiftLeft 1 n).toNat = 2^n.toNat
          rw [show (UInt32.shiftLeft 1 n) = (1:UInt32) <<< n from rfl, UInt32.toNat_shiftLeft]
          have : (1:UInt32).toNat = 1 := by rfl
          rw [this, Nat.mod_eq_of_lt (by omega : n.toNat < 32), Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
        have hone : (one : CompCert.Int).toNat = 1 := by rfl
        rw [hone, hshl]
        have hp2 : 2^n.toNat < 2^32 := Nat.pow_lt_pow_right (by omega) (by omega)
        have hp1 : (1:Nat) ≤ 2^n.toNat := Nat.one_le_two_pow
        have : (2^32 - 1 + 2^n.toNat) % 2^32 = 2^n.toNat - 1 := by omega
        exact this
      rw [hlhs, hrhs]
    case neg =>
      -- p ≥ 0: shru zero (sub (repr 32) n) = zero
      simp [hp]
      unfold shru zero
      simp [UInt32.shiftRight]

  -- Main Int-level theorem: shrx p n equals the sign-broadcast formula
  theorem shrx_shr_2_eq (p n : CompCert.Int) (hn : n.toNat < 31) :
      shrx p n = if eq n zero then p else
        shr (add p (shru (shr p (repr 31)) (sub (repr 32) n))) n := by
    by_cases hn0 : n = zero
    · -- n = zero: shrx p 0 = p
      rw [hn0]
      have heq0 : eq zero zero = true := by unfold eq; simp
      rw [heq0]
      simp only [if_true]
      unfold shrx zero
      have hz : (0 : UInt32).toNat = 0 := rfl
      by_cases hp : p.signed ≥ 0
      · simp only [hp, if_true, hz, Int.shiftRight_zero]
        exact repr_signed p
      · simp only [hp, if_false, hz]
        have h10 : ((1 <<< 0 - 1 : Nat) : _root_.Int) = 0 := by decide
        rw [h10, Int.shiftRight_zero]
        simpa using repr_signed p
    · -- n ≠ zero
      have heq_false : eq n zero = false := by
        unfold eq zero; simp; exact hn0
      simp [heq_false]
      have hn_toNat : n.toNat ≠ 0 := by
        unfold zero at hn0
        intro h
        apply hn0
        apply UInt32.toNat.inj
        simpa using h
      -- Rewrite using sign_mask_eq
      rw [sign_mask_eq p n hn_toNat hn]
      by_cases hp : p.signed < 0
      · -- p < 0: use shrx_shr_neg_eq
        simp [hp]
        rw [← shrx_shr_neg_eq p n hp hn]
      · -- p ≥ 0
        simp [hp]
        unfold shrx shr
        have hge : p.signed ≥ 0 := by omega
        have hq32 : n.toNat % 32 = n.toNat := Nat.mod_eq_of_lt (by omega)
        simp [hge, hq32]

end CompCert.Int

namespace CompCert.Int64
  -- Conversion operations
  def unsigned (x : CompCert.Int64) : Nat := x.toNat
  def signed (x : CompCert.Int64) : _root_.Int := x.toBitVec.toInt
  def repr (z : _root_.Int) : CompCert.Int64 := UInt64.ofInt z

  -- Constants
  def zero : CompCert.Int64 := 0
  def one : CompCert.Int64 := 1
  def mone : CompCert.Int64 := UInt64.ofInt (-1)
  def iwordsize : CompCert.Int64 := 64
  def iwordsize' : CompCert.Int := 64
  def min_signed : _root_.Int := -9223372036854775808
  def max_signed : _root_.Int := 9223372036854775807
  def max_unsigned : _root_.Int := 18446744073709551615

  -- Arithmetic operations
  def add := UInt64.add
  def sub := UInt64.sub
  def mul := UInt64.mul
  def neg (x : CompCert.Int64) : CompCert.Int64 := UInt64.ofInt (-(x.toNat : _root_.Int))

  -- Advanced arithmetic
  def mul' (x y : CompCert.Int) : CompCert.Int64 :=
    -- Multiply two 32-bit signed ints to get 64-bit result
    repr (x.signed * y.signed)

  def mulhs (x y : CompCert.Int64) : CompCert.Int64 :=
    -- Signed multiply high: upper 64 bits of 128-bit result
    -- Approximate using Nat arithmetic (sign-correct for most cases)
    let prod := x.signed * y.signed
    repr (prod / 18446744073709551616)

  def mulhu (x y : CompCert.Int64) : CompCert.Int64 :=
    -- Unsigned multiply high
    let prod := (x.unsigned : _root_.Int) * (y.unsigned : _root_.Int)
    repr (prod / 18446744073709551616)

  def divs (x y : CompCert.Int64) : CompCert.Int64 :=
    -- Signed division (toward zero) to match CompCert semantics
    repr (Int.tdiv x.signed y.signed)

  theorem repr_signed (x : CompCert.Int64) : repr (x.signed) = x := by
    unfold repr signed
    rw [UInt64.eq_iff_toBitVec_eq]
    have hbv : (UInt64.ofInt (x.toBitVec.toInt)).toBitVec = BitVec.ofInt 64 (x.toBitVec.toInt) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : (UInt64.ofInt (x.toBitVec.toInt)).toBitVec
                  = BitVec.ofNat 64 ((x.toBitVec.toInt % 2^64).toNat) := rfl
      simp only [h1, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    rw [hbv]
    exact BitVec.ofInt_toInt

  -- Private helper lemmas for UInt64
  private lemma uint64_ofInt_toNat (z : _root_.Int) :
      (UInt64.ofInt z).toNat = (z % (2^64 : _root_.Int)).toNat := by
    have hnn : (0 : _root_.Int) ≤ z % (2^64 : _root_.Int) :=
      Int.emod_nonneg z (by omega)
    have hbound : (z % (2^64 : _root_.Int)).toNat < 2^64 := by
      have hlt : (z % (2^64 : _root_.Int)) < (2^64 : _root_.Int) :=
        Int.emod_lt_of_pos z (by omega)
      omega
    show (UInt64.ofInt z).toBitVec.toNat = _
    have h1 : (UInt64.ofInt z).toBitVec = BitVec.ofNat 64 ((z % 2^64).toNat) := rfl
    rw [h1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hbound

  private lemma uint64_ofInt_toBitVec (z : _root_.Int) :
      (UInt64.ofInt z).toBitVec = BitVec.ofInt 64 z := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (UInt64.ofInt z).toBitVec = BitVec.ofNat 64 ((z % 2^64).toNat) := rfl
    simp only [h1, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

  private lemma neg_toNat (x : CompCert.Int64) :
      (neg x).toNat = (-(x.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat := by
    unfold neg
    exact uint64_ofInt_toNat _

  -- Helper lemmas for repr as a homomorphism mod 2^64
  theorem repr_sub_hom (a b : _root_.Int) :
      repr (a - b) = UInt64.sub (repr a) (repr b) := by
    unfold repr
    apply UInt64.toNat.inj
    show (UInt64.ofInt (a - b)).toNat = (UInt64.ofInt a - UInt64.ofInt b).toNat
    have h1 : (UInt64.ofInt (a - b)).toNat = ((a - b) % (2^64 : _root_.Int)).toNat := by
      have hbound : ((a - b) % (2^64 : _root_.Int)).toNat < 2^64 := by
        have hlt : ((a - b) % (2^64 : _root_.Int)) < (2^64 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt64.ofInt (a - b)).toBitVec.toNat = _
      have : (UInt64.ofInt (a - b)).toBitVec = BitVec.ofNat 64 (((a - b) % 2^64).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h2 : (UInt64.ofInt a).toNat = (a % (2^64 : _root_.Int)).toNat := by
      have hbound : (a % (2^64 : _root_.Int)).toNat < 2^64 := by
        have hlt : (a % (2^64 : _root_.Int)) < (2^64 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt64.ofInt a).toBitVec.toNat = _
      have : (UInt64.ofInt a).toBitVec = BitVec.ofNat 64 ((a % 2^64).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h3 : (UInt64.ofInt b).toNat = (b % (2^64 : _root_.Int)).toNat := by
      have hbound : (b % (2^64 : _root_.Int)).toNat < 2^64 := by
        have hlt : (b % (2^64 : _root_.Int)) < (2^64 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt64.ofInt b).toBitVec.toNat = _
      have : (UInt64.ofInt b).toBitVec = BitVec.ofNat 64 ((b % 2^64).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    rw [h1, UInt64.toNat_sub, h2, h3]
    have ha : 0 ≤ a % (2^64 : _root_.Int) := Int.emod_nonneg _ (by omega)
    have hb : 0 ≤ b % (2^64 : _root_.Int) := Int.emod_nonneg _ (by omega)
    have hac : a % (2^64 : _root_.Int) < 2^64 := Int.emod_lt_of_pos _ (by omega)
    have hbc : b % (2^64 : _root_.Int) < 2^64 := Int.emod_lt_of_pos _ (by omega)
    omega

  theorem repr_mul_hom (a b : _root_.Int) :
      repr (a * b) = UInt64.mul (repr a) (repr b) := by
    unfold repr
    apply UInt64.toNat.inj
    show (UInt64.ofInt (a * b)).toNat = (UInt64.ofInt a * UInt64.ofInt b).toNat
    have h1 : (UInt64.ofInt (a * b)).toNat = ((a * b) % (2^64 : _root_.Int)).toNat := by
      have hbound : ((a * b) % (2^64 : _root_.Int)).toNat < 2^64 := by
        have hlt : ((a * b) % (2^64 : _root_.Int)) < (2^64 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt64.ofInt (a * b)).toBitVec.toNat = _
      have : (UInt64.ofInt (a * b)).toBitVec = BitVec.ofNat 64 (((a * b) % 2^64).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h2 : (UInt64.ofInt a).toNat = (a % (2^64 : _root_.Int)).toNat := by
      have hbound : (a % (2^64 : _root_.Int)).toNat < 2^64 := by
        have hlt : (a % (2^64 : _root_.Int)) < (2^64 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt64.ofInt a).toBitVec.toNat = _
      have : (UInt64.ofInt a).toBitVec = BitVec.ofNat 64 ((a % 2^64).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have h3 : (UInt64.ofInt b).toNat = (b % (2^64 : _root_.Int)).toNat := by
      have hbound : (b % (2^64 : _root_.Int)).toNat < 2^64 := by
        have hlt : (b % (2^64 : _root_.Int)) < (2^64 : _root_.Int) := Int.emod_lt_of_pos _ (by omega)
        omega
      show (UInt64.ofInt b).toBitVec.toNat = _
      have : (UInt64.ofInt b).toBitVec = BitVec.ofNat 64 ((b % 2^64).toNat) := rfl
      rw [this, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    rw [h1, UInt64.toNat_mul, h2, h3]
    -- Goal: ((a * b) % 2^64).toNat = ((a % 2^64).toNat * (b % 2^64).toNat) % 2^64
    have ha : 0 ≤ a % (2^64 : _root_.Int) := Int.emod_nonneg _ (by omega)
    have hb : 0 ≤ b % (2^64 : _root_.Int) := Int.emod_nonneg _ (by omega)
    -- Key: (a * b) % 2^64 = (a%2^64) * (b%2^64) % 2^64
    have h_mod_mul : ((a * b) % (2^64 : _root_.Int)) = ((a % (2^64 : _root_.Int)) * (b % (2^64 : _root_.Int))) % (2^64 : _root_.Int) := by
      rw [Int.mul_emod]
    rw [h_mod_mul]
    -- Now show ((...) % 2^64).toNat = ((a%2^64).toNat * (b%2^64).toNat) % 2^64
    show ((a % (2^64 : _root_.Int)) * (b % (2^64 : _root_.Int)) % (2^64 : _root_.Int)).toNat
          = ((a % (2^64 : _root_.Int)).toNat * (b % (2^64 : _root_.Int)).toNat) % 2^64
    -- Use Int.toNat_mul for the product
    have h_prod : ((a % (2^64 : _root_.Int)) * (b % (2^64 : _root_.Int))).toNat
                    = (a % (2^64 : _root_.Int)).toNat * (b % (2^64 : _root_.Int)).toNat := by
      exact Int.toNat_mul (by omega : 0 ≤ a % (2^64 : _root_.Int)) (by omega : 0 ≤ b % (2^64 : _root_.Int))
    -- Use Int.toNat_emod for the mod
    have : ((a % (2^64 : _root_.Int)) * (b % (2^64 : _root_.Int)) % (2^64 : _root_.Int)).toNat
            = ((a % (2^64 : _root_.Int)) * (b % (2^64 : _root_.Int))).toNat % 2^64 := by
      have hx : 0 ≤ (a % (2^64 : _root_.Int)) * (b % (2^64 : _root_.Int)) := Int.mul_nonneg ha hb
      have hy : 0 ≤ (2^64 : _root_.Int) := by decide
      exact Int.toNat_emod hx hy
    rw [this, h_prod]
  theorem divs_one (x : CompCert.Int64) : divs x one = x := by
    unfold divs one
    simp only [repr, signed]
    have h_one_signed : (1 : UInt64).toBitVec.toInt = 1 := by decide
    simp only [h_one_signed, Int.tdiv_one]
    exact repr_signed x

  def mods (x y : CompCert.Int64) : CompCert.Int64 :=
    -- Signed modulo (tmod, matches tdiv)
    repr (Int.tmod x.signed y.signed)

  theorem mods_divs_identity (x y : CompCert.Int64) (_hy : y ≠ zero) :
      mods x y = sub x (mul (divs x y) y) := by
    unfold mods divs sub mul
    have htdiv : Int.tmod x.signed y.signed = x.signed - y.signed * (Int.tdiv x.signed y.signed) := Int.tmod_def _ _
    rw [htdiv]
    rw [repr_sub_hom, repr_mul_hom]
    rw [repr_signed, repr_signed]
    congr 1
    exact UInt64.mul_comm _ _
  def divu (x y : CompCert.Int64) : CompCert.Int64 :=
    repr ((x.unsigned : _root_.Int) / (y.unsigned : _root_.Int))

  theorem repr_unsigned (x : CompCert.Int64) : repr (x.unsigned) = x := by
    unfold repr unsigned
    apply UInt64.toNat.inj
    rw [uint64_ofInt_toNat]
    have h : x.toNat < 2^64 := x.toBitVec.isLt
    have hcast : ((x.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat = x.toNat := by
      have : (x.toNat : _root_.Int) % (2^64 : _root_.Int) = (x.toNat : _root_.Int) := by
        apply Int.emod_eq_of_lt (by omega : (0 : _root_.Int) ≤ ↑(x.toNat)) (by exact_mod_cast h)
      rw [this]; exact Int.toNat_natCast _
    exact hcast

  theorem divu_one (x : CompCert.Int64) : divu x one = x := by
    unfold divu
    have h1 : ((one : CompCert.Int64).unsigned : _root_.Int) = 1 := by decide
    rw [h1, Int.ediv_one, repr_unsigned]

  def modu (x y : CompCert.Int64) : CompCert.Int64 :=
    repr ((x.unsigned : _root_.Int) % (y.unsigned : _root_.Int))

  theorem modu_divu_identity (x y : CompCert.Int64) (_hy : y ≠ zero) :
      modu x y = sub x (mul (divu x y) y) := by
    unfold modu divu sub mul
    have heuc : (x.unsigned : _root_.Int) % (y.unsigned : _root_.Int)
                = (x.unsigned : _root_.Int) - (y.unsigned : _root_.Int) * ((x.unsigned : _root_.Int) / (y.unsigned : _root_.Int)) :=
      Int.emod_def _ _
    rw [heuc]
    rw [repr_sub_hom, repr_mul_hom]
    rw [repr_unsigned, repr_unsigned]
    congr 1
    exact UInt64.mul_comm _ _
  def add_carry (x y cin : CompCert.Int64) : CompCert.Int64 :=
    let sum := (x.unsigned : _root_.Int) + (y.unsigned : _root_.Int) + (cin.unsigned : _root_.Int)
    repr sum

  def sub_overflow (x y z : CompCert.Int64) : CompCert.Int64 :=
    let res := x.signed - y.signed - z.signed
    if res < min_signed || res > max_signed then one else zero

  def negative (x : CompCert.Int64) : CompCert.Int64 :=
    if x.signed < 0 then one else zero

  -- Comparison operations
  def eq (x y : CompCert.Int64) : Bool := x == y
  def lt (x y : CompCert.Int64) : Bool := x.signed < y.signed  -- signed less than
  def ltu (x y : CompCert.Int64) : Bool := x < y  -- unsigned less than

  def cmp (c : comparison) (x y : CompCert.Int64) : Bool :=
    match c with
    | .Ceq => x.signed == y.signed
    | .Cne => x.signed != y.signed
    | .Clt => x.signed < y.signed
    | .Cle => x.signed <= y.signed
    | .Cgt => x.signed > y.signed
    | .Cge => x.signed >= y.signed

  theorem cmp_swap (c : comparison) (x y : CompCert.Int64) :
      cmp (swap_comparison c) x y = cmp c y x := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmp, swap_comparison]
    -- Ceq
    · cases h : (x.signed == y.signed) <;> cases h' : (y.signed == x.signed) <;> simp_all
    -- Cne
    · cases h : (x.signed != y.signed) <;> cases h' : (y.signed != x.signed) <;> simp_all

  theorem cmp_negate (c : comparison) (x y : CompCert.Int64) :
      cmp (negate_comparison c) x y = !(cmp c x y) := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmp, negate_comparison]
    all_goals (try rfl)
    -- Ceq
    · cases h : (x.signed == y.signed) <;> cases h' : (x.signed != y.signed) <;> simp_all
    -- Clt
    · cases h : decide (x.signed < y.signed) <;> cases h' : decide (x.signed ≥ y.signed) <;> simp_all [decide_eq_true_eq]; omega
    -- Cle
    · cases h : decide (x.signed ≤ y.signed) <;> cases h' : decide (x.signed > y.signed) <;> simp_all [decide_eq_true_eq]; omega
    -- Cgt
    · cases h : decide (x.signed > y.signed) <;> cases h' : decide (x.signed ≤ y.signed) <;> simp_all [decide_eq_true_eq]; omega
    -- Cge
    · cases h : decide (x.signed ≥ y.signed) <;> cases h' : decide (x.signed < y.signed) <;> simp_all [decide_eq_true_eq]; omega

  def cmpu (c : comparison) (x y : CompCert.Int64) : Bool :=
    match c with
    | .Ceq => x.unsigned == y.unsigned
    | .Cne => x.unsigned != y.unsigned
    | .Clt => x.unsigned < y.unsigned
    | .Cle => x.unsigned <= y.unsigned
    | .Cgt => x.unsigned > y.unsigned
    | .Cge => x.unsigned >= y.unsigned

  theorem cmpu_swap (c : comparison) (x y : CompCert.Int64) :
      cmpu (swap_comparison c) x y = cmpu c y x := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmpu, swap_comparison]
    -- Ceq
    · cases h : (x.unsigned == y.unsigned) <;> cases h' : (y.unsigned == x.unsigned) <;> simp_all
    -- Cne
    · cases h : (x.unsigned != y.unsigned) <;> cases h' : (y.unsigned != x.unsigned) <;> simp_all

  theorem cmpu_negate (c : comparison) (x y : CompCert.Int64) :
      cmpu (negate_comparison c) x y = !(cmpu c x y) := by
    rcases c with _ | _ | _ | _ | _ | _
    all_goals simp only [cmpu, negate_comparison]
    all_goals (try rfl)
    -- Ceq
    · cases h : (x.unsigned == y.unsigned) <;> cases h' : (x.unsigned != y.unsigned) <;> simp_all
    -- Clt
    · cases h : decide (x.unsigned < y.unsigned) <;> cases h' : decide (x.unsigned ≥ y.unsigned) <;> simp_all [decide_eq_true_eq]; omega
    -- Cle
    · cases h : decide (x.unsigned ≤ y.unsigned) <;> cases h' : decide (x.unsigned > y.unsigned) <;> simp_all [decide_eq_true_eq]; omega
    -- Cgt
    · cases h : decide (x.unsigned > y.unsigned) <;> cases h' : decide (x.unsigned ≤ y.unsigned) <;> simp_all [decide_eq_true_eq]; omega
    -- Cge
    · cases h : decide (x.unsigned ≥ y.unsigned) <;> cases h' : decide (x.unsigned < y.unsigned) <;> simp_all [decide_eq_true_eq]; omega

  -- Bitwise operations
  def and := UInt64.land
  def or := UInt64.lor
  def xor := UInt64.xor
  def not (x : CompCert.Int64) : CompCert.Int64 := xor x mone

  -- Shift operations
  def shl := UInt64.shiftLeft
  def shru := UInt64.shiftRight

  def shr (x y : CompCert.Int64) : CompCert.Int64 :=
    -- Arithmetic shift right (sign-extending), shift amount is a 64-bit int
    let shamt := y.toNat % 64
    repr (x.signed >>> shamt)

  def shl' (x : CompCert.Int64) (y : CompCert.Int) : CompCert.Int64 :=
    -- Shift left, shift amount is 32-bit int
    shl x (y.toNat.toUInt64)

  def shr' (x : CompCert.Int64) (y : CompCert.Int) : CompCert.Int64 :=
    -- Arithmetic shift right
    let shamt := y.toNat % 64
    repr (x.signed >>> shamt)

  def shru' (x : CompCert.Int64) (y : CompCert.Int) : CompCert.Int64 :=
    -- Logical shift right
    shru x (y.toNat.toUInt64)

  def shrx' (x : CompCert.Int64) (y : CompCert.Int) : CompCert.Int64 :=
    -- Signed division by 2^y
    let shamt := y.toNat
    if x.signed >= 0 then
      repr (x.signed >>> shamt)
    else
      let round := (1 <<< shamt) - 1
      repr ((x.signed + round) >>> shamt)

  def shr_carry' (x : CompCert.Int64) (y : CompCert.Int) : CompCert.Int64 :=
    -- Carry bit for rounding: 1 iff x < 0 and some low bits are shifted out.
    if x.signed < 0 && (x.unsigned &&& ((1 <<< (y.toNat % 64)) - 1)) != 0 then one else zero

  -- Rotate operations
  def rol (x y : CompCert.Int64) : CompCert.Int64 :=
    let n := y.toNat % 64
    let bv := x.toBitVec
    UInt64.ofInt (bv.rotateLeft n |>.toInt)

  def ror (x y : CompCert.Int64) : CompCert.Int64 :=
    let n := y.toNat % 64
    let bv := x.toBitVec
    UInt64.ofInt (bv.rotateRight n |>.toInt)

  def rolm (x amount mask : CompCert.Int64) : CompCert.Int64 :=
    and (rol x amount) mask

/-
  Base type here are Nat, Int, and BitVec

-/

#print BitVec.zeroExtend

  theorem UInt64.ofInt_toBitVec_toInt (x : UInt64) :
    UInt64.ofInt x.toBitVec.toInt = x := by
    obtain ⟨⟨n, hn⟩⟩ := x
    simp only [UInt64.ofInt, BitVec.toInt, BitVec.toNat, UInt64.ofNat, BitVec.ofNat]
    split <;> · congr; apply Fin.ext; simp only [Fin.Internal.ofNat]; omega

  -- Helper lemmas for modular arithmetic proofs (Int64 versions)
  private lemma uint64_ofNat_toBitVec_toNat (n : Nat) :
      (UInt64.ofNat n).toBitVec.toNat = n % (2^64) := by
    simp [UInt64.ofNat, BitVec.toNat_ofNat]

  private lemma uint64_toNat_eq_toBitVec_toNat (x : UInt64) :
      UInt64.toNat x = x.toBitVec.toNat := by
    rfl

  private lemma uint64_toBitVec_toNat_add (x y : UInt64) :
      (x + y).toBitVec.toNat = (UInt64.toNat x + UInt64.toNat y) % (2^64) := by
    rfl

  theorem rol_zero (x : CompCert.Int64) : rol x zero = x := by
    unfold rol zero
    simp
    rw [BitVec.rotateLeft_zero]
    apply UInt64.ofInt_toBitVec_toInt

  -- Sign/zero extension operations
  def zero_ext (n : Nat) (x : CompCert.Int64) : CompCert.Int64 :=
    UInt64.ofInt (((x.toBitVec).zeroExtend (n.min 64) |>.toNat : _root_.Int))

  def sign_ext (n : Nat) (x : CompCert.Int64) : CompCert.Int64 :=
    UInt64.ofInt (x.toBitVec.signExtend (n.min 64) |>.toInt)

  -- Word operations
  def ofwords (hi lo : CompCert.Int) : CompCert.Int64 :=
    -- Combine two 32-bit words into 64-bit
    let hi64 := (hi.unsigned : Nat) <<< 32
    let lo64 := lo.unsigned
    repr (hi64 ||| lo64 : _root_.Int)

  def hiword (x : CompCert.Int64) : CompCert.Int :=
    -- Extract high 32 bits
    CompCert.Int.repr ((x.unsigned >>> 32 : Nat) : _root_.Int)

  def loword (x : CompCert.Int64) : CompCert.Int :=
    -- Extract low 32 bits
    CompCert.Int.repr ((x.unsigned &&& 4294967295 : Nat) : _root_.Int)

  -- Check if x is a power of 2, return the log2 (as Int) if so
  -- Check if x is a power of 2, return the log2 (as Int) if so
  def is_power2' (x : CompCert.Int64) : Option CompCert.Int :=
    if x == 0 then
      none
    else
      -- Check if x is a power of 2 using x & (x - 1) == 0
      let x_minus_1 := x - 1
      let and_result := x.land x_minus_1
      if and_result == 0 then
        -- x is a power of 2, find the bit position (log2)
        some (CompCert.Int.repr (x.toBitVec.toNat.log2 : _root_.Int))
      else
        none

  -- Check if x is a power of 2, return the log2 (as Int64) if so
  def is_power2 (x : CompCert.Int64) : Option CompCert.Int64 :=
    if x == 0 then
      none
    else
      -- Check if x is a power of 2 using x & (x - 1) == 0
      let x_minus_1 := x - 1
      let and_result := x.land x_minus_1
      if and_result == 0 then
        -- x is a power of 2, find the bit position (log2)
        some (repr (x.toBitVec.toNat.log2 : _root_.Int))
      else
        none

  theorem add_commut (x y : CompCert.Int64) : x + y = y + x := by
    ext
    ac_rfl

  theorem add_assoc (x y z : CompCert.Int64) : (x + y) + z = x + (y + z) := by
    ext
    ac_rfl

  theorem mul_commut (x y : CompCert.Int64) : x * y = y * x := by
    ext
    ac_rfl

  theorem mul_assoc (x y z : CompCert.Int64) : (x * y) * z = x * (y * z) := by
    ext
    ac_rfl

  theorem mul_add_distr_l (x y z : CompCert.Int64) : (x + y) * z = x * z + y * z := by
    ext
    congr
    grind

  theorem mul_add_distr_r (x y z : CompCert.Int64) : x * (y + z) = x * y + x * z := by
    ext
    congr
    grind

  theorem and_commut (x y : CompCert.Int64) : and x y = and y x := by
    unfold and
    unfold UInt64.land
    simp
    grind

  theorem and_assoc (x y z : CompCert.Int64) : and (and x y) z = and x (and y z) := by
    unfold and
    unfold UInt64.land
    simp
    grind

  theorem or_commut (x y : CompCert.Int64) : or x y = or y x := by
    unfold or
    unfold UInt64.lor
    simp
    grind

  theorem or_assoc (x y z : CompCert.Int64) : or (or x y) z = or x (or y z) := by
    unfold or
    unfold UInt64.lor
    simp
    grind

  theorem xor_commut (x y : CompCert.Int64) : xor x y = xor y x := by
    unfold xor
    unfold UInt64.xor
    simp
    grind

  theorem xor_assoc (x y z : CompCert.Int64) : xor (xor x y) z = xor x (xor y z) := by
    unfold xor
    unfold UInt64.xor
    simp
    grind

  theorem zero_ext_and (n : Nat) (x : CompCert.Int64) :
      zero_ext n x = and x (repr (two_p n - 1)) := by
    -- Helper lemmas for the proof (same pattern as Int but for UInt64)
    have ofInt_toBitVec_eq_ofInt : ∀ z : _root_.Int, (UInt64.ofInt z).toBitVec = BitVec.ofInt 64 z := by
      intro z
      apply BitVec.eq_of_toNat_eq
      have h1 : (UInt64.ofInt z).toBitVec = BitVec.ofNat 64 ((z % 2^64).toNat) := rfl
      simp only [h1, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    have BitVec_ofInt_natCast : ∀ n m : Nat, BitVec.ofInt n (m : _root_.Int) = BitVec.ofNat n m := by
      intros n m
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat]
    have two_pow_sub_one_nonneg : ∀ n : Nat, (2^n : _root_.Int) - 1 = ((2^n - 1 : Nat) : _root_.Int) := by
      intro n
      have : 1 ≤ 2^n := Nat.one_le_two_pow
      simp [_root_.Int.ofNat_sub this]
    have getLsbD_eq_testBit_toNat : ∀ {w : Nat} (v : BitVec w) (i : Nat),
        v.getLsbD i = v.toNat.testBit i := by intros; rfl

    -- Main proof
    rw [UInt64.eq_iff_toBitVec_eq]
    unfold zero_ext and repr two_p
    have rhs_eq : (UInt64.land x (UInt64.ofInt (2^n - 1))).toBitVec =
                   x.toBitVec &&& (UInt64.ofInt (2^n - 1)).toBitVec := rfl
    rw [rhs_eq]
    simp only [ofInt_toBitVec_eq_ofInt]
    rw [two_pow_sub_one_nonneg, BitVec_ofInt_natCast, BitVec_ofInt_natCast]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
    rw [← getLsbD_eq_testBit_toNat, BitVec.getLsbD_setWidth, Nat.testBit_two_pow_sub_one]
    have hi64 : decide (i < 64) = true := by simp [hi]
    rw [hi64]
    simp only [Bool.true_and]
    rw [Bool.and_comm]
    congr 1
    simp only [Nat.lt_min, decide_eq_decide]
    omega

  theorem neg_add_distr (x y : CompCert.Int64) : neg (x + y) = neg x + neg y := by
    ext
    unfold neg
    -- Same structure as Int32 version, but with 64-bit
    show (UInt64.ofInt (-(↑(x + y).toNat : _root_.Int))).toNat =
         (UInt64.ofInt (-(↑x.toNat : _root_.Int)) + UInt64.ofInt (-(↑y.toNat : _root_.Int))).toNat
    simp only [UInt64.ofInt, UInt64.toNat]
    have h64 : (2 : Nat) ^ 64 > 0 := by omega
    -- Reuse the generic helper lemma from CompCert.Int
    convert CompCert.Int.int_toNat_neg_add_mod x.toNat y.toNat (2^64) h64 using 1
    · -- Goal 1: LHS packaging
      rw [uint64_ofNat_toBitVec_toNat]
      rw [uint64_toBitVec_toNat_add]
      congr 1
      rw [Int.natCast_mod]
      simp only [Int.neg_emod]
      split
      · split <;> omega
      · split
        · omega
        · simp [Int.emod_emod_of_dvd _ (dvd_refl _)]
    · -- Goal 2: RHS packaging
      rw [uint64_toBitVec_toNat_add]
      simp only [UInt64.toNat]
      rw [uint64_ofNat_toBitVec_toNat, uint64_ofNat_toBitVec_toNat]
      rw [← uint64_toNat_eq_toBitVec_toNat x, ← uint64_toNat_eq_toBitVec_toNat y]
      simp

  theorem sub_add_opp (x y : CompCert.Int64) : sub x y = x + neg y := by
    apply UInt64.toNat.inj
    have hy : y.toNat < 2^64 := y.toBitVec.isLt
    -- `sub` is definitionally `UInt64.sub`, and `UInt64.sub x y = x - y`, so restate
    -- the LHS using the `-` operator so that `UInt64.toNat_sub` applies.
    show (x - y).toNat = (x + neg y).toNat
    rw [UInt64.toNat_add, neg_toNat, UInt64.toNat_sub]
    have hkey : (-(y.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat
                  = (2^64 - y.toNat) % 2^64 := by
      have hnn : (0 : _root_.Int) ≤ -(y.toNat : _root_.Int) % (2^64 : _root_.Int) :=
        Int.emod_nonneg _ (by omega)
      have : ((-(y.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat : _root_.Int)
               = (((2^64 - y.toNat) % 2^64 : Nat) : _root_.Int) := by
        rw [Int.toNat_of_nonneg hnn]
        push_cast [Nat.mod_eq_of_lt (a := 2^64 - y.toNat)]
        omega
      exact_mod_cast this
    rw [hkey]
    omega

  theorem neg_involutive (x : CompCert.Int64) : neg (neg x) = x := by
    apply UInt64.toNat.inj
    have hx : x.toNat < 2^64 := x.toBitVec.isLt
    rw [neg_toNat, neg_toNat]
    have hnn : (0 : _root_.Int) ≤ -(x.toNat : _root_.Int) % (2^64 : _root_.Int) :=
      Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hnn]
    have hneg : (-(-(x.toNat : _root_.Int) % (2^64 : _root_.Int)) % (2^64 : _root_.Int))
                  = (x.toNat : _root_.Int) := by
      have h1 : (-(-(x.toNat : _root_.Int) % (2^64 : _root_.Int)) % (2^64 : _root_.Int))
                  = (-(-(x.toNat : _root_.Int)) % (2^64 : _root_.Int)) := by
        omega
      rw [h1, neg_neg]
      apply Int.emod_eq_of_lt (by omega)
      exact_mod_cast hx
    rw [hneg]
    exact Int.toNat_natCast _

  theorem sub_add_l (a b i : CompCert.Int64) :
      sub (a + i) b = sub a b + i := by
    rw [sub_add_opp, sub_add_opp]
    ac_rfl

  theorem sub_add_r (a b i : CompCert.Int64) :
      sub a (b + i) = sub a b + neg i := by
    rw [sub_add_opp, sub_add_opp, neg_add_distr]
    ac_rfl

  /-- The signed interpretation is congruent to the unsigned value modulo 2^64. -/
  theorem signed_mod_eq_toNat_mod (i : CompCert.Int64) :
      i.signed % (2^64 : _root_.Int) = (i.toNat : _root_.Int) % (2^64 : _root_.Int) := by
    unfold signed
    rw [show i.toNat = i.toBitVec.toNat from rfl]
    rw [BitVec.toInt_eq_toNat_bmod]
    unfold Int.bmod
    simp only []
    split
    · simp
    · have h_bound : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
      omega

  /-- `(neg x).signed ≡ -(x.signed) (mod 2^64)` — the true congruence. -/
  theorem neg_signed_mod (x : CompCert.Int64) :
      (neg x).signed % (2^64 : _root_.Int) = (-(x.signed)) % (2^64 : _root_.Int) := by
    rw [signed_mod_eq_toNat_mod, neg_toNat]
    have hx : x.toNat < 2^64 := x.toBitVec.isLt
    have hnn : (0 : _root_.Int) ≤ -(x.toNat : _root_.Int) % (2^64 : _root_.Int) :=
      Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hnn]
    have hsig : x.signed % (2^64 : _root_.Int) = (x.toNat : _root_.Int) % (2^64 : _root_.Int) :=
      signed_mod_eq_toNat_mod x
    omega

  -- Addition is congruent modulo 2^64 on the signed interpretation.
  theorem add_signed_mod (i j : CompCert.Int64) :
      CompCert.Int64.signed (add i j) % (2^64 : _root_.Int)
        = (i.signed + j.signed) % (2^64 : _root_.Int) := by
    rw [signed_mod_eq_toNat_mod]
    have hij : (add i j).toNat = (i.toNat + j.toNat) % (2^64) := by
      change (i + j).toNat = _
      rw [uint64_toNat_eq_toBitVec_toNat, uint64_toBitVec_toNat_add,
          uint64_toNat_eq_toBitVec_toNat, uint64_toNat_eq_toBitVec_toNat]
    rw [hij]
    have hi := signed_mod_eq_toNat_mod i
    have hj := signed_mod_eq_toNat_mod j
    have hi_lt : i.toNat < 2^64 := i.toBitVec.isLt
    have hj_lt : j.toNat < 2^64 := j.toBitVec.isLt
    omega

  theorem repr_add_signed (x : _root_.Int) (i : CompCert.Int64) :
      repr (x + i.signed) = repr x + i := by
    rw [UInt64.eq_iff_toBitVec_eq]
    apply BitVec.eq_of_toNat_eq
    unfold repr signed
    simp only [uint64_ofInt_toBitVec, BitVec.toNat_ofInt]
    have h_add : (UInt64.ofInt x + i).toBitVec.toNat
                  = ((UInt64.ofInt x).toBitVec + i.toBitVec).toNat := rfl
    rw [h_add]
    simp only [BitVec.toNat_add, uint64_ofInt_toBitVec, BitVec.toNat_ofInt]
    have h_i_nat : i.toNat = i.toBitVec.toNat := rfl
    rw [← h_i_nat]
    have h_signed := signed_mod_eq_toNat_mod i
    unfold signed at h_signed
    have h_add_mod : (x + i.toBitVec.toInt) % ↑(2^64 : Nat) = (x + ↑i.toNat) % ↑(2^64 : Nat) := by
      omega
    rw [h_add_mod]
    have h_expand : (x + ↑i.toNat) % ↑(2^64 : Nat)
                      = (x % ↑(2^64 : Nat) + ↑i.toNat) % ↑(2^64 : Nat) := by
      omega
    rw [h_expand]
    have h_i_lt : i.toNat < 2^64 := i.toBitVec.isLt
    omega

  theorem repr_congr {a b : _root_.Int} (h : a % (2^64 : _root_.Int) = b % (2^64 : _root_.Int)) :
      repr a = repr b := by
    apply UInt64.toNat.inj
    show (UInt64.ofInt a).toNat = (UInt64.ofInt b).toNat
    rw [uint64_ofInt_toNat, uint64_ofInt_toNat, h]

  -- Helper lemma for Int64 rotate
  theorem rol_toBitVec (x n : CompCert.Int64) :
      (rol x n).toBitVec = x.toBitVec.rotateLeft (n.toNat % 64) := by
    unfold rol
    -- Similar to Int.rol_toBitVec
    have h1 : ∀ (bv : BitVec 64), (UInt64.ofInt bv.toInt).toBitVec = bv := by
      intro bv
      have h_eq : (UInt64.ofInt bv.toInt).toBitVec = BitVec.ofInt 64 bv.toInt := by
        apply BitVec.eq_of_toNat_eq
        have : (UInt64.ofInt bv.toInt).toBitVec = BitVec.ofNat 64 ((bv.toInt % 2^64).toNat) := rfl
        simp only [this, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
        omega
      rw [h_eq]
      exact BitVec.ofInt_toInt
    exact h1 _

  -- Shift-left equals rolm (64-bit version)
  theorem shl_rolm (x : CompCert.Int64) (n : CompCert.Int)
      (H : CompCert.Int.ltu n iwordsize' = true) :
      shl x (CompCert.Int64.repr (CompCert.Int.unsigned n)) = rolm x (CompCert.Int64.repr (CompCert.Int.unsigned n)) (shl mone (CompCert.Int64.repr (CompCert.Int.unsigned n))) := by
    -- Extract n.toNat < 64 from H
    have hn : n.toNat < 64 := by
      unfold CompCert.Int.ltu iwordsize' at H
      have : n < (64 : UInt32) := by simpa using H
      have : n.toNat < (64 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp this
      simp at this
      exact this
    -- Show that m := repr (unsigned n) has m.toNat = n.toNat
    let m := CompCert.Int64.repr (CompCert.Int.unsigned n)
    have hm : m.toNat = n.toNat := by
      unfold m repr CompCert.Int.unsigned
      have : (UInt64.ofInt (n.toNat : _root_.Int)).toNat = n.toNat % 2^64 := by
        exact uint64_ofInt_toNat (n.toNat : _root_.Int)
      rw [this]
      have : n.toNat < 2^64 := by omega
      exact Nat.mod_eq_of_lt this
    rw [UInt64.eq_iff_toBitVec_eq]
    show (x <<< m).toBitVec = ((rol x m).land (mone <<< m)).toBitVec
    have hshl : ∀ (a k : CompCert.Int64), (a <<< k).toBitVec = a.toBitVec <<< (k.toNat % 64) := by
      intro a k; rfl
    rw [hshl]
    show x.toBitVec <<< (m.toNat % 64) = (rol x m).toBitVec &&& (mone <<< m).toBitVec
    rw [rol_toBitVec, hshl]
    have hmone : mone.toBitVec = BitVec.allOnes 64 := by decide
    rw [hmone]
    rw [hm, Nat.mod_eq_of_lt hn]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 64
    · by_cases hin : i < n.toNat
      · have hmod : (i - n.toNat % 64) % 64 = i - n.toNat := by
          rw [Nat.mod_eq_of_lt hn]; exact Nat.mod_eq_of_lt (by omega)
        simp [hi, hin, Nat.mod_eq_of_lt hn]
      · have hmod : (i - n.toNat % 64) % 64 = i - n.toNat := by
          rw [Nat.mod_eq_of_lt hn]; exact Nat.mod_eq_of_lt (by omega)
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, BitVec.getLsbD_shiftLeft, hi, hin, Nat.mod_eq_of_lt hn,
          decide_true, decide_false, Bool.true_and]
        have hlt : i - n.toNat < 64 := by omega
        simp [hlt]
    · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]
      simp
  theorem shru_rolm (x : CompCert.Int64) (n : CompCert.Int)
      (H : CompCert.Int.ltu n iwordsize' = true) :
      shru x (CompCert.Int64.repr (CompCert.Int.unsigned n)) = rolm x (CompCert.Int64.repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n))) (shru mone (CompCert.Int64.repr (CompCert.Int.unsigned n))) := by
    -- Extract n.toNat < 64 from H
    have hn : n.toNat < 64 := by
      unfold CompCert.Int.ltu iwordsize' at H
      have : n < (64 : UInt32) := by simpa using H
      have : n.toNat < (64 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp this
      simp at this
      exact this
    by_cases hn0 : n.toNat = 0
    · -- Special case: n = 0, so shru x 0 = x and rolm x 64 mone = x
      let m := CompCert.Int64.repr (CompCert.Int.unsigned n)
      have hm : m.toNat = n.toNat := by
        unfold m repr CompCert.Int.unsigned
        have : (UInt64.ofInt (n.toNat : _root_.Int)).toNat = n.toNat % 2^64 := by
          exact uint64_ofInt_toNat (n.toNat : _root_.Int)
        rw [this]
        have : n.toNat < 2^64 := by omega
        exact Nat.mod_eq_of_lt this
      rw [UInt64.eq_iff_toBitVec_eq]
      show (x >>> m).toBitVec = ((rol x (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n)))).land (mone >>> m)).toBitVec
      have hshru : ∀ (a k : CompCert.Int64), (a >>> k).toBitVec = a.toBitVec >>> (k.toNat % 64) := by
        intro a k; rfl
      rw [hshru]
      show x.toBitVec >>> (m.toNat % 64) = (rol x (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n)))).toBitVec &&& (mone >>> m).toBitVec
      have hsub0 : (CompCert.Int.sub iwordsize' n).toNat % 32 = 0 := by
        unfold CompCert.Int.sub iwordsize'
        show ((64 : UInt32) - n).toNat % 32 = 0
        rw [UInt32.toNat_sub]
        have h64 : (64 : UInt32).toNat = 64 := by decide
        rw [h64, hn0]
      have hmsub : (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n))).toNat % 64 = 0 := by
        unfold repr CompCert.Int.unsigned
        have hsub_toNat : (CompCert.Int.sub iwordsize' n).toNat = 64 := by
          unfold CompCert.Int.sub iwordsize'
          show ((64 : UInt32) - n).toNat = 64
          rw [UInt32.toNat_sub]
          have h64 : (64 : UInt32).toNat = 64 := by decide
          rw [h64, hn0]
        have : (UInt64.ofInt ((CompCert.Int.sub iwordsize' n).toNat : _root_.Int)).toNat = (CompCert.Int.sub iwordsize' n).toNat % 2^64 := by
          exact uint64_ofInt_toNat ((CompCert.Int.sub iwordsize' n).toNat : _root_.Int)
        rw [this, hsub_toNat]
        simp
      rw [rol_toBitVec, hshru]
      have hmone : mone.toBitVec = BitVec.allOnes 64 := by decide
      rw [hmone, hm, hn0, hmsub]
      apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < 64
      · simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, hi, Nat.zero_mod, Nat.sub_zero,
          decide_true, Bool.true_and]
        intro _
        simp [hi]
      · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]
        simp
    -- Main case: n.toNat > 0
    let m := CompCert.Int64.repr (CompCert.Int.unsigned n)
    have hm : m.toNat = n.toNat := by
      unfold m repr CompCert.Int.unsigned
      have : (UInt64.ofInt (n.toNat : _root_.Int)).toNat = n.toNat % 2^64 := by
        exact uint64_ofInt_toNat (n.toNat : _root_.Int)
      rw [this]
      have : n.toNat < 2^64 := by omega
      exact Nat.mod_eq_of_lt this
    -- (sub iwordsize' n).toNat = 64 - n.toNat for the 32-bit sub
    have hsub_int : (CompCert.Int.sub iwordsize' n).toNat = 64 - n.toNat := by
      unfold CompCert.Int.sub iwordsize'
      show ((64 : UInt32) - n).toNat = 64 - n.toNat
      rw [UInt32.toNat_sub]
      have h64 : (64 : UInt32).toNat = 64 := by decide
      rw [h64]
      have : (2^32 - n.toNat + 64) = 2^32 + (64 - n.toNat) := by omega
      rw [this, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    -- Then repr of that also has toNat = 64 - n.toNat
    have hsub : (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n))).toNat = 64 - n.toNat := by
      unfold repr CompCert.Int.unsigned
      have : (UInt64.ofInt ((CompCert.Int.sub iwordsize' n).toNat : _root_.Int)).toNat
               = (CompCert.Int.sub iwordsize' n).toNat % 2^64 := by
        exact uint64_ofInt_toNat ((CompCert.Int.sub iwordsize' n).toNat : _root_.Int)
      rw [this, hsub_int]
      have : 64 - n.toNat < 2^64 := by omega
      exact Nat.mod_eq_of_lt this
    rw [UInt64.eq_iff_toBitVec_eq]
    show (x >>> m).toBitVec = ((rol x (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n)))).land (mone >>> m)).toBitVec
    have hshru : ∀ (a k : CompCert.Int64), (a >>> k).toBitVec = a.toBitVec >>> (k.toNat % 64) := by
      intro a k; rfl
    rw [hshru]
    show x.toBitVec >>> (m.toNat % 64) = (rol x (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n)))).toBitVec &&& (mone >>> m).toBitVec
    rw [rol_toBitVec, hshru]
    have hmone : mone.toBitVec = BitVec.allOnes 64 := by decide
    rw [hmone, hsub, hm, Nat.mod_eq_of_lt hn]
    have hsubmod : (64 - n.toNat) % 64 = 64 - n.toNat := by
      apply Nat.mod_eq_of_lt
      have : 0 < n.toNat := Nat.pos_of_ne_zero hn0
      exact Nat.sub_lt (by decide) this
    rw [hsubmod]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 64
    · by_cases hin : i < 64 - n.toNat
      · -- When i < 64 - n.toNat, we have i + n.toNat < 64
        have hip : i + n.toNat < 64 := by omega
        have hmod : (64 - n.toNat) % 64 = 64 - n.toNat := hsubmod
        -- rotateLeft: since i < r % 64, use first branch: 64 - r % 64 + i = n.toNat + i
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, hi, hmod]
        rw [if_pos hin]
        -- Now: x.getLsbD (64 - (64 - n.toNat) + i) && decide (n.toNat + i < 64) = x.getLsbD (n.toNat + i)
        have hidx : 64 - (64 - n.toNat) + i = n.toNat + i := by omega
        rw [hidx]
        have hip' : n.toNat + i < 64 := by omega
        rw [decide_eq_true hip']
        simp
      · -- When i >= 64 - n.toNat, we have i + n.toNat >= 64
        have hip : ¬ (i + n.toNat < 64) := by omega
        have hmod : (64 - n.toNat) % 64 = 64 - n.toNat := hsubmod
        -- rotateLeft: since i >= r % 64, use second branch: i - r % 64 = i - (64 - n.toNat)
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_rotateLeft,
          BitVec.getLsbD_allOnes, hi, hmod]
        rw [if_neg hin]
        have hip' : ¬ (n.toNat + i < 64) := by omega
        rw [decide_eq_false hip']
        simp
        rw [BitVec.getLsbD_of_ge]
        omega
    · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]
      simp

  -- Multiplication by 2^n equals shift left by n (64-bit version)
  theorem mul_pow2_shl (x : CompCert.Int64) (n : CompCert.Int)
      (H : CompCert.Int.ltu n iwordsize' = true) :
      mul x (shl one (CompCert.Int64.repr (CompCert.Int.unsigned n))) = shl x (CompCert.Int64.repr (CompCert.Int.unsigned n)) := by
    have hn : n.toNat < 64 := by
      unfold CompCert.Int.ltu iwordsize' at H
      have : n < (64 : UInt32) := by simpa using H
      have : n.toNat < (64 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp this
      simp at this
      exact this
    let m := CompCert.Int64.repr (CompCert.Int.unsigned n)
    have hm : m.toNat = n.toNat := by
      unfold m repr CompCert.Int.unsigned
      have : (UInt64.ofInt (n.toNat : _root_.Int)).toNat = n.toNat % 2^64 := by
        exact uint64_ofInt_toNat (n.toNat : _root_.Int)
      rw [this]
      have : n.toNat < 2^64 := by omega
      exact Nat.mod_eq_of_lt this
    rw [UInt64.eq_iff_toBitVec_eq]
    unfold mul shl one
    show (x * (1 <<< m)).toBitVec = (x <<< m).toBitVec
    have hmul : ∀ (a b : CompCert.Int64), (a * b).toBitVec = a.toBitVec * b.toBitVec := by
      intro a b; rfl
    have hshl : ∀ (a k : CompCert.Int64), (a <<< k).toBitVec = a.toBitVec <<< (k.toNat % 64) := by
      intro a k; rfl
    rw [hmul, hshl, hshl]
    have hone : (1 : CompCert.Int64).toBitVec = (1 : BitVec 64) := by decide
    rw [hone, hm]
    rw [Nat.mod_eq_of_lt hn]
    -- Goal: x.toBitVec * (1#64 <<< n.toNat) = x.toBitVec <<< n.toNat
    have h_shift_eq_twoPow : (1 : BitVec 64) <<< n.toNat = BitVec.twoPow 64 n.toNat := by
      rfl
    rw [h_shift_eq_twoPow]
    exact BitVec.mul_twoPow_eq_shiftLeft _ _

  -- Helper: toUInt64 equals repr for values < 2^64
  private lemma toUInt64_eq_repr (n : CompCert.Int) :
      n.toNat.toUInt64 = repr (CompCert.Int.unsigned n) := by
    unfold repr CompCert.Int.unsigned
    -- toUInt64 is UInt64.ofNat, so this is UInt64.ofNat n.toNat = UInt64.ofInt (n.toNat : Int)
    have : n.toNat.toUInt64 = UInt64.ofNat n.toNat := by rfl
    rw [this]
    apply UInt64.toNat.inj
    have h1 : (UInt64.ofNat n.toNat).toNat = n.toNat % 2^64 := by
      rfl
    have h2 : (UInt64.ofInt (n.toNat : _root_.Int)).toNat = ((n.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat := by
      exact uint64_ofInt_toNat (n.toNat : _root_.Int)
    rw [h1, h2]
    have : n.toNat < 2^32 := n.toBitVec.isLt
    have h_lt : (n.toNat : _root_.Int) < (2^64 : _root_.Int) := by omega
    have h_mod : (n.toNat : _root_.Int) % (2^64 : _root_.Int) = (n.toNat : _root_.Int) := by
      exact Int.emod_eq_of_lt (by omega) h_lt
    rw [h_mod]
    simp

  -- Wrapper theorems for shl' and shru' (used by Values.lean)
  theorem shl'_rolm (x : CompCert.Int64) (n : CompCert.Int)
      (H : CompCert.Int.ltu n iwordsize' = true) :
      shl' x n = rolm x (repr (CompCert.Int.unsigned n)) (shl mone (repr (CompCert.Int.unsigned n))) := by
    unfold shl'
    rw [toUInt64_eq_repr]
    exact shl_rolm x n H

  theorem shru'_rolm (x : CompCert.Int64) (n : CompCert.Int)
      (H : CompCert.Int.ltu n iwordsize' = true) :
      shru' x n = rolm x (repr (CompCert.Int.unsigned (CompCert.Int.sub iwordsize' n))) (shru mone (repr (CompCert.Int.unsigned n))) := by
    unfold shru'
    rw [toUInt64_eq_repr]
    exact shru_rolm x n H

  -- Int64 power-of-2 lemmas (unsigned)
  theorem is_power2'_pow (n : CompCert.Int64) (logn : CompCert.Int)
      (H : is_power2' n = some logn) :
      n = shl one (repr (CompCert.Int.unsigned logn)) ∧ logn.toNat < 64 := by
    unfold is_power2' at H
    simp only [beq_iff_eq] at H
    split at H
    · contradiction
    · rename_i hn
      split at H
      · rename_i hland
        have hn_ne : n ≠ 0 := hn
        have hlogn : logn = CompCert.Int.repr (n.toBitVec.toNat.log2 : _root_.Int) := by
          injection H with h; exact h.symm
        have n_toNat_ne : n.toNat ≠ 0 := by
          intro h; apply hn_ne; apply UInt64.toNat.inj; simp only [h]; rfl
        have hland_toNat : n.toNat &&& (n.toNat - 1) = 0 := by
          have h1 : (n.land (n - 1)).toNat = 0 := by
            have : n.land (n - 1) = 0 := hland
            conv_lhs => rw [this]
            rfl
          have h2 : (n.land (n - 1)).toNat = n.toNat &&& (n - 1).toNat := by
            show (n.land (n - 1)).toBitVec.toNat = n.toNat &&& (n - 1).toNat
            have : (n.land (n - 1)).toBitVec = n.toBitVec &&& (n - 1).toBitVec := by rfl
            rw [this]; exact BitVec.toNat_and _ _
          have h3 : (n - 1).toNat = n.toNat - 1 := by
            rw [UInt64.toNat_sub]
            have h_bound : n.toNat < 2^64 := n.toBitVec.isLt
            have hn_pos : n.toNat ≥ 1 := by omega
            have : (2^64 - 1 + n.toNat) % 2^64 = n.toNat - 1 := by omega
            exact this
          rw [h2, h3] at h1; exact h1
        obtain ⟨k, hk⟩ := CompCert.Int.nat_pow2_of_land_pred_eq_zero n_toNat_ne hland_toNat
        have hk_log2 : k = n.toNat.log2 := by
          have : (2^k).log2 = k := Nat.log2_two_pow
          rw [← hk] at this; exact this.symm
        have n_toNat_eq : n.toNat = n.toBitVec.toNat := by rfl
        have hlog2_lt : n.toNat.log2 < 64 := by
          have h1 : n.toNat < 2^64 := n.toBitVec.isLt
          rw [Nat.log2_lt n_toNat_ne]; exact h1
        -- logn.toNat = n.toNat.log2  (32-bit repr of a value < 64)
        have hlogn_toNat : logn.toNat = n.toNat.log2 := by
          rw [hlogn]
          show (CompCert.Int.repr (n.toBitVec.toNat.log2 : _root_.Int)).toNat = n.toNat.log2
          unfold CompCert.Int.repr
          rw [← n_toNat_eq]
          rw [CompCert.Int.uint32_ofInt_toNat]
          rw [Int.emod_eq_of_lt (by omega) (by omega)]
          rw [Int.toNat_natCast]
        refine ⟨?_, by rw [hlogn_toNat]; exact hlog2_lt⟩
        -- n = shl one (repr (unsigned logn))
        apply UInt64.toNat.inj
        unfold shl repr CompCert.Int.unsigned
        rw [hlogn_toNat]
        have h_shl_eq : (UInt64.shiftLeft one (UInt64.ofInt (n.toNat.log2 : _root_.Int))).toNat
                        = 2^n.toNat.log2 := by
          have : (UInt64.shiftLeft one (UInt64.ofInt (n.toNat.log2 : _root_.Int))).toNat =
                 (one <<< (UInt64.ofInt (n.toNat.log2 : _root_.Int))).toNat := by rfl
          rw [this, UInt64.toNat_shiftLeft]
          have h_one : (one : CompCert.Int64).toNat = 1 := by rfl
          have h_repr_toNat : (UInt64.ofInt (n.toNat.log2 : _root_.Int)).toNat = n.toNat.log2 := by
            rw [uint64_ofInt_toNat, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
          rw [h_one, h_repr_toNat, Nat.mod_eq_of_lt hlog2_lt, Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlog2_lt)
        rw [h_shl_eq, ← hk_log2]
        exact hk
      · contradiction

  theorem is_power2_pow' (n logn : CompCert.Int64)
      (H : is_power2 n = some logn) :
      n = shl one logn ∧ logn.toNat < 64 := by
    unfold is_power2 at H
    simp only [beq_iff_eq] at H
    split at H
    · contradiction
    · rename_i hn
      split at H
      · rename_i hland
        have hn_ne : n ≠ 0 := hn
        have hlogn : logn = repr (n.toBitVec.toNat.log2 : _root_.Int) := by
          injection H with h; exact h.symm
        have n_toNat_ne : n.toNat ≠ 0 := by
          intro h; apply hn_ne; apply UInt64.toNat.inj; simp only [h]; rfl
        have hland_toNat : n.toNat &&& (n.toNat - 1) = 0 := by
          have h1 : (n.land (n - 1)).toNat = 0 := by
            have : n.land (n - 1) = 0 := hland
            conv_lhs => rw [this]
            rfl
          have h2 : (n.land (n - 1)).toNat = n.toNat &&& (n - 1).toNat := by
            show (n.land (n - 1)).toBitVec.toNat = n.toNat &&& (n - 1).toNat
            have : (n.land (n - 1)).toBitVec = n.toBitVec &&& (n - 1).toBitVec := by rfl
            rw [this]; exact BitVec.toNat_and _ _
          have h3 : (n - 1).toNat = n.toNat - 1 := by
            rw [UInt64.toNat_sub]
            have h_bound : n.toNat < 2^64 := n.toBitVec.isLt
            have hn_pos : n.toNat ≥ 1 := by omega
            have : (2^64 - 1 + n.toNat) % 2^64 = n.toNat - 1 := by omega
            exact this
          rw [h2, h3] at h1; exact h1
        obtain ⟨k, hk⟩ := CompCert.Int.nat_pow2_of_land_pred_eq_zero n_toNat_ne hland_toNat
        have hk_log2 : k = n.toNat.log2 := by
          have : (2^k).log2 = k := Nat.log2_two_pow
          rw [← hk] at this; exact this.symm
        have n_toNat_eq : n.toNat = n.toBitVec.toNat := by rfl
        have hlog2_lt : n.toNat.log2 < 64 := by
          have h1 : n.toNat < 2^64 := n.toBitVec.isLt
          rw [Nat.log2_lt n_toNat_ne]; exact h1
        constructor
        · apply UInt64.toNat.inj
          rw [hlogn]
          unfold shl repr
          conv_rhs => rw [← n_toNat_eq]
          have h_repr_toNat : (UInt64.ofInt (n.toNat.log2 : _root_.Int)).toNat = n.toNat.log2 := by
            have h_int_mod : ((n.toNat.log2 : _root_.Int) % (2^64 : _root_.Int)).toNat = n.toNat.log2 := by
              rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast _
            show (UInt64.ofInt (n.toNat.log2 : _root_.Int)).toBitVec.toNat = n.toNat.log2
            have : (UInt64.ofInt (n.toNat.log2 : _root_.Int)).toBitVec.toNat =
                   (BitVec.ofNat 64 ((n.toNat.log2 : _root_.Int) % (2^64 : _root_.Int)).toNat).toNat := by rfl
            rw [this, BitVec.toNat_ofNat, h_int_mod]
            exact Nat.mod_eq_of_lt (by omega)
          have h_shl_eq : (UInt64.shiftLeft one (UInt64.ofInt (n.toNat.log2 : _root_.Int))).toNat
                          = 2^n.toNat.log2 := by
            have : (UInt64.shiftLeft one (UInt64.ofInt (n.toNat.log2 : _root_.Int))).toNat =
                   (one <<< (UInt64.ofInt (n.toNat.log2 : _root_.Int))).toNat := by rfl
            rw [this, UInt64.toNat_shiftLeft]
            have h_one : (one : CompCert.Int64).toNat = 1 := by rfl
            rw [h_one, h_repr_toNat, Nat.mod_eq_of_lt hlog2_lt, Nat.shiftLeft_eq, Nat.one_mul]
            exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlog2_lt)
          rw [h_shl_eq, ← hk_log2, hk]
        · rw [hlogn]
          unfold repr
          have h_int_mod : ((n.toNat.log2 : _root_.Int) % (2^64 : _root_.Int)).toNat = n.toNat.log2 := by
            rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact Int.toNat_natCast _
          show (UInt64.ofInt (n.toBitVec.toNat.log2 : _root_.Int)).toBitVec.toNat < 64
          rw [← n_toNat_eq]
          have : (UInt64.ofInt (n.toNat.log2 : _root_.Int)).toBitVec.toNat =
                 (BitVec.ofNat 64 ((n.toNat.log2 : _root_.Int) % (2^64 : _root_.Int)).toNat).toNat := by rfl
          rw [this, BitVec.toNat_ofNat, h_int_mod, Nat.mod_eq_of_lt (by omega)]
          exact hlog2_lt
      · contradiction

  theorem is_power2'_toNat_pow (n : CompCert.Int64) (logn : CompCert.Int)
      (H : is_power2' n = some logn) :
      n.toNat = 2 ^ logn.toNat := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2'_pow n logn H
    calc n.toNat
      _ = (shl one (repr (CompCert.Int.unsigned logn))).toNat := by rw [← hn_eq]
      _ = ((1:UInt64) <<< (UInt64.ofInt (logn.toNat : _root_.Int))).toNat := by
        unfold shl one repr CompCert.Int.unsigned
        rfl
      _ = (1:UInt64).toNat <<< ((UInt64.ofInt (logn.toNat : _root_.Int)).toNat % 64) % 2^64 := by
        exact UInt64.toNat_shiftLeft 1 (UInt64.ofInt (logn.toNat : _root_.Int))
      _ = 1 <<< logn.toNat % 2^64 := by
        rw [show (1:UInt64).toNat = 1 from rfl]
        have h_repr : (UInt64.ofInt (logn.toNat : _root_.Int)).toNat = logn.toNat := by
          have h_int_mod : ((logn.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat = logn.toNat := by
            have h_pos : (0 : _root_.Int) ≤ (logn.toNat : _root_.Int) := by omega
            have h_lt : (logn.toNat : _root_.Int) < (2^64 : _root_.Int) := by omega
            rw [Int.emod_eq_of_lt h_pos h_lt]
            exact Int.toNat_natCast _
          show (UInt64.ofInt (logn.toNat : _root_.Int)).toBitVec.toNat = logn.toNat
          have : (UInt64.ofInt (logn.toNat : _root_.Int)).toBitVec.toNat =
                 (BitVec.ofNat 64 ((logn.toNat : _root_.Int) % (2^64 : _root_.Int)).toNat).toNat := by rfl
          rw [this, BitVec.toNat_ofNat]
          have h_nat_mod : logn.toNat % 2^64 = logn.toNat := by
            exact Nat.mod_eq_of_lt (by omega : logn.toNat < 2^64)
          rw [h_int_mod, h_nat_mod]
        rw [h_repr, Nat.mod_eq_of_lt hlogn_lt]
      _ = 2 ^ logn.toNat % 2^64 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
      _ = 2 ^ logn.toNat := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlogn_lt)

  theorem is_power2_toNat_pow' (n logn : CompCert.Int64) (H : is_power2 n = some logn) :
      n.toNat = 2 ^ logn.toNat := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2_pow' n logn H
    calc n.toNat
      _ = (shl one logn).toNat := by rw [← hn_eq]
      _ = ((1:UInt64) <<< logn).toNat := by rfl
      _ = (1:UInt64).toNat <<< (logn.toNat % 64) % 2^64 := by exact UInt64.toNat_shiftLeft 1 logn
      _ = 1 <<< logn.toNat % 2^64 := by rw [show (1:UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlogn_lt]
      _ = 2 ^ logn.toNat % 2^64 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
      _ = 2 ^ logn.toNat := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlogn_lt)

  theorem divu_pow2 (x n : CompCert.Int64) (logn : CompCert.Int)
      (H : is_power2' n = some logn) :
      divu x n = shru' x logn := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2'_pow n logn H
    have hn_toNat : n.toNat = 2 ^ logn.toNat := is_power2'_toNat_pow n logn H
    have hn_pos : 0 < n.toNat := by rw [hn_toNat]; exact Nat.two_pow_pos _
    apply UInt64.toNat.inj
    unfold divu shru'
    -- LHS: (repr (x.toNat / n.toNat)).toNat = x.toNat / n.toNat
    have h_divu : (repr ((x.unsigned : _root_.Int) / (n.unsigned : _root_.Int))).toNat
                  = x.toNat / n.toNat := by
      unfold repr unsigned
      rw [uint64_ofInt_toNat]
      have hnn : (0 : _root_.Int) ≤ (x.toNat : _root_.Int) / (n.toNat : _root_.Int) :=
        Int.ediv_nonneg (by omega : (0:_root_.Int) ≤ x.toNat) (by omega : (0:_root_.Int) ≤ n.toNat)
      have hbd : (x.toNat : _root_.Int) / (n.toNat : _root_.Int) < 2 ^ 64 := by
        have hx : x.toNat < 2 ^ 64 := x.toBitVec.isLt
        have h1 : (x.toNat : _root_.Int) / (n.toNat : _root_.Int) ≤ (x.toNat : _root_.Int) :=
          Int.ediv_le_self _ (by omega : (0:_root_.Int) ≤ x.toNat)
        have h2 : (x.toNat : _root_.Int) < (2 ^ 64 : _root_.Int) := by omega
        omega
      rw [Int.emod_eq_of_lt hnn hbd]
      rw [show ((x.toNat : _root_.Int) / (n.toNat : _root_.Int))
            = ((x.toNat / n.toNat : Nat) : _root_.Int) from by
        exact (Int.natCast_div _ _).symm]
      exact Int.toNat_natCast _
    rw [h_divu]
    -- RHS: shru' x logn = shru x (logn.toNat.toUInt64)
    unfold shru
    -- Goal: x.toNat / n.toNat = (x >>> logn.toNat.toUInt64).toNat
    have h_shru : (x >>> logn.toNat.toUInt64).toBitVec.toNat = x.toNat >>> logn.toNat := by
      change (x >>> logn.toNat.toUInt64).toNat = x.toNat >>> logn.toNat
      have : (x >>> logn.toNat.toUInt64).toNat = x.toNat >>> (logn.toNat.toUInt64.toNat % 64) :=
        UInt64.toNat_shiftRight x logn.toNat.toUInt64
      rw [this]
      have h_toNat : logn.toNat.toUInt64.toNat = logn.toNat % 2^64 := by
        show (UInt64.ofNat logn.toNat).toNat = logn.toNat % 2^64
        change (UInt64.ofNat logn.toNat).toBitVec.toNat = logn.toNat % 2^64
        have : (UInt64.ofNat logn.toNat).toBitVec.toNat = (BitVec.ofNat 64 logn.toNat).toNat := by rfl
        rw [this, BitVec.toNat_ofNat]
      rw [h_toNat]
      have : logn.toNat % 2^64 = logn.toNat := Nat.mod_eq_of_lt (by omega : logn.toNat < 2^64)
      rw [this, Nat.mod_eq_of_lt hlogn_lt]
    show x.toNat / n.toNat = (x >>> logn.toNat.toUInt64).toBitVec.toNat
    rw [h_shru, Nat.shiftRight_eq_div_pow, hn_toNat]

  theorem modu_pow2 (x n logn : CompCert.Int64)
      (H : is_power2 n = some logn) :
      modu x n = and x (sub n one) := by
    have ⟨hn_eq, hlogn_lt⟩ := is_power2_pow' n logn H
    have hn_toNat : n.toNat = 2 ^ logn.toNat := is_power2_toNat_pow' n logn H
    have hn_pos : 0 < n.toNat := by rw [hn_toNat]; exact Nat.two_pow_pos _
    apply UInt64.toNat.inj
    unfold modu and sub one
    -- LHS: (repr (x.toNat % n.toNat)).toNat = x.toNat % n.toNat
    have h_modu : (repr ((x.toNat : _root_.Int) % (n.toNat : _root_.Int))).toNat =
                  x.toNat % n.toNat := by
      unfold repr
      have h_mod_pos : (x.toNat : _root_.Int) % (n.toNat : _root_.Int) ≥ 0 := by
        apply Int.emod_nonneg
        omega
      have h_mod_bound : (x.toNat : _root_.Int) % (n.toNat : _root_.Int) < 2^64 := by
        have : (x.toNat : _root_.Int) % (n.toNat : _root_.Int) < n.toNat := by
          apply Int.emod_lt_of_pos
          omega
        have : n.toNat < 2^64 := n.toBitVec.isLt
        omega
      have : ((x.toNat : _root_.Int) % (n.toNat : _root_.Int)) % (2^64 : _root_.Int) =
             (x.toNat : _root_.Int) % (n.toNat : _root_.Int) := by
        apply Int.emod_eq_of_lt h_mod_pos h_mod_bound
      show (UInt64.ofInt ((x.toNat : _root_.Int) % (n.toNat : _root_.Int))).toBitVec.toNat = x.toNat % n.toNat
      unfold UInt64.ofInt
      rw [this]
      -- Goal: (UInt64.ofNat ((x.toNat : Int) % (n.toNat : Int)).toNat).toBitVec.toNat = x.toNat % n.toNat
      change (BitVec.ofNat 64 ((x.toNat : _root_.Int) % (n.toNat : _root_.Int)).toNat).toNat = x.toNat % n.toNat
      rw [BitVec.toNat_ofNat]
      -- Goal: ((x.toNat : Int) % (n.toNat : Int)).toNat % 2^64 = x.toNat % n.toNat
      have h_toNat : ((x.toNat : _root_.Int) % (n.toNat : _root_.Int)).toNat = x.toNat % n.toNat :=
        (Int.toNat_emod (by omega : (0:_root_.Int) ≤ x.toNat) (by omega : (0:_root_.Int) ≤ n.toNat)).symm
      rw [h_toNat]
      exact Nat.mod_eq_of_lt (by have : x.toNat % n.toNat < n.toNat := Nat.mod_lt _ hn_pos; omega)
    -- After applying UInt64.toNat.inj, goal is: (modu x n).toNat = (and x (sub n one)).toNat
    show (modu x n).toNat = (and x (sub n one)).toNat
    -- Simplify LHS using h_modu
    unfold modu unsigned at *
    calc (repr ((x.toNat : _root_.Int) % (n.toNat : _root_.Int))).toNat
      _ = x.toNat % n.toNat := h_modu
      _ = x.toNat &&& (2^logn.toNat - 1) := by
        rw [hn_toNat]
        exact (Nat.and_two_pow_sub_one_eq_mod x.toNat logn.toNat).symm
      _ = x.toNat &&& (n - 1).toNat := by
        have hn_sub_one : (n - 1).toNat = 2^logn.toNat - 1 := by
          calc (n - 1).toNat
            _ = (2^64 - 1 + n.toNat) % 2^64 := UInt64.toNat_sub n 1
            _ = (2^64 - 1 + 2^logn.toNat) % 2^64 := by rw [hn_toNat]
            _ = 2^logn.toNat - 1 := by
              have h_pow_bound : 2^logn.toNat < 2^64 := Nat.pow_lt_pow_right (by omega : 1 < 2) hlogn_lt
              have h_pow_pos : 1 ≤ 2^logn.toNat := by
                have : 0 < 2^logn.toNat := Nat.two_pow_pos _
                omega
              have h_add_rearr : 2^64 - 1 + 2^logn.toNat = 2^64 + (2^logn.toNat - 1) := by omega
              rw [h_add_rearr]
              have h_mod_lt : 2^logn.toNat - 1 < 2^64 := by omega
              calc (2^64 + (2^logn.toNat - 1)) % 2^64
                _ = ((2^64 % 2^64) + (2^logn.toNat - 1) % 2^64) % 2^64 := Nat.add_mod _ _ _
                _ = (0 + (2^logn.toNat - 1)) % 2^64 := by simp
                _ = (2^logn.toNat - 1) % 2^64 := by simp
                _ = 2^logn.toNat - 1 := Nat.mod_eq_of_lt h_mod_lt
        rw [hn_sub_one]
      _ = (and x (sub n one)).toNat := by
        unfold and sub one
        calc x.toNat &&& (n - 1).toNat
          _ = x.toBitVec.toNat &&& (n - 1).toBitVec.toNat := by rfl
          _ = (x.toBitVec &&& (n - 1).toBitVec).toNat := (BitVec.toNat_and _ _).symm
          _ = (x &&& (n - 1)).toBitVec.toNat := by rfl
          _ = (x &&& (n - 1)).toNat := by rfl

  -- Helper: add x zero = x
  @[simp] theorem add_zero (x : CompCert.Int64) : add x zero = x := by
    unfold add zero
    exact UInt64.add_zero x

  -- Bridge: the masked low bits of x (as Nat) are nonzero iff x.signed is not divisible by 2^k,
  -- for k < 63 (so 2^k ∣ 2^64).
  private theorem shrx_low_bits_ne_iff (x : CompCert.Int64) (k : Nat) (hk : k < 63) :
      (x.unsigned &&& ((1 <<< k) - 1) ≠ 0) ↔ x.signed % (2 ^ k : _root_.Int) ≠ 0 := by
    have hmask : (1 : Nat) <<< k - 1 = 2 ^ k - 1 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hmask]
    -- Nat and-mask = mod
    have hand : x.unsigned &&& (2 ^ k - 1) = x.unsigned % 2 ^ k :=
      Nat.and_two_pow_sub_one_eq_mod x.unsigned k
    rw [hand]
    -- x.unsigned % 2^k (Nat) = 0 ↔ x.signed % 2^k (Int) = 0
    constructor
    · intro h hc
      apply h
      -- from x.signed % 2^k = 0 (Int) deduce x.unsigned % 2^k = 0 (Nat)
      have hcong : (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int) = x.signed % (2 ^ k : _root_.Int) := by
        have hdvd : (2 ^ k : _root_.Int) ∣ (2 ^ 64 : _root_.Int) := pow_dvd_pow 2 (by omega)
        have hsig : x.signed % (2 ^ 64 : _root_.Int) = (x.unsigned : _root_.Int) % (2 ^ 64 : _root_.Int) := by
          have := signed_mod_eq_toNat_mod x
          simpa [unsigned] using this
        calc (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int)
            = ((x.unsigned : _root_.Int) % (2 ^ 64 : _root_.Int)) % (2 ^ k : _root_.Int) :=
              (Int.emod_emod_of_dvd _ hdvd).symm
          _ = (x.signed % (2 ^ 64 : _root_.Int)) % (2 ^ k : _root_.Int) := by rw [hsig]
          _ = x.signed % (2 ^ k : _root_.Int) := Int.emod_emod_of_dvd _ hdvd
      rw [hc] at hcong
      have : ((x.unsigned % 2 ^ k : Nat) : _root_.Int) = 0 := by
        rw [Int.natCast_mod]; exact hcong
      omega
    · intro h hc
      apply h
      have hcong : (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int) = x.signed % (2 ^ k : _root_.Int) := by
        have hdvd : (2 ^ k : _root_.Int) ∣ (2 ^ 64 : _root_.Int) := pow_dvd_pow 2 (by omega)
        have hsig : x.signed % (2 ^ 64 : _root_.Int) = (x.unsigned : _root_.Int) % (2 ^ 64 : _root_.Int) := by
          have := signed_mod_eq_toNat_mod x
          simpa [unsigned] using this
        calc (x.unsigned : _root_.Int) % (2 ^ k : _root_.Int)
            = ((x.unsigned : _root_.Int) % (2 ^ 64 : _root_.Int)) % (2 ^ k : _root_.Int) :=
              (Int.emod_emod_of_dvd _ hdvd).symm
          _ = (x.signed % (2 ^ 64 : _root_.Int)) % (2 ^ k : _root_.Int) := by rw [hsig]
          _ = x.signed % (2 ^ k : _root_.Int) := Int.emod_emod_of_dvd _ hdvd
      -- Goal: x.signed % 2^k = 0
      -- We have hcong : (x.unsigned : Int) % 2^k = x.signed % 2^k
      -- and hc : x.unsigned % 2^k = 0 (Nat)
      rw [← hcong]
      have hc_int : ((x.unsigned % 2^k : Nat) : _root_.Int) = 0 := by omega
      rw [Int.natCast_mod] at hc_int
      exact hc_int

  -- Main theorem: shrx_carry identity for Int64
  theorem shrx_carry'_eq (x : CompCert.Int64) (y : CompCert.Int) (H : y.toNat < 63) :
      add (shr' x y) (shr_carry' x y) = shrx' x y := by
    unfold shr' shr_carry' shrx' add
    simp only []
    have shamt_eq : y.toNat % 64 = y.toNat := Nat.mod_eq_of_lt (by omega : y.toNat < 64)
    by_cases hx : x.signed ≥ 0
    case pos =>
      -- Case x.signed ≥ 0: shr_carry' = zero, shrx' = shr'
      simp [hx, show ¬(x.signed < 0) by omega, shamt_eq]
      -- Goal: repr (x.signed >>> y.toNat) + zero = repr (x.signed >>> y.toNat)
      exact UInt64.add_zero _
    case neg =>
      -- Case x.signed < 0
      simp [show ¬(x.signed ≥ 0) by omega, shamt_eq]
      set shamt := y.toNat
      set low_bits := x.unsigned &&& ((1 <<< shamt) - 1)
      -- Simplify the condition
      have hxneg : x.signed < 0 := by omega
      by_cases hlow : low_bits ≠ 0
      case pos =>
        -- low_bits ≠ 0 AND x.signed < 0, so shr_carry' = one
        simp [hxneg, hlow]
        -- Goal: repr (x.signed >>> shamt) + one = repr ((x.signed + (1 <<< shamt - 1)) >>> shamt)
        have hd : (0 : _root_.Int) < (2 ^ shamt : _root_.Int) := by
          have : 0 < 2 ^ shamt := Nat.two_pow_pos shamt
          exact Nat.cast_lt.mpr this
        have hcast : ((1 <<< shamt - 1 : Nat) : _root_.Int) = (2 ^ shamt : _root_.Int) - 1 := by
          have h1 : (1 : Nat) <<< shamt = 2 ^ shamt := by rw [Nat.shiftLeft_eq, Nat.one_mul]
          have hle : (1 : Nat) ≤ 2 ^ shamt := Nat.one_le_two_pow
          rw [show (1 <<< shamt - 1 : Nat) = 2 ^ shamt - 1 by rw [← h1]]
          rw [Nat.cast_sub hle]
          simp
        have hnd : x.signed % (2 ^ shamt : _root_.Int) ≠ 0 := by
          exact shrx_low_bits_ne_iff x shamt (by omega) |>.mp hlow
        rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, CompCert.Int.int_one_shiftLeft_sub_one]
        push_cast
        rw [CompCert.Int.ediv_add_pred_of_not_dvd x.signed (2 ^ shamt : _root_.Int) hd hnd]
        -- repr (q + 1) = repr q + one
        rw [show (x.signed / (2^shamt : _root_.Int) + 1)
              = (x.signed / (2^shamt : _root_.Int)) + 1 from rfl]
        show add (repr (x.signed / (2^shamt:_root_.Int))) one
           = repr ((x.signed / (2^shamt:_root_.Int)) + 1)
        -- Since add = UInt64.add and repr = UInt64.ofInt, and one = repr 1 = UInt64.ofInt 1
        -- we need: UInt64.add (UInt64.ofInt a) (UInt64.ofInt 1) = UInt64.ofInt (a + 1)
        unfold add one repr
        apply UInt64.toNat.inj
        change (UInt64.ofInt (x.signed / 2 ^ shamt) + (UInt64.ofInt 1)).toNat = (UInt64.ofInt (x.signed / 2 ^ shamt + 1)).toNat
        rw [UInt64.toNat_add]
        have h1 : (UInt64.ofInt (x.signed / 2 ^ shamt)).toNat = ((x.signed / 2 ^ shamt) % 2^64).toNat := uint64_ofInt_toNat _
        have h2 : (UInt64.ofInt 1).toNat = 1 := by decide
        have h3 : (UInt64.ofInt ((x.signed / 2 ^ shamt) + 1)).toNat = (((x.signed / 2 ^ shamt) + 1) % 2^64).toNat := uint64_ofInt_toNat _
        rw [h1, h2, h3]
        have ha : 0 ≤ (x.signed / 2 ^ shamt) % 2^64 := Int.emod_nonneg _ (by omega)
        have hb : (x.signed / 2 ^ shamt) % 2^64 < 2^64 := Int.emod_lt_of_pos _ (by omega)
        omega
      case neg =>
        -- low_bits = 0, so shr_carry' = zero
        have hlow0 : low_bits = 0 := by omega
        simp [hxneg, hlow0]
        -- Goal: UInt64.add (repr (x.signed >>> shamt)) zero = repr ((x.signed + (1 <<< shamt - 1)) >>> shamt)
        show UInt64.add (repr (x.signed >>> shamt)) zero = repr ((x.signed + (1 <<< shamt - 1)) >>> shamt)
        conv_lhs => rw [show UInt64.add (repr (x.signed >>> shamt)) zero = repr (x.signed >>> shamt) by exact UInt64.add_zero _]
        -- When low bits are zero, x.signed is divisible by 2^shamt
        have hd : (0 : _root_.Int) < (2 ^ shamt : _root_.Int) := by
          have : 0 < 2 ^ shamt := Nat.two_pow_pos shamt
          exact Nat.cast_lt.mpr this
        have hdvd : x.signed % (2 ^ shamt : _root_.Int) = 0 := by
          by_contra h
          exact hlow ((shrx_low_bits_ne_iff x shamt (by omega)).mpr h)
        rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, CompCert.Int.natCast_one_shiftLeft_sub_one]
        push_cast
        rw [CompCert.Int.ediv_add_pred_of_dvd x.signed (2 ^ shamt : _root_.Int) hd hdvd]

  -- Int64 version: same key lemma for negative dividend and power-of-2 divisor
  private theorem tdiv_pow2_neg_eq_ediv_round64 (a : _root_.Int) (k : Nat) (ha : a < 0) :
      Int.tdiv a (2^k : _root_.Int) = (a + (2^k : _root_.Int) - 1) / (2^k : _root_.Int) := by
    exact CompCert.Int.tdiv_pow2_neg_eq_ediv_round a k ha

  -- Signed division by 2^n equals shrx' n (for n < 63)
  theorem divs_pow2'_eq (x : CompCert.Int64) (n : CompCert.Int64) (logn : CompCert.Int)
      (H1 : is_power2' n = some logn)
      (H2 : logn.toNat < 63) :
      divs x n = shrx' x logn := by
    -- Similar structure to Int32 version
    have ⟨hn_eq, hlogn_lt⟩ := is_power2'_pow n logn H1
    have hn_toNat : n.toNat = 2 ^ logn.toNat := is_power2'_toNat_pow n logn H1
    have hn_pos : 0 < n.toNat := by rw [hn_toNat]; exact Nat.two_pow_pos _

    -- n.toNat < 2^63, so n.signed = n.toNat (positive)
    have hn_signed_eq : n.signed = (n.toNat : _root_.Int) := by
      unfold signed
      have h_bound : n.toNat < 2^63 := by
        rw [hn_toNat]
        exact Nat.pow_lt_pow_right (by omega) H2
      have h_bound' : n.toNat < 2^64 := by omega
      have : n.toBitVec.toInt = (n.toNat : _root_.Int) := by
        have h2n : 2 * n.toBitVec.toNat < 2^64 := by
          have : n.toBitVec.toNat = n.toNat := by rfl
          rw [this]
          have : n.toNat < 2^63 := h_bound
          omega
        exact BitVec.toInt_eq_toNat_of_lt h2n
      exact this

    unfold divs shrx'
    apply UInt64.toNat.inj

    -- Substitute the key facts: n.signed = 2^logn.toNat
    have hn_signed_pow : n.signed = (2 ^ logn.toNat : _root_.Int) := by
      rw [hn_signed_eq, hn_toNat]
      simp [Nat.cast_pow]

    rw [hn_signed_pow]

    by_cases hx : x.signed ≥ 0
    · -- case pos: x.signed ≥ 0
      simp only [hx, ite_true]
      have htdiv_eq : x.signed.tdiv (2^logn.toNat : _root_.Int) = x.signed / (2^logn.toNat : _root_.Int) := by
        exact Int.tdiv_eq_ediv_of_nonneg hx
      rw [htdiv_eq]
      have hshr : (x.signed >>> logn.toNat) = x.signed / (↑(2 ^ logn.toNat) : _root_.Int) := Int.shiftRight_eq_div_pow x.signed logn.toNat
      rw [hshr]
    · -- case neg: x.signed < 0
      simp only [show ¬(x.signed ≥ 0) from by omega, ite_false]
      rw [Int.shiftRight_eq_div_pow]
      have hcast : ((1 <<< logn.toNat - 1 : Nat) : _root_.Int) = (2 ^ logn.toNat : _root_.Int) - 1 := by
        have h1 : (1 : Nat) <<< logn.toNat = 2 ^ logn.toNat := by rw [Nat.shiftLeft_eq, Nat.one_mul]
        have hle : (1 : Nat) ≤ 2 ^ logn.toNat := Nat.one_le_two_pow
        rw [show (1 <<< logn.toNat - 1 : Nat) = 2 ^ logn.toNat - 1 from by rw [← h1]]
        rw [Nat.cast_sub hle]
        simp
      rw [hcast]
      push_cast
      have htdiv_formula : x.signed.tdiv (2^logn.toNat : _root_.Int) = (x.signed + (2^logn.toNat : _root_.Int) - 1) / (2^logn.toNat : _root_.Int) := by
        exact tdiv_pow2_neg_eq_ediv_round64 x.signed logn.toNat (by omega)
      rw [htdiv_formula]
      -- The RHS has `(x.signed + (2^k - 1))` which equals `x.signed + 2^k - 1` by algebra
      have : x.signed + (2 ^ logn.toNat : _root_.Int) - 1 = x.signed + ((2 ^ logn.toNat : _root_.Int) - 1) := by ring
      rw [this]

  -- When the true signed sum is in range, `add` does not overflow (Int64 version)
  theorem add_signed_eq_of_range (i j : CompCert.Int64)
      (hlo : -(2^63 : _root_.Int) ≤ i.signed + j.signed)
      (hhi : i.signed + j.signed < (2^63 : _root_.Int)) :
      CompCert.Int64.signed (add i j) = i.signed + j.signed := by
    have hmod := add_signed_mod i j
    have hlo2 : -(2^63 : _root_.Int) ≤ CompCert.Int64.signed (add i j) := by
      have := @BitVec.le_toInt 64 (add i j).toBitVec
      simpa [signed] using this
    have hhi2 : CompCert.Int64.signed (add i j) < (2^63 : _root_.Int) := by
      have := @BitVec.toInt_lt 64 (add i j).toBitVec
      simpa [signed] using this
    omega

  -- `sub (shl one q) one` is the mask `2^q - 1`, with signed value `2^q - 1` for q < 63.
  theorem shl_one_sub_one_signed (q : CompCert.Int) (hq : q.toNat < 63) :
      CompCert.Int64.signed (sub (shl one (q.toNat.toUInt64)) one) = (2 ^ q.toNat : _root_.Int) - 1 := by
    have hshl : (shl one (q.toNat.toUInt64)).toNat = 2 ^ q.toNat := by
      show (UInt64.shiftLeft 1 (q.toNat.toUInt64)).toNat = 2 ^ q.toNat
      rw [show (UInt64.shiftLeft 1 (q.toNat.toUInt64)) = (1 : UInt64) <<< (q.toNat.toUInt64) from rfl, UInt64.toNat_shiftLeft]
      have h1 : (1 : UInt64).toNat = 1 := by rfl
      rw [h1]
      have hqnat : (q.toNat.toUInt64).toNat = q.toNat := by
        show (UInt64.ofNat q.toNat).toNat = q.toNat
        have hq64 : q.toNat < 2^64 := by omega
        simp
      rw [hqnat, Nat.mod_eq_of_lt (by omega : q.toNat < 64), Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    have hsub : (sub (shl one (q.toNat.toUInt64)) one).toNat = 2 ^ q.toNat - 1 := by
      show ((shl one (q.toNat.toUInt64)) - one).toNat = 2 ^ q.toNat - 1
      rw [UInt64.toNat_sub]
      have hone : (one : CompCert.Int64).toNat = 1 := by rfl
      rw [hone, hshl]
      have hp : 2 ^ q.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) (by omega)
      have hp1 : (1 : Nat) ≤ 2 ^ q.toNat := Nat.one_le_two_pow
      have : (2 ^ 64 - 1 + 2 ^ q.toNat) % 2 ^ 64 = 2 ^ q.toNat - 1 := by omega
      exact this
    -- signed = toNat since 2^q - 1 < 2^63
    have hlt : 2 ^ q.toNat - 1 < 2 ^ 63 := by
      have : 2 ^ q.toNat < 2 ^ 63 := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hsigned : CompCert.Int64.signed (sub (shl one (q.toNat.toUInt64)) one)
                     = ((sub (shl one (q.toNat.toUInt64)) one).toNat : _root_.Int) := by
      unfold signed
      have h2n : 2 * (sub (shl one (q.toNat.toUInt64)) one).toBitVec.toNat < 2^64 := by
        have : (sub (shl one (q.toNat.toUInt64)) one).toBitVec.toNat = (sub (shl one (q.toNat.toUInt64)) one).toNat := rfl
        rw [this, hsub]
        omega
      exact BitVec.toInt_eq_toNat_of_lt h2n
    rw [hsigned, hsub]
    have hp1 : (1 : Nat) ≤ 2 ^ q.toNat := Nat.one_le_two_pow
    push_cast [Nat.cast_sub hp1]
    ring

  -- shrx' for a negative argument equals shr' of the rounded value `p + (2^q - 1)`.
  theorem shrx_shr_neg_eq (p : CompCert.Int64) (q : CompCert.Int)
      (hp : p.signed < 0) (hq : q.toNat < 63) :
      shrx' p q = shr' (add p (sub (shl one (q.toNat.toUInt64)) one)) q := by
    have hmask : CompCert.Int64.signed (sub (shl one (q.toNat.toUInt64)) one)
                = (2 ^ q.toNat : _root_.Int) - 1 :=
      shl_one_sub_one_signed q hq
    have hrange_lo : -(2^63 : _root_.Int) ≤ p.signed + CompCert.Int64.signed (sub (shl one (q.toNat.toUInt64)) one) := by
      rw [hmask]
      have hplo : -(2^63 : _root_.Int) ≤ p.signed := by
        have := @BitVec.le_toInt 64 p.toBitVec
        simpa [signed] using this
      have hpk : (1 : _root_.Int) ≤ 2 ^ q.toNat := by
        exact_mod_cast Nat.one_le_two_pow
      omega
    have hrange_hi : p.signed + CompCert.Int64.signed (sub (shl one (q.toNat.toUInt64)) one) < (2^63 : _root_.Int) := by
      rw [hmask]
      have hpk : (2 ^ q.toNat : _root_.Int) < 2 ^ 63 := by
        have : (2:Nat) ^ q.toNat < 2 ^ 63 := Nat.pow_lt_pow_right (by omega) (by omega)
        exact_mod_cast this
      omega
    have hadd : CompCert.Int64.signed (add p (sub (shl one (q.toNat.toUInt64)) one))
              = p.signed + ((2 ^ q.toNat : _root_.Int) - 1) := by
      rw [add_signed_eq_of_range p (sub (shl one (q.toNat.toUInt64)) one) hrange_lo hrange_hi, hmask]
    unfold shrx' shr'
    simp only [show ¬(p.signed ≥ 0) by omega, if_false]
    rw [hadd]
    have hcast : ((1 <<< q.toNat - 1 : Nat) : _root_.Int) = (2 ^ q.toNat : _root_.Int) - 1 := by
      have h1 : (1 : Nat) <<< q.toNat = 2 ^ q.toNat := by rw [Nat.shiftLeft_eq, Nat.one_mul]
      have hle : (1 : Nat) ≤ 2 ^ q.toNat := Nat.one_le_two_pow
      rw [show (1 <<< q.toNat - 1 : Nat) = 2 ^ q.toNat - 1 by rw [← h1]]
      rw [Nat.cast_sub hle]
      simp
    rw [hcast]
    have hq64 : q.toNat % 64 = q.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hq64]

  -- Arithmetic shift by 63 broadcasts the sign bit (Int64 version)
  theorem shr_63_eq (p : CompCert.Int64) :
      shr' p (CompCert.Int.repr 63) = if p.signed < 0 then mone else zero := by
    unfold shr' CompCert.Int.repr repr
    have h63mod : ((UInt32.ofInt 63).toNat % 64) = 63 := by decide
    simp only [h63mod]
    have hshr : p.signed >>> 63 = if p.signed < 0 then -1 else 0 := by
      unfold signed
      have hp_lo : -(2^63 : _root_.Int) ≤ p.toBitVec.toInt := by
        have := @BitVec.le_toInt 64 p.toBitVec
        exact this
      have hp_hi : p.toBitVec.toInt < (2^63 : _root_.Int) := by
        have := @BitVec.toInt_lt 64 p.toBitVec
        exact this
      rw [Int.shiftRight_eq_div_pow]
      by_cases hp : p.toBitVec.toInt < 0
      · -- p < 0: p ∈ [-2^63, 0), so p / 2^63 = -1
        simp [hp]
        have : p.toBitVec.toInt / (2^63 : _root_.Int) = -1 := by omega
        exact this
      · -- p ≥ 0: p ∈ [0, 2^63), so p / 2^63 = 0
        simp [hp]
        have : p.toBitVec.toInt / (2^63 : _root_.Int) = 0 := by omega
        exact this
    rw [hshr]
    by_cases hp : p.signed < 0 <;> simp [hp] <;> decide

  -- Key lemma: shru' (shr' p 63) (64-n) is the sign mask (0 or 2^n-1) for Int64
  theorem sign_mask_eq (p : CompCert.Int64) (n : CompCert.Int)
      (hn0 : n.toNat ≠ 0) (hn : n.toNat < 63) :
      shru' (shr' p (CompCert.Int.repr 63)) (CompCert.Int.sub (CompCert.Int.repr 64) n)
        = if p.signed < 0 then sub (shl one (n.toNat.toUInt64)) one else zero := by
    rw [shr_63_eq]
    have hsub_toNat : (CompCert.Int.sub (CompCert.Int.repr 64) n).toNat = 64 - n.toNat := by
      show ((CompCert.Int.repr 64) - n).toNat = 64 - n.toNat
      have h64 : (CompCert.Int.repr 64).toNat = 64 := by decide
      rw [UInt32.toNat_sub, h64]
      have hn_bound : n.toNat < 2^32 := n.toBitVec.isLt
      omega
    set k := 64 - n.toNat
    by_cases hp : p.signed < 0
    case pos =>
      -- p < 0: shru' mone (sub (repr 64) n) = 2^n - 1 = sub (shl one n) one
      simp only [hp, if_true]
      have hallOnes_shift : ∀ m : Nat, m < 64 → m > 0 →
          (BitVec.allOnes 64 >>> m).toNat = 2^(64 - m) - 1 := by
        intro m hm1 hm2
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_allOnes]
        rw [Nat.shiftRight_eq_div_pow]
        have hsplit : (2:Nat)^64 = 2^(64 - m) * 2^m := by
          rw [← Nat.pow_add]; congr 1; omega
        have hpm : 0 < (2:Nat)^m := Nat.two_pow_pos m
        have hc : 0 < (2:Nat)^(64-m) := Nat.two_pow_pos (64-m)
        apply Nat.div_eq_of_lt_le
        · have : (2^(64-m) - 1) * 2^m = 2^64 - 2^m := by
            rw [Nat.sub_mul, Nat.one_mul, ← hsplit]
          omega
        · have : (2^(64-m) - 1 + 1) * 2^m = 2^64 := by
            rw [Nat.sub_add_cancel hc, ← hsplit]
          omega
      apply UInt64.toNat.inj
      -- LHS: (shru' mone (CompCert.Int.sub (CompCert.Int.repr 64) n)).toNat
      have hlhs : (shru' mone (CompCert.Int.sub (CompCert.Int.repr 64) n)).toNat = 2^n.toNat - 1 := by
        -- shru' mone m = shru mone (m.toNat.toUInt64); reduce to BitVec allOnes shift
        show (shru mone ((CompCert.Int.sub (CompCert.Int.repr 64) n).toNat.toUInt64)).toNat = 2^n.toNat - 1
        rw [show (shru mone ((CompCert.Int.sub (CompCert.Int.repr 64) n).toNat.toUInt64))
              = UInt64.ofBitVec ((mone : CompCert.Int64).toBitVec
                  >>> (((CompCert.Int.sub (CompCert.Int.repr 64) n).toNat.toUInt64).toNat % 64)) from rfl]
        rw [UInt64.toNat_ofBitVec]
        have hmone_bv : (mone : CompCert.Int64).toBitVec = BitVec.allOnes 64 := by decide
        rw [hmone_bv]
        -- shift amount = 64 - n.toNat
        have hk : (((CompCert.Int.sub (CompCert.Int.repr 64) n).toNat.toUInt64).toNat % 64) = 64 - n.toNat := by
          have hsub64 : (CompCert.Int.sub (CompCert.Int.repr 64) n).toNat = 64 - n.toNat := by
            show ((CompCert.Int.repr 64) - n).toNat = 64 - n.toNat
            rw [UInt32.toNat_sub]
            have h64 : (CompCert.Int.repr 64).toNat = 64 := by decide
            rw [h64]
            have hn_bound : n.toNat < 2^32 := n.toBitVec.isLt
            have hmod : (2^32 - n.toNat + 64) % 2^32 = 64 - n.toNat := by
              have hpow : (2:Nat)^32 = 4294967296 := by norm_num
              rw [hpow]; omega
            -- UInt32.toNat_sub gives (repr64.toNat + (2^32 - n.toNat)) % 2^32 form
            omega
          have htoU : ((CompCert.Int.sub (CompCert.Int.repr 64) n).toNat.toUInt64).toNat
                    = (CompCert.Int.sub (CompCert.Int.repr 64) n).toNat := by
            rw [hsub64]
            show (Nat.toUInt64 (64 - n.toNat)).toNat = 64 - n.toNat
            simp only [Nat.toUInt64]
            exact Nat.mod_eq_of_lt (by omega)
          rw [htoU, hsub64]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hk, hallOnes_shift (64 - n.toNat) (by omega) (by omega)]
        have hee : 64 - (64 - n.toNat) = n.toNat := by omega
        rw [hee]
      -- RHS: (sub (shl one n) one).toNat = 2^n.toNat - 1
      have hrhs : (sub (shl one (n.toNat.toUInt64)) one).toNat = 2^n.toNat - 1 := by
        show ((shl one (n.toNat.toUInt64)) - one).toNat = 2^n.toNat - 1
        rw [UInt64.toNat_sub]
        have hshl : (shl one (n.toNat.toUInt64)).toNat = 2^n.toNat := by
          show (UInt64.shiftLeft 1 (n.toNat.toUInt64)).toNat = 2^n.toNat
          rw [show (UInt64.shiftLeft 1 (n.toNat.toUInt64)) = (1:UInt64) <<< (n.toNat.toUInt64) from rfl, UInt64.toNat_shiftLeft]
          have : (1:UInt64).toNat = 1 := by rfl
          rw [this]
          have hqnat : (n.toNat.toUInt64).toNat = n.toNat := by
            show (UInt64.ofNat n.toNat).toNat = n.toNat
            have : n.toNat < 2^64 := by omega
            simp
          rw [hqnat, Nat.mod_eq_of_lt (by omega : n.toNat < 64), Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
        have hone : (one : CompCert.Int64).toNat = 1 := by rfl
        rw [hone, hshl]
        have hp2 : 2^n.toNat < 2^64 := Nat.pow_lt_pow_right (by omega) (by omega)
        have hp1 : (1:Nat) ≤ 2^n.toNat := Nat.one_le_two_pow
        have : (2^64 - 1 + 2^n.toNat) % 2^64 = 2^n.toNat - 1 := by omega
        exact this
      rw [hlhs, hrhs]
    case neg =>
      -- p ≥ 0: shru' zero (sub (repr 64) n) = zero
      simp [hp]
      unfold shru' zero shru
      simp [UInt64.shiftRight]

  -- Main Int64-level theorem: shrx' p n equals the sign-broadcast formula
  theorem shrx_shr_2'_eq (p : CompCert.Int64) (n : CompCert.Int) (hn : n.toNat < 63) :
      shrx' p n = if CompCert.Int.eq n CompCert.Int.zero then p else
        shr' (add p (shru' (shr' p (CompCert.Int.repr 63)) (CompCert.Int.sub (CompCert.Int.repr 64) n))) n := by
    by_cases hn0 : n = CompCert.Int.zero
    · -- n = zero: shrx' p 0 = p
      rw [hn0]
      have heq0 : CompCert.Int.eq CompCert.Int.zero CompCert.Int.zero = true := by
        unfold CompCert.Int.eq; simp
      rw [heq0]
      simp only [if_true]
      unfold shrx' CompCert.Int.zero
      have hz : (0 : UInt32).toNat = 0 := rfl
      by_cases hp : p.signed ≥ 0
      · simp only [hp, if_true, hz, Int.shiftRight_zero]
        exact repr_signed p
      · simp only [hp, if_false, hz]
        have h10 : ((1 <<< 0 - 1 : Nat) : _root_.Int) = 0 := by decide
        rw [h10, Int.shiftRight_zero]
        simpa using repr_signed p
    · -- n ≠ zero
      have heq_false : CompCert.Int.eq n CompCert.Int.zero = false := by
        unfold CompCert.Int.eq CompCert.Int.zero; simp; exact hn0
      simp [heq_false]
      have hn_toNat : n.toNat ≠ 0 := by
        unfold CompCert.Int.zero at hn0
        intro h
        apply hn0
        apply UInt32.toNat.inj
        simpa using h
      -- Rewrite using sign_mask_eq
      rw [sign_mask_eq p n hn_toNat hn]
      by_cases hp : p.signed < 0
      · -- p < 0: use shrx_shr_neg_eq
        simp [hp]
        -- Goal: shrx' p n = shr' (add p (sub (shl one (n.toUInt64)) one)) n
        -- But shrx_shr_neg_eq gives: shrx' p n = shr' (add p (sub (shl one (n.toNat.toUInt64)) one)) n
        -- Need to show n.toUInt64 = n.toNat.toUInt64
        have hconv : (n : UInt32).toUInt64 = n.toNat.toUInt64 := by
          apply UInt64.toNat.inj
          show (n.toUInt64).toNat = (n.toNat.toUInt64).toNat
          unfold UInt32.toUInt64
          show ({ toBitVec := { toFin := ⟨n.toNat, _⟩ } } : UInt64).toNat = (UInt64.ofNat n.toNat).toNat
          simp
        conv_lhs => rw [shrx_shr_neg_eq p n hp hn]
        congr 1
        congr 1
        congr 1
        congr 1
        exact hconv.symm
      · -- p ≥ 0
        simp [hp]
        unfold shrx' shr'
        have hge : p.signed ≥ 0 := by omega
        have hq64 : n.toNat % 64 = n.toNat := Nat.mod_eq_of_lt (by omega)
        simp [hge, hq64]

end CompCert.Int64
