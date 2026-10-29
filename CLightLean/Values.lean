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

/- This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. -/

import CLightLean.AST
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats
import CLightLean.Lib.Ptrofs

set_option maxErrors 2000

variable [Archi]

def block : Type := Nat deriving DecidableEq, Hashable, ToString, DecidableLT

-- `block` is a `def` (not `abbrev`) so it does not automatically inherit `Nat`'s
-- arithmetic/order/`Repr` instances during typeclass search (which only unfolds
-- `@[reducible]` definitions). Since `block` is *definitionally* `Nat`, we can
-- reuse `Nat`'s instances directly. This mirrors CompCert's `Values.v`, where
-- `block := positive` is likewise equipped with the ambient order/successor
-- operations on `positive` from the Coq standard library.
instance : Repr block := inferInstanceAs (Repr Nat)
instance : LT block := inferInstanceAs (LT Nat)
instance : DecidableRel (α := block) (· < ·) := inferInstanceAs (DecidableRel (α := Nat) (· < ·))
instance : LE block := inferInstanceAs (LE Nat)
instance : DecidableRel (α := block) (· ≤ ·) := inferInstanceAs (DecidableRel (α := Nat) (· ≤ ·))
instance (n : Nat) : OfNat block n := inferInstanceAs (OfNat Nat n)
instance : Add block := inferInstanceAs (Add Nat)

/- A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
-/

/- Pointer offsets use the modular `Ptrofs` type (see `CLightLean/Lib/Ptrofs.lean`),
   which is architecture-keyed (32-bit when `!ptr64`, 64-bit when `ptr64`) and matches
   CompCert's `ptrofs`.  This replaces the earlier `abbrev Ptrofs := Int` model. -/

abbrev ptrofs : Type := Ptrofs

inductive val : Type where
  | Vundef
  | Vint (i : CompCert.Int)
  | Vlong (i : CompCert.Int64)
  | Vfloat (f : CompCert.Float64)
  | Vsingle (f : CompCert.Float32)
  | Vptr (b : block) (ofs : ptrofs)  -- NOTE: ptrofs = Int (see warning above)
  deriving DecidableEq

def Vzero : val := .Vint CompCert.Int.zero
def Vone : val := .Vint CompCert.Int.one
def Vmone : val := .Vint CompCert.Int.mone

def Vtrue : val := .Vint CompCert.Int.one
def Vfalse : val := .Vint CompCert.Int.zero

def Vnullptr : val := if Archi.ptr64 then .Vlong CompCert.Int64.zero else .Vint CompCert.Int.zero
def Vptrofs (n : ptrofs) : val := if Archi.ptr64 then .Vlong (Ptrofs.to_int64 n) else .Vint (Ptrofs.to_int n)

-- * Operations over values

/- The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. -/

namespace Val

/-- Check whether a value has a given type.
    Vundef matches any type. Pointers match Tint on 32-bit and Tlong on 64-bit. -/
def has_type (v : val) (t : typ) : Prop :=
  match v, t with
  | .Vundef, _ => True
  | .Vint _, .Tint => True
  | .Vlong _, .Tlong => True
  | .Vfloat _, .Tfloat => True
  | .Vsingle _, .Tsingle => True
  | .Vptr _ _, .Tint => Archi.ptr64 = false
  | .Vptr _ _, .Tlong => Archi.ptr64 = true
  | .Vint _, .Tany32 => True
  | .Vsingle _, .Tany32 => True
  | .Vptr _ _, .Tany32 => Archi.ptr64 = false
  | _, .Tany64 => True
  | _, _ => False

/-- Check whether a list of values has the corresponding types (pairwise). -/
def has_type_list (vl : List val) (tl : List typ) : Prop :=
  match vl, tl with
  | [], [] => True
  | v :: vs, t :: ts => has_type v t ∧ has_type_list vs ts
  | _, _ => False

/-- Check whether a value matches an optional type.
    None type requires Vundef; Some t requires has_type v t. -/
def has_opttype (v : val) (ot : Option typ) : Prop :=
  match ot with
  | none => v = .Vundef
  | some t => has_type v t

theorem Vptr_has_type (b : block) (ofs : ptrofs) : has_type (.Vptr b ofs) Tptr := by
  unfold Tptr has_type
  cases Archi.ptr64 <;> rfl

theorem Vnullptr_has_type : has_type Vnullptr Tptr := by
  unfold has_type Vnullptr Tptr
  cases Archi.ptr64 <;> simp

theorem has_subtype (ty1 ty2 : typ) (v : val) :
    subtype ty1 ty2 = true → has_type v ty1 → has_type v ty2 := by
  cases ty1 <;> cases ty2 <;> cases v <;> simp [subtype, has_type]

theorem has_subtype_list (tyl1 tyl2 : List typ) (vl : List val) :
    subtype_list tyl1 tyl2 = true → has_type_list vl tyl1 → has_type_list vl tyl2 := by
  induction tyl1 generalizing tyl2 vl with
  | nil => cases tyl2 <;> cases vl <;> simp [subtype_list, has_type_list]
  | cons ty1 tys1 ih =>
    cases tyl2 <;> cases vl <;>
      simp_all [subtype_list, has_type_list, has_subtype ty1]

instance has_type_decidable (v : val) (t : typ) : Decidable (has_type v t) := by
  unfold has_type
  cases v <;> cases t <;>
    all_goals { exact inferInstance }

/-- Strict matching between values and extended types.
    Used to characterize arguments to function calls.
    Rejects Vundef (except for Xvoid), requires specific forms
    (e.g., booleans must be 0 or 1, 8-bit values must be properly extended). -/
def has_argtype (v : val) (x : xtype) : Prop :=
  match x, v with
  | .Xbool, .Vint n => n = CompCert.Int.zero ∨ n = CompCert.Int.one
  | .Xint8signed, .Vint n => n = CompCert.Int.sign_ext 8 n
  | .Xint8unsigned, .Vint n => n = CompCert.Int.zero_ext 8 n
  | .Xint16signed, .Vint n => n = CompCert.Int.sign_ext 16 n
  | .Xint16unsigned, .Vint n => n = CompCert.Int.zero_ext 16 n
  | .Xint, .Vint _ => True
  | .Xint, .Vptr _ _ => Archi.ptr64 = false
  | .Xlong, .Vlong _ => True
  | .Xlong, .Vptr _ _ => Archi.ptr64 = true
  | .Xfloat, .Vfloat _ => True
  | .Xsingle, .Vsingle _ => True
  | .Xptr, .Vptr _ _ => True
  | .Xptr, .Vint _ => Archi.ptr64 = false
  | .Xptr, .Vlong _ => Archi.ptr64 = true
  | .Xany32, .Vint _ => True
  | .Xany32, .Vsingle _ => True
  | .Xany32, .Vptr _ _ => Archi.ptr64 = false
  | .Xany64, .Vint _ => True
  | .Xany64, .Vlong _ => True
  | .Xany64, .Vptr _ _ => True
  | .Xany64, .Vsingle _ => True
  | .Xany64, .Vfloat _ => True
  | .Xvoid, _ => True
  | _, _ => False

/-- Pairwise application of has_argtype to lists of values and extended types. -/
def has_argtype_list (vl : List val) (xl : List xtype) : Prop :=
  List.Forall₂ has_argtype vl xl

/-- Lax matching between values and extended types.
    Vundef belongs to every type.
    Used to characterize return values from external calls and built-in functions. -/
def has_rettype (v : val) (r : xtype) : Prop :=
  match r, v with
  | .Xbool, .Vint n => n = CompCert.Int.zero ∨ n = CompCert.Int.one
  | .Xint8signed, .Vint n => n = CompCert.Int.sign_ext 8 n
  | .Xint8unsigned, .Vint n => n = CompCert.Int.zero_ext 8 n
  | .Xint16signed, .Vint n => n = CompCert.Int.sign_ext 16 n
  | .Xint16unsigned, .Vint n => n = CompCert.Int.zero_ext 16 n
  | .Xint, .Vint _ => True
  | .Xint, .Vptr _ _ => Archi.ptr64 = false
  | .Xlong, .Vlong _ => True
  | .Xlong, .Vptr _ _ => Archi.ptr64 = true
  | .Xfloat, .Vfloat _ => True
  | .Xsingle, .Vsingle _ => True
  | .Xptr, .Vptr _ _ => True
  | .Xptr, .Vint _ => Archi.ptr64 = false
  | .Xptr, .Vlong _ => Archi.ptr64 = true
  | .Xany32, .Vint _ => True
  | .Xany32, .Vsingle _ => True
  | .Xany32, .Vptr _ _ => Archi.ptr64 = false
  | .Xany64, _ => True
  | _, .Vundef => True
  | _, _ => False

theorem has_proj_xtype (v : val) (t : xtype) :
    has_rettype v t → has_type v (proj_xtype t) := by
  intro h
  cases t <;> cases v <;> simp only [has_rettype, proj_xtype, has_type, Tptr] at h ⊢
  all_goals (try trivial)
  -- Handle Tptr cases with explicit contradiction handling
  all_goals (try (
    cases h_arch : Archi.ptr64 <;>
    simp_all only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  ))

theorem has_inj_type (v : val) (t : typ) :
    has_type v t → has_rettype v (inj_type t) := by
  intro h
  cases v <;> cases t <;> simp only [has_type, inj_type, has_rettype] at h ⊢
  all_goals (try trivial)

/-- Truth values. Non-zero integers are treated as True.
    The integer 0 (also used to represent the null pointer) is False.
    Other values are neither true nor false. -/
inductive bool_of_val : val → Bool → Prop where
  | bool_of_val_int (n : CompCert.Int) :
      bool_of_val (.Vint n) (!(n == CompCert.Int.zero))

-- ** Arithmetic operations

/-- Integer negation. -/
def neg (v : val) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.neg n)
  | _ => .Vundef

/-- Float negation. -/
def negf (v : val) : val :=
  match v with
  | .Vfloat f => .Vfloat (CompCert.Float64.neg f)
  | _ => .Vundef

/-- Float absolute value. -/
def absf (v : val) : val :=
  match v with
  | .Vfloat f => .Vfloat (CompCert.Float64.abs f)
  | _ => .Vundef

/-- Single-precision float negation. -/
def negfs (v : val) : val :=
  match v with
  | .Vsingle f => .Vsingle (CompCert.Float32.neg f)
  | _ => .Vundef

/-- Single-precision float absolute value. -/
def absfs (v : val) : val :=
  match v with
  | .Vsingle f => .Vsingle (CompCert.Float32.abs f)
  | _ => .Vundef

/-- Convert option val to val, using Vundef for None. -/
def maketotal (ov : Option val) : val :=
  match ov with
  | some v => v
  | none => .Vundef

/-- Convert float to int (with rounding). -/
def intoffloat (v : val) : Option val :=
  match v with
  | .Vfloat f => (CompCert.Float64.to_int f).map .Vint
  | _ => none

/-- Convert float to unsigned int. -/
def intuoffloat (v : val) : Option val :=
  match v with
  | .Vfloat f => (CompCert.Float64.to_intu f).map .Vint
  | _ => none

/-- Convert signed int to float. -/
def floatofint (v : val) : Option val :=
  match v with
  | .Vint n => some (.Vfloat (CompCert.Float64.of_int n))
  | _ => none

/-- Convert unsigned int to float. -/
def floatofintu (v : val) : Option val :=
  match v with
  | .Vint n => some (.Vfloat (CompCert.Float64.of_intu n))
  | _ => none

/-- Convert single to int. -/
def intofsingle (v : val) : Option val :=
  match v with
  | .Vsingle f => (CompCert.Float32.to_int f).map .Vint
  | _ => none

/-- Convert single to unsigned int. -/
def intuofsingle (v : val) : Option val :=
  match v with
  | .Vsingle f => (CompCert.Float32.to_intu f).map .Vint
  | _ => none

/-- Convert signed int to single. -/
def singleofint (v : val) : Option val :=
  match v with
  | .Vint n => some (.Vsingle (CompCert.Float32.of_int n))
  | _ => none

/-- Convert unsigned int to single. -/
def singleofintu (v : val) : Option val :=
  match v with
  | .Vint n => some (.Vsingle (CompCert.Float32.of_intu n))
  | _ => none

/-- Integer negation (duplicate of neg). -/
def negint (v : val) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.neg n)
  | _ => .Vundef

/-- Bitwise NOT. -/
def notint (v : val) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.not n)
  | _ => .Vundef

/-- Convert boolean to value. -/
def of_bool (b : Bool) : val := if b then Vtrue else Vfalse

/-- Check if value is a boolean (Vtrue or Vfalse). -/
def is_bool (v : val) : Bool := v == Vtrue || v == Vfalse

/-- Normalize to boolean or Vundef. -/
def norm_bool (v : val) : val := if is_bool v then v else .Vundef

/-- Convert value to boolean (C truthiness). -/
def boolval (v : val) : val :=
  match v with
  | .Vint n => of_bool (!(n == CompCert.Int.zero))
  | .Vptr _ _ => Vtrue
  | _ => .Vundef

/-- Boolean negation. -/
def notbool (v : val) : val :=
  match v with
  | .Vint n => of_bool (n == CompCert.Int.zero)
  | .Vptr _ _ => Vfalse
  | _ => .Vundef

/-- Zero extension to nbits. -/
def zero_ext (nbits : Nat) (v : val) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.zero_ext nbits n)
  | _ => .Vundef

/-- Sign extension to nbits. -/
def sign_ext (nbits : Nat) (v : val) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.sign_ext nbits n)
  | _ => .Vundef

/-- Convert float to single. -/
def singleoffloat (v : val) : val :=
  match v with
  | .Vfloat f => .Vsingle (CompCert.Float64.to_single f)
  | _ => .Vundef

/-- Convert single to float. -/
def floatofsingle (v : val) : val :=
  match v with
  | .Vsingle f => .Vfloat (CompCert.Float64.of_single f)
  | _ => .Vundef

/-- Integer addition (with pointer arithmetic). -/
def add (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.add n1 n2)
  | .Vptr b1 ofs1, .Vint n2 =>
      if Archi.ptr64 then .Vundef
      else .Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int n2))
  | .Vint n1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then .Vundef
      else .Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int n1))
  | _, _ => .Vundef

/-- Integer subtraction (with pointer arithmetic). -/
def sub (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.sub n1 n2)
  | .Vptr b1 ofs1, .Vint n2 =>
      if Archi.ptr64 then .Vundef
      else .Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int n2))
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then .Vundef
      else if b1 == b2 then .Vint (Ptrofs.to_int (Ptrofs.sub ofs1 ofs2))
           else .Vundef
  | _, _ => .Vundef

/-- Integer multiplication. -/
def mul (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.mul n1 n2)
  | _, _ => .Vundef

/-- Signed multiply high (upper 32 bits of 64-bit result). -/
def mulhs (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.mulhs n1 n2)
  | _, _ => .Vundef

/-- Unsigned multiply high. -/
def mulhu (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.mulhu n1 n2)
  | _, _ => .Vundef

/-- Signed division. Returns None on division by zero or overflow. -/
def divs (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if n2 == CompCert.Int.zero
         || (n1 == CompCert.Int.repr CompCert.Int.min_signed && n2 == CompCert.Int.mone)
      then none
      else some (.Vint (CompCert.Int.divs n1 n2))
  | _, _ => none

/-- Signed modulo. -/
def mods (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if n2 == CompCert.Int.zero
         || (n1 == CompCert.Int.repr CompCert.Int.min_signed && n2 == CompCert.Int.mone)
      then none
      else some (.Vint (CompCert.Int.mods n1 n2))
  | _, _ => none

/-- Unsigned division. -/
def divu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if n2 == CompCert.Int.zero then none
      else some (.Vint (CompCert.Int.divu n1 n2))
  | _, _ => none

/-- Unsigned modulo. -/
def modu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if n2 == CompCert.Int.zero then none
      else some (.Vint (CompCert.Int.modu n1 n2))
  | _, _ => none

/-- Add with carry. -/
def add_carry (v1 v2 cin : val) : val :=
  match v1, v2, cin with
  | .Vint n1, .Vint n2, .Vint c => .Vint (CompCert.Int.add_carry n1 n2 c)
  | _, _, _ => .Vundef

/-- Subtraction overflow flag. -/
def sub_overflow (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.sub_overflow n1 n2 CompCert.Int.zero)
  | _, _ => .Vundef

/-- Negative test (sign bit). -/
def negative (v : val) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.negative n)
  | _ => .Vundef

/-- Bitwise AND. -/
def and (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.and n1 n2)
  | _, _ => .Vundef

/-- Bitwise OR. -/
def or (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.or n1 n2)
  | _, _ => .Vundef

/-- Bitwise XOR. -/
def xor (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.xor n1 n2)
  | _, _ => .Vundef

/-- Shift left. -/
def shl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int.iwordsize
      then .Vint (CompCert.Int.shl n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- Arithmetic shift right. -/
def shr (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int.iwordsize
      then .Vint (CompCert.Int.shr n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- Shift right with carry. -/
def shr_carry (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int.iwordsize
      then .Vint (CompCert.Int.shr_carry n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- Signed division by power of 2. -/
def shrx (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if CompCert.Int.ltu n2 (CompCert.Int.repr 31)
      then some (.Vint (CompCert.Int.shrx n1 n2))
      else none
  | _, _ => none

/-- Logical shift right. -/
def shru (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int.iwordsize
      then .Vint (CompCert.Int.shru n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- Rotate left. -/
def rol (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.rol n1 n2)
  | _, _ => .Vundef

/-- Rotate left and mask. -/
def rolm (v : val) (amount mask : CompCert.Int) : val :=
  match v with
  | .Vint n => .Vint (CompCert.Int.rolm n amount mask)
  | _ => .Vundef

/-- Rotate right. -/
def ror (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (CompCert.Int.ror n1 n2)
  | _, _ => .Vundef

/-- Float addition. -/
def addf (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (CompCert.Float64.add f1 f2).value
  | _, _ => .Vundef

/-- Float subtraction. -/
def subf (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (CompCert.Float64.sub f1 f2).value
  | _, _ => .Vundef

/-- Float multiplication. -/
def mulf (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (CompCert.Float64.mul f1 f2).value
  | _, _ => .Vundef

/-- Float division. -/
def divf (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (CompCert.Float64.div f1 f2).value
  | _, _ => .Vundef

/-- Construct float from two 32-bit words. -/
def floatofwords (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vfloat (CompCert.Float64.from_words n1 n2)
  | _, _ => .Vundef

/-- Single addition. -/
def addfs (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (CompCert.Float32.add f1 f2).value
  | _, _ => .Vundef

/-- Single subtraction. -/
def subfs (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (CompCert.Float32.sub f1 f2).value
  | _, _ => .Vundef

/-- Single multiplication. -/
def mulfs (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (CompCert.Float32.mul f1 f2).value
  | _, _ => .Vundef

/-- Single division. -/
def divfs (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (CompCert.Float32.div f1 f2).value
  | _, _ => .Vundef

-- ** Operations on 64-bit integers

/-- Construct 64-bit int from two 32-bit words. -/
def longofwords (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vlong (CompCert.Int64.ofwords n1 n2)
  | _, _ => .Vundef

/-- Extract low 32 bits. -/
def loword (v : val) : val :=
  match v with
  | .Vlong n => .Vint (CompCert.Int64.loword n)
  | _ => .Vundef

/-- Extract high 32 bits. -/
def hiword (v : val) : val :=
  match v with
  | .Vlong n => .Vint (CompCert.Int64.hiword n)
  | _ => .Vundef

/-- 64-bit negation. -/
def negl (v : val) : val :=
  match v with
  | .Vlong n => .Vlong (CompCert.Int64.neg n)
  | _ => .Vundef

/-- 64-bit bitwise NOT. -/
def notl (v : val) : val :=
  match v with
  | .Vlong n => .Vlong (CompCert.Int64.not n)
  | _ => .Vundef

/-- Sign-extend 32-bit int to 64-bit. -/
def longofint (v : val) : val :=
  match v with
  | .Vint n => .Vlong (CompCert.Int64.repr n.signed)
  | _ => .Vundef

/-- Zero-extend 32-bit int to 64-bit. -/
def longofintu (v : val) : val :=
  match v with
  | .Vint n => .Vlong (CompCert.Int64.repr n.unsigned)
  | _ => .Vundef

/-- Convert float to signed 64-bit int. -/
def longoffloat (v : val) : Option val :=
  match v with
  | .Vfloat f => (CompCert.Float64.to_long f).map .Vlong
  | _ => none

/-- Convert float to unsigned 64-bit int. -/
def longuoffloat (v : val) : Option val :=
  match v with
  | .Vfloat f => (CompCert.Float64.to_longu f).map .Vlong
  | _ => none

/-- Convert single to signed 64-bit int. -/
def longofsingle (v : val) : Option val :=
  match v with
  | .Vsingle f => (CompCert.Float32.to_long f).map .Vlong
  | _ => none

/-- Convert single to unsigned 64-bit int. -/
def longuofsingle (v : val) : Option val :=
  match v with
  | .Vsingle f => (CompCert.Float32.to_longu f).map .Vlong
  | _ => none

/-- Convert signed 64-bit int to float. -/
def floatoflong (v : val) : Option val :=
  match v with
  | .Vlong n => some (.Vfloat (CompCert.Float64.of_long n))
  | _ => none

/-- Convert unsigned 64-bit int to float. -/
def floatoflongu (v : val) : Option val :=
  match v with
  | .Vlong n => some (.Vfloat (CompCert.Float64.of_longu n))
  | _ => none

/-- Convert signed 64-bit int to single. -/
def singleoflong (v : val) : Option val :=
  match v with
  | .Vlong n => some (.Vsingle (CompCert.Float32.of_long n))
  | _ => none

/-- Convert unsigned 64-bit int to single. -/
def singleoflongu (v : val) : Option val :=
  match v with
  | .Vlong n => some (.Vsingle (CompCert.Float32.of_longu n))
  | _ => none

/-- 64-bit addition (with pointer arithmetic). -/
def addl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.add n1 n2)
  | .Vptr b1 ofs1, .Vlong n2 =>
      if Archi.ptr64 then .Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int64 n2))
      else .Vundef
  | .Vlong n1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then .Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 n1))
      else .Vundef
  | _, _ => .Vundef

/-- 64-bit subtraction (with pointer arithmetic). -/
def subl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.sub n1 n2)
  | .Vptr b1 ofs1, .Vlong n2 =>
      if Archi.ptr64 then .Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int64 n2))
      else .Vundef
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if !Archi.ptr64 then .Vundef
      else if b1 == b2 then .Vlong (Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2))
           else .Vundef
  | _, _ => .Vundef

/-- 64-bit multiplication. -/
def mull (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.mul n1 n2)
  | _, _ => .Vundef

/-- 64-bit multiply from two 32-bit inputs. -/
def mull' (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vlong (CompCert.Int64.mul' n1 n2)
  | _, _ => .Vundef

/-- 64-bit signed multiply high. -/
def mullhs (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.mulhs n1 n2)
  | _, _ => .Vundef

/-- 64-bit unsigned multiply high. -/
def mullhu (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.mulhu n1 n2)
  | _, _ => .Vundef

/-- 64-bit signed division. -/
def divls (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if n2 == CompCert.Int64.zero
         || (n1 == CompCert.Int64.repr CompCert.Int64.min_signed && n2 == CompCert.Int64.mone)
      then none
      else some (.Vlong (CompCert.Int64.divs n1 n2))
  | _, _ => none

/-- 64-bit signed modulo. -/
def modls (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if n2 == CompCert.Int64.zero
         || (n1 == CompCert.Int64.repr CompCert.Int64.min_signed && n2 == CompCert.Int64.mone)
      then none
      else some (.Vlong (CompCert.Int64.mods n1 n2))
  | _, _ => none

/-- 64-bit unsigned division. -/
def divlu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if n2 == CompCert.Int64.zero then none
      else some (.Vlong (CompCert.Int64.divu n1 n2))
  | _, _ => none

/-- 64-bit unsigned modulo. -/
def modlu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if n2 == CompCert.Int64.zero then none
      else some (.Vlong (CompCert.Int64.modu n1 n2))
  | _, _ => none

/-- 64-bit add with carry. -/
def addl_carry (v1 v2 cin : val) : val :=
  match v1, v2, cin with
  | .Vlong n1, .Vlong n2, .Vlong c => .Vlong (CompCert.Int64.add_carry n1 n2 c)
  | _, _, _ => .Vundef

/-- 64-bit subtraction overflow flag. -/
def subl_overflow (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vint (CompCert.Int.repr (CompCert.Int64.sub_overflow n1 n2 CompCert.Int64.zero).unsigned)
  | _, _ => .Vundef

/-- 64-bit negative test. -/
def negativel (v : val) : val :=
  match v with
  | .Vlong n => .Vint (CompCert.Int.repr (CompCert.Int64.negative n).unsigned)
  | _ => .Vundef

/-- 64-bit bitwise AND. -/
def andl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.and n1 n2)
  | _, _ => .Vundef

/-- 64-bit bitwise OR. -/
def orl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.or n1 n2)
  | _, _ => .Vundef

/-- 64-bit bitwise XOR. -/
def xorl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.xor n1 n2)
  | _, _ => .Vundef

/-- 64-bit shift left. -/
def shll (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int64.iwordsize'
      then .Vlong (CompCert.Int64.shl' n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- 64-bit arithmetic shift right. -/
def shrl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int64.iwordsize'
      then .Vlong (CompCert.Int64.shr' n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- 64-bit logical shift right. -/
def shrlu (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int64.iwordsize'
      then .Vlong (CompCert.Int64.shru' n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- 64-bit signed division by power of 2. -/
def shrxl (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if CompCert.Int.ltu n2 (CompCert.Int.repr 63)
      then some (.Vlong (CompCert.Int64.shrx' n1 n2))
      else none
  | _, _ => none

/-- 64-bit shift right with carry. -/
def shrl_carry (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if CompCert.Int.ltu n2 CompCert.Int64.iwordsize'
      then .Vlong (CompCert.Int64.shr_carry' n1 n2)
      else .Vundef
  | _, _ => .Vundef

/-- 64-bit rotate left. -/
def roll (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 => .Vlong (CompCert.Int64.rol n1 (CompCert.Int64.repr n2.unsigned))
  | _, _ => .Vundef

/-- 64-bit rotate right. -/
def rorl (v1 v2 : val) : val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 => .Vlong (CompCert.Int64.ror n1 (CompCert.Int64.repr n2.unsigned))
  | _, _ => .Vundef

/-- 64-bit rotate left and mask. -/
def rolml (v : val) (amount : CompCert.Int) (mask : CompCert.Int64) : val :=
  match v with
  | .Vlong n => .Vlong (CompCert.Int64.rolm n (CompCert.Int64.repr amount.unsigned) mask)
  | _ => .Vundef

theorem rolml_zero (x : val) (m : CompCert.Int64) :
    rolml x CompCert.Int.zero m = andl x (.Vlong m) := by
  cases x with
  | Vundef => rfl
  | Vint _ => rfl
  | Vlong n =>
    unfold rolml andl
    simp [CompCert.Int64.rolm]
    -- Goal: and (n.rol (repr 0)) m = and n m
    have : CompCert.Int64.repr (CompCert.Int.zero.unsigned : Int) = CompCert.Int64.zero := rfl
    rw [this, CompCert.Int64.rol_zero]
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl

/-- 64-bit zero extension. -/
def zero_ext_l (nbits : Nat) (v : val) : val :=
  match v with
  | .Vlong n => .Vlong (CompCert.Int64.zero_ext nbits n)
  | _ => .Vundef

/-- 64-bit sign extension. -/
def sign_ext_l (nbits : Nat) (v : val) : val :=
  match v with
  | .Vlong n => .Vlong (CompCert.Int64.sign_ext nbits n)
  | _ => .Vundef

-- ** Comparisons

section COMPARISONS

variable (valid_ptr : block → Int → Bool)

/-- A pointer is weakly valid if it points within a block or one past the end -/
def weak_valid_ptr (b : block) (ofs : Ptrofs) : Bool :=
  valid_ptr b ofs.unsigned || valid_ptr b (ofs.unsigned - 1)

/-- Signed integer comparison -/
def cmp_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => some (CompCert.Int.cmp c n1 n2)
  | _, _ => none

/-- Comparison result for different blocks -/
def cmp_different_blocks (c : comparison) : Option Bool :=
  match c with
  | .Ceq => some false
  | .Cne => some true
  | _ => none

omit [Archi] in
theorem cmp_different_blocks_negate (c : comparison) :
    cmp_different_blocks (negate_comparison c) = Option.map not (cmp_different_blocks c) := by
  cases c <;> simp [cmp_different_blocks, negate_comparison]

omit [Archi] in
theorem cmp_different_blocks_swap (c : comparison) :
    cmp_different_blocks (swap_comparison c) = cmp_different_blocks c := by
  cases c <;> simp [cmp_different_blocks, swap_comparison]

/-- Unsigned integer comparison with pointer support -/
def cmpu_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => some (CompCert.Int.cmpu c n1 n2)
  | .Vint n1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then none
      else if n1 == CompCert.Int.zero && weak_valid_ptr valid_ptr b2 ofs2
           then cmp_different_blocks c
           else none
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then none
      else if b1 == b2 then
             if weak_valid_ptr valid_ptr b1 ofs1 && weak_valid_ptr valid_ptr b2 ofs2
             then some (Ptrofs.cmpu c ofs1 ofs2)
             else none
           else
             if valid_ptr b1 ofs1.unsigned && valid_ptr b2 ofs2.unsigned
             then cmp_different_blocks c
             else none
  | .Vptr b1 ofs1, .Vint n2 =>
      if Archi.ptr64 then none
      else if n2 == CompCert.Int.zero && weak_valid_ptr valid_ptr b1 ofs1
           then cmp_different_blocks c
           else none
  | _, _ => none

/-- Float comparison -/
def cmpf_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => some (CompCert.Float64.cmp c f1 f2)
  | _, _ => none

/-- Single-precision float comparison -/
def cmpfs_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => some (CompCert.Float32.cmp c f1 f2)
  | _, _ => none

/-- Signed 64-bit integer comparison -/
def cmpl_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => some (CompCert.Int64.cmp c n1 n2)
  | _, _ => none

/-- Unsigned 64-bit integer comparison with pointer support -/
def cmplu_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => some (CompCert.Int64.cmpu c n1 n2)
  | .Vlong n1, .Vptr b2 ofs2 =>
      if !Archi.ptr64 then none
      else if n1 == CompCert.Int64.zero && weak_valid_ptr valid_ptr b2 ofs2
           then cmp_different_blocks c
           else none
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if !Archi.ptr64 then none
      else if b1 == b2 then
             if weak_valid_ptr valid_ptr b1 ofs1 && weak_valid_ptr valid_ptr b2 ofs2
             then some (Ptrofs.cmpu c ofs1 ofs2)
             else none
           else
             if valid_ptr b1 ofs1.unsigned && valid_ptr b2 ofs2.unsigned
             then cmp_different_blocks c
             else none
  | .Vptr b1 ofs1, .Vlong n2 =>
      if !Archi.ptr64 then none
      else if n2 == CompCert.Int64.zero && weak_valid_ptr valid_ptr b1 ofs1
           then cmp_different_blocks c
           else none
  | _, _ => none

/-- Convert option bool to value -/
def of_optbool (ob : Option Bool) : val :=
  match ob with
  | some true => Vtrue
  | some false => Vfalse
  | none => .Vundef

/-- Signed integer comparison returning a value -/
def cmp (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmp_bool c v1 v2)

/-- Unsigned integer comparison returning a value -/
def cmpu (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpu_bool valid_ptr c v1 v2)

/-- Float comparison returning a value -/
def cmpf (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpf_bool c v1 v2)

/-- Single float comparison returning a value -/
def cmpfs (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpfs_bool c v1 v2)

/-- Signed 64-bit comparison returning option value -/
def cmpl (c : comparison) (v1 v2 : val) : Option val :=
  (cmpl_bool c v1 v2).map of_bool

/-- Unsigned 64-bit comparison returning option value -/
def cmplu (c : comparison) (v1 v2 : val) : Option val :=
  (cmplu_bool valid_ptr c v1 v2).map of_bool

/-- Test if value ANDed with mask is zero -/
def maskzero_bool (v : val) (mask : CompCert.Int) : Option Bool :=
  match v with
  | .Vint n => some (CompCert.Int.and n mask == CompCert.Int.zero)
  | _ => none

end COMPARISONS

-- ** Helper operations

/-- Add offset to pointer -/
def offset_ptr (v : val) (delta : ptrofs) : val :=
  match v with
  | .Vptr b ofs => .Vptr b (Ptrofs.add ofs delta)
  | _ => .Vundef

/-- Normalize value to given type, returning Vundef if type mismatch -/
def normalize (v : val) (ty : typ) : val :=
  match v, ty with
  | .Vundef, _ => .Vundef
  | .Vint _, .Tint => v
  | .Vlong _, .Tlong => v
  | .Vfloat _, .Tfloat => v
  | .Vsingle _, .Tsingle => v
  | .Vptr _ _, .Tint => if Archi.ptr64 then .Vundef else v
  | .Vptr _ _, .Tlong => if Archi.ptr64 then v else .Vundef
  | .Vptr _ _, .Tany32 => if Archi.ptr64 then .Vundef else v
  | .Vint _, .Tany32 => v
  | .Vsingle _, .Tany32 => v
  | _, .Tany64 => v
  | _, _ => .Vundef

/-- Select value based on comparison result -/
def select (cmp : Option Bool) (v1 v2 : val) (ty : typ) : val :=
  match cmp with
  | some b => normalize (if b then v1 else v2) ty
  | none => .Vundef

/-- Load result reflects storing a value with a memory chunk then reading back -/
def load_result (chunk : memory_chunk) (v : val) : val :=
  match chunk, v with
  | .Mbool, .Vint n => norm_bool (.Vint (CompCert.Int.zero_ext 8 n))
  | .Mint8signed, .Vint n => .Vint (CompCert.Int.sign_ext 8 n)
  | .Mint8unsigned, .Vint n => .Vint (CompCert.Int.zero_ext 8 n)
  | .Mint16signed, .Vint n => .Vint (CompCert.Int.sign_ext 16 n)
  | .Mint16unsigned, .Vint n => .Vint (CompCert.Int.zero_ext 16 n)
  | .Mint32, .Vint n => .Vint n
  | .Mint32, .Vptr b ofs => if Archi.ptr64 then .Vundef else .Vptr b ofs
  | .Mint64, .Vlong n => .Vlong n
  | .Mint64, .Vptr b ofs => if Archi.ptr64 then .Vptr b ofs else .Vundef
  | .Mfloat32, .Vsingle f => .Vsingle f
  | .Mfloat64, .Vfloat f => .Vfloat f
  | .Many32, .Vint _ => v
  | .Many32, .Vsingle _ => v
  | .Many32, .Vptr _ _ => if Archi.ptr64 then .Vundef else v
  | .Many64, _ => v
  | _, _ => .Vundef

-- ** Theorems on operations

theorem normalize_type (v : val) (ty : typ) :
    has_type (normalize v ty) ty := by
  cases v <;> cases ty <;>
    simp only [normalize, has_type] <;>
    (first
      | trivial
      | (split <;> simp only)
      | (by_cases hp : Archi.ptr64 = true <;> simp [hp]))

theorem normalize_idem (v : val) (ty : typ) :
    has_type v ty → normalize v ty = v := by
  intro h
  cases v <;> cases ty <;>
    simp_all only [normalize, has_type] <;>
    rfl

theorem norm_bool_cases (v : val) :
    norm_bool v = .Vundef ∨ norm_bool v = Vfalse ∨ norm_bool v = Vtrue := by
  unfold norm_bool
  split
  case isTrue h =>
    -- is_bool v = true means v = Vtrue ∨ v = Vfalse
    unfold is_bool at h
    simp [Vtrue, Vfalse] at h
    cases h with
    | inl h => right; right; exact h
    | inr h => right; left; exact h
  case isFalse h =>
    left; rfl

theorem load_result_xtype (chunk : memory_chunk) (v : val) :
    has_rettype (load_result chunk v) (xtype_of_chunk chunk) := by
  cases chunk <;> cases v <;>
    simp only [load_result, xtype_of_chunk, has_rettype]
  case Mbool.Vint n =>
    rcases norm_bool_cases (.Vint (CompCert.Int.zero_ext 8 n)) with h | h | h <;>
      simp only [h, Vfalse, Vtrue] <;>
      tauto
  case Mint8signed.Vint n => exact (CompCert.Int.sign_ext_idem 8 n).symm
  case Mint8unsigned.Vint n => exact (CompCert.Int.zero_ext_idem 8 n).symm
  case Mint16signed.Vint n => exact (CompCert.Int.sign_ext_idem 16 n).symm
  case Mint16unsigned.Vint n => exact (CompCert.Int.zero_ext_idem 16 n).symm
  case Mint32.Vptr b ofs => by_cases h : Archi.ptr64 = true <;> simp [h]
  case Mint64.Vptr b ofs => by_cases h : Archi.ptr64 = true <;> simp [h]
  case Many32.Vptr b ofs => by_cases h : Archi.ptr64 = true <;> simp [h]

theorem load_result_type (chunk : memory_chunk) (v : val) :
    has_type (load_result chunk v) (type_of_chunk chunk) := by
  cases chunk <;> cases v <;>
    simp only [load_result, type_of_chunk, has_type]
  case Mbool.Vint n =>
    rcases norm_bool_cases (.Vint (CompCert.Int.zero_ext 8 n)) with h | h | h <;>
      simp only [h, Vfalse, Vtrue]
  case Mint32.Vptr b ofs => by_cases h : Archi.ptr64 = true <;> simp [h]
  case Mint64.Vptr b ofs => by_cases h : Archi.ptr64 = true <;> simp [h]
  case Many32.Vptr b ofs => by_cases h : Archi.ptr64 = true <;> simp [h]

theorem load_result_same (v : val) (ty : typ) :
    has_type v ty → load_result (chunk_of_type ty) v = v := by
  intro hty
  cases v <;> cases ty <;>
    simp_all only [has_type, chunk_of_type, load_result] <;>
    rfl


theorem cast8unsigned_and (x : val) :
    zero_ext 8 x = and x (.Vint (CompCert.Int.repr 255)) := by
  cases x <;> simp [zero_ext, and]
  case Vint i =>
    rw [CompCert.Int.zero_ext_and]
    norm_num [two_p]

theorem cast16unsigned_and (x : val) :
    zero_ext 16 x = and x (.Vint (CompCert.Int.repr 65535)) := by
  cases x <;> simp [zero_ext, and]
  case Vint i =>
    rw [CompCert.Int.zero_ext_and]
    norm_num [two_p]

theorem bool_of_val_of_bool (b1 b2 : Bool) :
    bool_of_val (of_bool b1) b2 → b1 = b2 := by
  intro h
  unfold of_bool at h
  cases b1 <;> cases b2 <;> (try simp [Vtrue, Vfalse] at h; try (cases h; simp at *));
  . contradiction
  . contradiction

theorem of_bool_is_bool (b : Bool) :
    is_bool (of_bool b) = true := by
  unfold is_bool of_bool
  cases b <;> simp [Vtrue, Vfalse]

theorem norm_bool_idem (v : val) :
    norm_bool (norm_bool v) = norm_bool v := by
  unfold norm_bool
  split <;> simp [is_bool]

theorem notbool_negb_1 (b : Bool) :
    of_bool (!b) = notbool (of_bool b) := by
  cases b <;> rfl

theorem notbool_negb_2 (b : Bool) :
    of_bool b = notbool (of_bool (!b)) := by
  cases b <;> rfl

theorem notbool_negb_3 (ob : Option Bool) :
    of_optbool (Option.map not ob) = notbool (of_optbool ob) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

theorem notbool_idem2 (b : Bool) :
    notbool (notbool (of_bool b)) = of_bool b := by
  cases b <;> rfl

theorem notbool_idem3 (x : val) :
    notbool (notbool (notbool x)) = notbool x := by
  cases x <;> simp [notbool]
  case Vint i => cases (i == CompCert.Int.zero) <;> rfl
  case Vptr b ofs => rfl

theorem notbool_idem4 (ob : Option Bool) :
    notbool (notbool (of_optbool ob)) = of_optbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

/- ** Properties of integer addition -/

theorem add_commut (x y : val) :
    add x y = add y x := by
  cases x <;> cases y <;> simp [add]; try rfl
  case Vint.Vint i j => exact CompCert.Int.add_commut i j

theorem add_assoc (x y z : val) :
    add (add x y) z = add x (add y z) := by
  rcases hp : Archi.ptr64 with _ | _ <;>
  cases x <;> cases y <;> cases z <;>
    simp only [add, hp, if_true, if_false, Bool.false_eq_true]
  -- All remaining goals are val constructor equalities, use congr 1 once
  all_goals (try (congr 1))
  -- Now handle the Ptrofs arithmetic
  all_goals (
    first
    | exact CompCert.Int.add_assoc _ _ _
    | (rw [Ptrofs.of_int_add hp, Ptrofs.add_assoc])
    | (rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.of_int _) (Ptrofs.of_int _)])
  )
  -- Handle remaining goal (if any)
  all_goals (congr 1; rw [Ptrofs.add_commut])

theorem add_permut (x y z : val) :
    add x (add y z) = add y (add x z) := by
  rw [← add_assoc, add_commut x y, add_assoc]

theorem add_permut_4 (x y z t : val) :
    add (add x y) (add z t) = add (add x z) (add y t) := by
  rw [add_assoc, add_permut y z, ← add_assoc, ← add_assoc]

theorem neg_zero :
    neg Vzero = Vzero := by
  rfl

theorem neg_add_distr (x y : val) :
    neg (add x y) = add (neg x) (neg y) := by
  cases x <;> cases y <;> simp only [neg, add]
  case Vint.Vint i j =>
    congr 1
    exact CompCert.Int.neg_add_distr i j
  -- All other cases are either Vundef = Vundef directly, or involve pointer arithmetic
  -- Pointer cases: split on Archi.ptr64
  case Vptr.Vint b o j =>
    by_cases h : Archi.ptr64
    · simp [h]
    · simp [h]
  case Vint.Vptr i b o =>
    by_cases h : Archi.ptr64
    · simp [h]
    · simp [h]

theorem sub_zero_r (x : val) :
    sub Vzero x = neg x := by
  cases x <;> simp [sub, neg, Vzero]
  case Vint n =>
    -- Need: CompCert.Int.sub CompCert.Int.zero n = CompCert.Int.neg n
    rw [CompCert.Int.sub_add_opp]
    -- Now: CompCert.Int.zero + CompCert.Int.neg n = CompCert.Int.neg n
    -- Use extensionality and compute at the UInt32 level
    ext
    simp [CompCert.Int.neg, CompCert.Int.zero]

theorem sub_add_opp (x : val) (y : CompCert.Int) :
    sub x (.Vint y) = add x (.Vint (CompCert.Int.neg y)) := by
  cases x <;> simp [sub, add] <;> try rfl
  case Vint i => exact CompCert.Int.sub_add_opp i y
  case Vptr b ofs =>
    split <;> simp
    case isFalse h =>
      -- ptr64 = false: Ptrofs.sub ofs (of_int y) = Ptrofs.add ofs (of_int (neg y))
      rw [Ptrofs.sub_add_opp, Ptrofs.of_int_neg (by simpa using h)]

theorem sub_opp_add (x : val) (y : CompCert.Int) :
    sub x (.Vint (CompCert.Int.neg y)) = add x (.Vint y) := by
  rw [sub_add_opp, CompCert.Int.neg_involutive]

theorem sub_add_l (v1 v2 : val) (i : CompCert.Int) :
    sub (add v1 (.Vint i)) v2 = add (sub v1 v2) (.Vint i) := by
  cases v1 <;> cases v2
  all_goals (first | rfl | skip)
  case Vint.Vint a b =>
    simp only [add, sub]
    congr 1
    exact CompCert.Int.sub_add_l a b i
  case Vptr.Vint b1 o1 c =>
    simp only [add, sub]
    by_cases hp : Archi.ptr64
    · simp [hp]
    · have hpf : Archi.ptr64 = false := by simp at hp; exact hp
      simp only [hpf, if_false, Bool.false_eq_true]
      congr 1
      exact Ptrofs.sub_add_l o1 (Ptrofs.of_int c) i.signed
  case Vptr.Vptr b1 o1 b2 o2 =>
    simp only [add, sub]
    by_cases hp : Archi.ptr64
    · simp [hp]
    · have hpf : Archi.ptr64 = false := by simp at hp; exact hp
      simp only [hpf, if_false, Bool.false_eq_true]
      by_cases hb : b1 == b2
      · simp [hb]
        show Ptrofs.to_int (Ptrofs.sub (Ptrofs.add o1 (Ptrofs.of_int i)) o2) =
             CompCert.Int.add (Ptrofs.to_int (Ptrofs.sub o1 o2)) i
        simp only [Ptrofs.of_int]
        rw [Ptrofs.sub_add_l o1 o2 i.signed]
        exact Ptrofs.to_int_add_of_int (Ptrofs.sub o1 o2) i
      · simp [hb]
  all_goals simp only [add, sub]
  all_goals (first | rfl | (by_cases hp : Archi.ptr64 <;> simp [hp]))

theorem sub_add_r (v1 v2 : val) (i : CompCert.Int) :
    sub v1 (add v2 (.Vint i)) = add (sub v1 v2) (.Vint (CompCert.Int.neg i)) := by
  cases v1 <;> cases v2
  all_goals (first | rfl | skip)
  case Vint.Vint a b =>
    simp only [add, sub]
    congr 1
    exact CompCert.Int.sub_add_r a b i
  case Vint.Vptr a b2 o2 =>
    simp only [add, sub]
    by_cases hp : Archi.ptr64 <;> simp [hp]
  case Vptr.Vint b1 o1 c =>
    simp only [add, sub]
    by_cases hp : Archi.ptr64
    · simp [hp]
    · have hpf : Archi.ptr64 = false := by simp at hp; exact hp
      simp only [hpf, if_false, Bool.false_eq_true]
      rw [Ptrofs.of_int_add hpf c i]
      congr 1
      simp only [Ptrofs.of_int]
      rw [Ptrofs.sub_add_r o1 (Ptrofs.repr c.signed) i.signed]
      congr 1
      rw [Ptrofs.repr_eq_iff]
      simp only [Ptrofs.modulus_eq_pow32 hpf]
      exact (CompCert.Int.neg_signed_mod i).symm
  case Vptr.Vptr b1 o1 b2 o2 =>
    simp only [add, sub]
    by_cases hp : Archi.ptr64
    · simp [hp]
    · have hpf : Archi.ptr64 = false := by simp at hp; exact hp
      simp only [hpf, if_false, Bool.false_eq_true]
      by_cases hb : b1 == b2
      · simp [hb]
        show Ptrofs.to_int (Ptrofs.sub o1 (Ptrofs.add o2 (Ptrofs.of_int i))) =
             CompCert.Int.add (Ptrofs.to_int (Ptrofs.sub o1 o2)) (CompCert.Int.neg i)
        simp only [Ptrofs.of_int]
        rw [Ptrofs.sub_add_r o1 o2 i.signed]
        have : Ptrofs.repr (-i.signed) = Ptrofs.repr (CompCert.Int.neg i).signed := by
          rw [Ptrofs.repr_eq_iff]
          simp only [Ptrofs.modulus_eq_pow32 hpf]
          exact (CompCert.Int.neg_signed_mod i).symm
        rw [this]
        rw [← show Ptrofs.of_int (CompCert.Int.neg i) = Ptrofs.repr (CompCert.Int.neg i).signed from rfl]
        rw [Ptrofs.to_int_add_of_int]
        rfl
      · simp [hb]

/- ** Properties of integer multiplication -/

theorem mul_commut (x y : val) :
    mul x y = mul y x := by
  cases x <;> cases y <;> simp [mul]; try rfl
  case Vint.Vint i j =>
    show CompCert.Int.mul i j = CompCert.Int.mul j i
    exact CompCert.Int.mul_commut i j

theorem mul_assoc (x y z : val) :
    mul (mul x y) z = mul x (mul y z) := by
  cases x <;> cases y <;> cases z <;> simp [mul]; try rfl
  case Vint.Vint.Vint i j k =>
    show CompCert.Int.mul (CompCert.Int.mul i j) k = CompCert.Int.mul i (CompCert.Int.mul j k)
    exact CompCert.Int.mul_assoc i j k

theorem mul_add_distr_l (x y z : val) :
    mul (add x y) z = add (mul x z) (mul y z) := by
  cases x <;> cases y <;> cases z <;> simp [add, mul]
  all_goals (try (split_ifs <;> rfl))
  case Vint.Vint.Vint =>
    exact CompCert.Int.mul_add_distr_l _ _ _

theorem mul_add_distr_r (x y z : val) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  cases x <;> cases y <;> cases z <;> simp [add, mul]
  all_goals (try (split_ifs <;> rfl))
  case Vint.Vint.Vint =>
    exact CompCert.Int.mul_add_distr_r _ _ _

theorem mul_pow2 (x : val) (n logn : CompCert.Int)
    (H : CompCert.Int.is_power2 n = some logn) :
    mul x (.Vint n) = shl x (.Vint logn) := by
  have ⟨hn_eq, hlogn_lt⟩ := CompCert.Int.is_power2_pow n logn H
  cases x
  all_goals (unfold mul shl; simp)
  case Vint i =>
    -- Goal: Vint (Int.mul i n) = if ltu logn iwordsize then Vint (Int.shl i logn) else Vundef
    have h_ltu : CompCert.Int.ltu logn CompCert.Int.iwordsize = true := by
      unfold CompCert.Int.ltu CompCert.Int.iwordsize
      simp only [decide_eq_true_eq]
      exact hlogn_lt
    rw [if_pos h_ltu]
    congr 1
    have : CompCert.Int.mul i n = CompCert.Int.mul i (CompCert.Int.shl CompCert.Int.one logn) := by
      rw [← hn_eq]
    rw [this]
    exact CompCert.Int.mul_pow2_shl i logn h_ltu

/- ** Properties of integer division and modulus -/

theorem mods_divs (x y z : val)
    (H : mods x y = some z) :
    ∃ v, divs x y = some v ∧ z = sub x (mul v y) := by
  -- Only Vint, Vint with guard-false produces `some`
  cases x <;> cases y <;> simp only [mods] at H <;> try contradiction
  -- Now x = Vint n1, y = Vint n2
  rename_i n1 n2
  -- Split the guard
  split at H
  · contradiction  -- guard true ⇒ none = some z
  · -- guard false. H : some (Vint (mods n1 n2)) = some z
    rename_i hguard   -- hguard : ¬(n2 == zero || ...)
    -- Extract z = Vint (mods n1 n2)
    injection H with H
    -- Extract n2 ≠ zero from guard
    -- hguard is: ¬((n2 == zero) || (n1 == min_signed && n2 == mone)) = true
    -- which simplifies to: (n2 == zero) = false ∧ ...
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hguard
    have hy : n2 ≠ CompCert.Int.zero := by
      intro h
      subst h
      simp [CompCert.Int.zero] at hguard
    refine ⟨.Vint (CompCert.Int.divs n1 n2), ?_, ?_⟩
    · -- divs x y = some (Vint (divs n1 n2)): same guard is false
      simp only [divs]
      -- The guard is the same, so use hguard to rewrite
      have : ¬(n2 == CompCert.Int.zero
               || (n1 == CompCert.Int.repr CompCert.Int.min_signed && n2 == CompCert.Int.mone)) := by
        simp only [Bool.or_eq_true, Bool.and_eq_true]
        exact hguard
      rw [if_neg this]
    · -- z = sub (Vint n1) (mul (Vint (divs n1 n2)) (Vint n2))
      rw [← H]
      simp only [sub, mul]
      congr 1
      exact CompCert.Int.mods_divs_identity n1 n2 hy

theorem modu_divu (x y z : val)
    (H : modu x y = some z) :
    ∃ v, divu x y = some v ∧ z = sub x (mul v y) := by
  -- Only Vint, Vint with guard-false produces `some`
  cases x <;> cases y <;> simp only [modu] at H <;> try contradiction
  -- Now x = Vint n1, y = Vint n2
  rename_i n1 n2
  -- Split the guard
  split at H
  · contradiction  -- guard true ⇒ none = some z
  · -- guard false. H : some (Vint (modu n1 n2)) = some z
    rename_i hguard   -- hguard : ¬(n2 == zero)
    -- Extract z = Vint (modu n1 n2)
    injection H with H
    -- Extract n2 ≠ zero from guard
    have hy : n2 ≠ CompCert.Int.zero := by
      intro h
      subst h
      simp [CompCert.Int.zero] at hguard
    refine ⟨.Vint (CompCert.Int.divu n1 n2), ?_, ?_⟩
    · -- divu x y = some (Vint (divu n1 n2)): same guard is false
      simp only [divu]
      rw [if_neg hguard]
    · -- z = sub (Vint n1) (mul (Vint (divu n1 n2)) (Vint n2))
      rw [← H]
      simp only [sub, mul]
      congr 1
      exact CompCert.Int.modu_divu_identity n1 n2 hy

theorem modls_divls (x y z : val)
    (H : modls x y = some z) :
    ∃ v, divls x y = some v ∧ z = subl x (mull v y) := by
  -- Only Vlong, Vlong with guard-false produces `some`
  cases x <;> cases y <;> simp only [modls] at H <;> try contradiction
  -- Now x = Vlong n1, y = Vlong n2
  rename_i n1 n2
  -- Split the guard
  split at H
  · contradiction  -- guard true ⇒ none = some z
  · -- guard false. H : some (Vlong (mods n1 n2)) = some z
    rename_i hguard   -- hguard : ¬(n2 == zero || ...)
    -- Extract z = Vlong (mods n1 n2)
    injection H with H
    -- Extract n2 ≠ zero from guard
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hguard
    have hy : n2 ≠ CompCert.Int64.zero := by
      intro h
      subst h
      simp [CompCert.Int64.zero] at hguard
    refine ⟨.Vlong (CompCert.Int64.divs n1 n2), ?_, ?_⟩
    · -- divls x y = some (Vlong (divs n1 n2)): same guard is false
      simp only [divls]
      have : ¬(n2 == CompCert.Int64.zero
               || (n1 == CompCert.Int64.repr CompCert.Int64.min_signed && n2 == CompCert.Int64.mone)) := by
        simp only [Bool.or_eq_true, Bool.and_eq_true]
        exact hguard
      rw [if_neg this]
    · -- z = subl (Vlong n1) (mull (Vlong (divs n1 n2)) (Vlong n2))
      rw [← H]
      simp only [subl, mull]
      congr 1
      exact CompCert.Int64.mods_divs_identity n1 n2 hy

theorem modlu_divlu (x y z : val)
    (H : modlu x y = some z) :
    ∃ v, divlu x y = some v ∧ z = subl x (mull v y) := by
  -- Only Vlong, Vlong with guard-false produces `some`
  cases x <;> cases y <;> simp only [modlu] at H <;> try contradiction
  -- Now x = Vlong n1, y = Vlong n2
  rename_i n1 n2
  -- Split the guard
  split at H
  · contradiction  -- guard true ⇒ none = some z
  · -- guard false. H : some (Vlong (modu n1 n2)) = some z
    rename_i hguard   -- hguard : ¬(n2 == zero)
    -- Extract z = Vlong (modu n1 n2)
    injection H with H
    -- Extract n2 ≠ zero from guard
    have hy : n2 ≠ CompCert.Int64.zero := by
      intro h
      subst h
      simp [CompCert.Int64.zero] at hguard
    refine ⟨.Vlong (CompCert.Int64.divu n1 n2), ?_, ?_⟩
    · -- divlu x y = some (Vlong (divu n1 n2)): same guard is false
      simp only [divlu]
      rw [if_neg hguard]
    · -- z = subl (Vlong n1) (mull (Vlong (divu n1 n2)) (Vlong n2))
      rw [← H]
      simp only [subl, mull]
      congr 1
      exact CompCert.Int64.modu_divu_identity n1 n2 hy

theorem divs_pow2 (x y : val) (n logn : CompCert.Int)
    (H1 : CompCert.Int.is_power2 n = some logn)
    (H2 : CompCert.Int.ltu logn (CompCert.Int.repr 31) = true)
    (H3 : divs x (.Vint n) = some y) :
    shrx x (.Vint logn) = some y := by
  -- From H3, x must be Vint and the guard must be false
  cases x with
  | Vundef | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ =>
    unfold divs at H3; contradiction
  | Vint i =>
    unfold divs at H3
    by_cases hguard : n == CompCert.Int.zero || (i == CompCert.Int.repr CompCert.Int.min_signed && n == CompCert.Int.mone)
    · simp [hguard] at H3
    · simp [hguard] at H3
      -- H3 : some (Vint (CompCert.Int.divs i n)) = some y
      cases H3
      -- y = Vint (CompCert.Int.divs i n)
      -- Goal: shrx (Vint i) (Vint logn) = some (Vint (CompCert.Int.divs i n))
      unfold shrx
      -- From H2: ltu logn (repr 31) = true
      simp only [H2, ite_true]
      -- Goal: some (Vint (CompCert.Int.shrx i logn)) = some (Vint (CompCert.Int.divs i n))
      congr 2
      -- Use the Int-level lemma
      have hlogn_lt : logn.toNat < 31 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at H2
        have h31 : (UInt32.ofInt 31).toNat = 31 := by rfl
        simp at H2
        exact H2
      have := CompCert.Int.divs_pow2_eq i n logn H1 hlogn_lt
      exact this.symm

theorem divs_one (s : CompCert.Int) :
    divs (.Vint s) (.Vint CompCert.Int.one) = some (.Vint s) := by
  simp only [divs]
  have h1 : ¬(CompCert.Int.one == CompCert.Int.zero) := by decide
  have h2 : ¬(CompCert.Int.one == CompCert.Int.mone) := by decide
  simp [h1, h2, CompCert.Int.divs_one]

theorem divu_pow2 (x y : val) (n logn : CompCert.Int)
    (H1 : CompCert.Int.is_power2 n = some logn)
    (H2 : divu x (.Vint n) = some y) :
    shru x (.Vint logn) = y := by
  -- From H2, x must be Vint and n ≠ 0
  cases x with
  | Vundef | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ =>
    unfold divu at H2; contradiction
  | Vint i =>
    unfold divu at H2
    by_cases hn : n == CompCert.Int.zero
    · simp [hn] at H2
    · simp [hn] at H2
      subst H2
      -- Goal: shru (Vint i) (Vint logn) = Vint (Int.divu i n)
      have ⟨hn_eq, hlogn_lt⟩ := CompCert.Int.is_power2_pow n logn H1
      simp only [shru]
      have h_ltu : CompCert.Int.ltu logn CompCert.Int.iwordsize = true := by
        unfold CompCert.Int.ltu CompCert.Int.iwordsize
        simp only [decide_eq_true_eq]
        exact hlogn_lt
      rw [if_pos h_ltu]
      congr 1
      exact (CompCert.Int.divu_pow2 i n logn H1).symm

theorem divu_one (s : CompCert.Int) :
    divu (.Vint s) (.Vint CompCert.Int.one) = some (.Vint s) := by
  simp [divu]
  constructor
  · -- one ≠ zero
    decide
  · -- divu s one = s
    exact CompCert.Int.divu_one s

theorem modu_pow2 (x : val) (n logn : CompCert.Int) (y : val)
    (H1 : CompCert.Int.is_power2 n = some logn)
    (H2 : modu x (.Vint n) = some y) :
    and x (.Vint (CompCert.Int.sub n CompCert.Int.one)) = y := by
  -- From H2, x must be Vint and n ≠ 0
  cases x with
  | Vundef | Vlong _ | Vfloat _ | Vsingle _ | Vptr _ _ =>
    unfold modu at H2; contradiction
  | Vint i =>
    unfold modu at H2
    by_cases hn : n == CompCert.Int.zero
    · simp [hn] at H2
    · simp [hn] at H2
      subst H2
      -- Goal: and (Vint i) (Vint (sub n one)) = Vint (Int.modu i n)
      simp only [and]
      congr 1
      exact (CompCert.Int.modu_pow2 i n logn H1).symm

/- ** Properties of bitwise operations -/

theorem and_commut (x y : val) :
    and x y = and y x := by
  cases x <;> cases y <;> simp [and]; try rfl
  case Vint.Vint => rw [CompCert.Int.and_commut]

theorem and_assoc (x y z : val) :
    and (and x y) z = and x (and y z) := by
  cases x <;> cases y <;> cases z <;> simp [and]; try rfl
  case Vint.Vint.Vint => rw [CompCert.Int.and_assoc]

theorem or_commut (x y : val) :
    or x y = or y x := by
  cases x <;> cases y <;> simp [or]; try rfl
  case Vint.Vint => rw [CompCert.Int.or_commut]

theorem or_assoc (x y z : val) :
    or (or x y) z = or x (or y z) := by
  cases x <;> cases y <;> cases z <;> simp [or]; try rfl
  case Vint.Vint.Vint => rw [CompCert.Int.or_assoc]

theorem xor_commut (x y : val) :
    xor x y = xor y x := by
  cases x <;> cases y <;> simp [xor]; try rfl
  case Vint.Vint => rw [CompCert.Int.xor_commut]

theorem xor_assoc (x y z : val) :
    xor (xor x y) z = xor x (xor y z) := by
  cases x <;> cases y <;> cases z <;> simp [xor]; try rfl
  case Vint.Vint.Vint => rw [CompCert.Int.xor_assoc]

theorem not_xor (x : val) :
    notint x = xor x (.Vint CompCert.Int.mone) := by
  cases x <;> simp [notint, xor, CompCert.Int.not]

/- ** Properties of shifts and rotations -/

theorem shl_mul (x y : val) :
    mul x (shl Vone y) = shl x y := by
  cases x <;> cases y <;> (try rfl)
  -- Only Vint/Vint case remains
  rename_i i j
  simp only [mul, shl, Vone]
  by_cases H : CompCert.Int.ltu j CompCert.Int.iwordsize = true
  · simp [H]; exact CompCert.Int.mul_pow2_shl i j H
  · simp [H]

theorem shl_rolm (x : val) (n : CompCert.Int)
    (H : CompCert.Int.ltu n CompCert.Int.iwordsize = true) :
    shl x (.Vint n) = rolm x n (CompCert.Int.shl CompCert.Int.mone n) := by
  cases x <;> (try rfl)
  rename_i i
  simp only [shl, rolm, H, if_true]
  congr 1
  exact CompCert.Int.shl_rolm i n H

theorem shll_rolml (x : val) (n : CompCert.Int)
    (H : CompCert.Int.ltu n CompCert.Int64.iwordsize' = true) :
    shll x (.Vint n) = rolml x n (CompCert.Int64.shl CompCert.Int64.mone (CompCert.Int64.repr (CompCert.Int.unsigned n))) := by
  cases x <;> (try rfl)
  rename_i i
  simp only [shll, rolml, H, if_true]
  congr 1
  exact CompCert.Int64.shl'_rolm i n H

theorem shru_rolm (x : val) (n : CompCert.Int)
    (H : CompCert.Int.ltu n CompCert.Int.iwordsize = true) :
    shru x (.Vint n) = rolm x (CompCert.Int.sub CompCert.Int.iwordsize n) (CompCert.Int.shru CompCert.Int.mone n) := by
  cases x <;> (try rfl)
  rename_i i
  simp only [shru, rolm, H, if_true]
  congr 1
  exact CompCert.Int.shru_rolm i n H

theorem shrlu_rolml (x : val) (n : CompCert.Int)
    (H : CompCert.Int.ltu n CompCert.Int64.iwordsize' = true) :
    shrlu x (.Vint n) = rolml x (CompCert.Int.sub CompCert.Int64.iwordsize' n) (CompCert.Int64.shru CompCert.Int64.mone (CompCert.Int64.repr (CompCert.Int.unsigned n))) := by
  cases x <;> (try rfl)
  rename_i i
  simp only [shrlu, rolml, H, if_true]
  congr 1
  exact CompCert.Int64.shru'_rolm i n H


theorem shrx_carry (x y z : val)
    (H : shrx x y = some z) :
    add (shr x y) (shr_carry x y) = z := by
  -- From shrx x y = some z, extract n1, n2
  unfold shrx at H
  cases x <;> cases y <;> simp at H; try contradiction
  case Vint.Vint n1 n2 =>
    -- After simp, H is an if-then-else
    by_cases hltu : CompCert.Int.ltu n2 (CompCert.Int.repr 31)
    · -- ltu n2 (repr 31) = true
      simp [hltu] at H
      rw [← H]
      -- Goal: add (shr (val.Vint n1) (val.Vint n2)) (shr_carry (val.Vint n1) (val.Vint n2)) = val.Vint (CompCert.Int.shrx n1 n2)
      unfold add shr shr_carry
      simp only []
      -- Need to show the ltu guards pass
      have hbound : n2.toNat < 31 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at hltu
        have : (UInt32.ofInt 31).toNat = 31 := by rfl
        simp at hltu
        exact hltu
      have hltu_iws : CompCert.Int.ltu n2 CompCert.Int.iwordsize = true := by
        unfold CompCert.Int.ltu CompCert.Int.iwordsize
        have : (32 : UInt32).toNat = 32 := by rfl
        simp
        show n2.toNat < 32
        omega
      simp [hltu_iws]
      -- Apply the Int-level theorem
      exact CompCert.Int.shrx_carry_eq n1 n2 hbound
    · -- ltu n2 (repr 31) = false, contradiction
      simp [hltu] at H

theorem shrx_shr (x y z : val)
    (H : shrx x y = some z) :
    ∃ p q,
      x = .Vint p ∧ y = .Vint q ∧
      z = shr (if CompCert.Int.lt p CompCert.Int.zero then add x (.Vint (CompCert.Int.sub (CompCert.Int.shl CompCert.Int.one q) CompCert.Int.one)) else x) (.Vint q) := by
  -- From shrx x y = some z, extract that x = Vint p, y = Vint q
  unfold shrx at H
  cases x <;> cases y <;> simp at H; try contradiction
  case Vint.Vint p q =>
    -- H : if ltu q (repr 31) then some (Vint (Int.shrx p q)) else none = some z
    by_cases hltu : CompCert.Int.ltu q (CompCert.Int.repr 31)
    · -- ltu holds, so z = Vint (Int.shrx p q)
      simp [hltu] at H
      subst H
      refine ⟨p, q, rfl, rfl, ?_⟩
      have hb : q.toNat < 31 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at hltu
        have h31 : (UInt32.ofInt 31).toNat = 31 := by rfl
        simp at hltu; exact hltu
      have hltu_iws : CompCert.Int.ltu q CompCert.Int.iwordsize = true := by
        unfold CompCert.Int.ltu CompCert.Int.iwordsize
        have : (32 : UInt32).toNat = 32 := by rfl
        simp; show q.toNat < 32; omega
      -- lt p zero ↔ p.signed < 0
      have hlt_eq : CompCert.Int.lt p CompCert.Int.zero = decide (p.signed < 0) := by
        unfold CompCert.Int.lt CompCert.Int.zero
        have hz : CompCert.Int.signed 0 = 0 := by decide
        simp [hz]
      by_cases hp : CompCert.Int.signed p < 0
      · -- p < 0: use the Int-level shrx_shr_neg_eq
        rw [hlt_eq]
        simp only [hp, decide_true, if_true]
        rw [CompCert.Int.shrx_shr_neg_eq p q hp hb]
        -- Goal: Vint (Int.shr (Int.add p mask) q) = shr (add (Vint p) (Vint mask)) (Vint q)
        simp only [add, shr, hltu_iws, if_true]
      · -- p >= 0: shrx p q = shr p q
        rw [hlt_eq]
        simp only [hp, decide_false]
        show val.Vint (CompCert.Int.shrx p q) = shr (val.Vint p) (val.Vint q)
        rw [show shr (val.Vint p) (val.Vint q) = val.Vint (CompCert.Int.shr p q) by
          simp only [shr]; rw [if_pos hltu_iws]]
        congr 1
        unfold CompCert.Int.shrx CompCert.Int.shr
        have hq32 : q.toNat % 32 = q.toNat := Nat.mod_eq_of_lt (by omega)
        simp [show CompCert.Int.signed p ≥ 0 by omega, hq32]
    · -- ltu doesn't hold, contradiction
      simp [hltu] at H

theorem shrx_shr_2 (n : CompCert.Int) (x z : val)
    (H : shrx x (.Vint n) = some z) :
    z = (if CompCert.Int.eq n CompCert.Int.zero then x else
         shr (add x (shru (shr x (.Vint (CompCert.Int.repr 31)))
                    (.Vint (CompCert.Int.sub (CompCert.Int.repr 32) n))))
             (.Vint n)) := by
  -- Extract that x = Vint p
  unfold shrx at H
  cases x <;> simp at H; try contradiction
  case Vint p =>
    by_cases hltu : CompCert.Int.ltu n (CompCert.Int.repr 31)
    · -- n < 31, so z = Vint (shrx p n)
      simp [hltu] at H
      subst H
      have hbound : n.toNat < 31 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at hltu
        have h31 : (UInt32.ofInt 31).toNat = 31 := by rfl
        simp at hltu; exact hltu
      -- Int-level characterization
      rw [CompCert.Int.shrx_shr_2_eq p n hbound]
      by_cases hn : CompCert.Int.eq n CompCert.Int.zero
      · simp only [hn, if_true]
      · simp only [hn]
        have hn0 : n.toNat ≠ 0 := by
          intro h
          apply hn
          unfold CompCert.Int.eq CompCert.Int.zero
          have : n = 0 := by apply UInt32.toNat.inj; simpa using h
          simp [this]
        -- push the val ops through Vint; discharge all shift guards
        have h31lt : CompCert.Int.ltu (CompCert.Int.repr 31) CompCert.Int.iwordsize = true := by
          unfold CompCert.Int.ltu CompCert.Int.iwordsize CompCert.Int.repr
          decide
        have hsub_lt : CompCert.Int.ltu (CompCert.Int.sub (CompCert.Int.repr 32) n) CompCert.Int.iwordsize = true := by
          unfold CompCert.Int.ltu CompCert.Int.iwordsize
          have hb : (32 : UInt32).toNat = 32 := by rfl
          simp only [decide_eq_true_eq]
          show (CompCert.Int.sub (CompCert.Int.repr 32) n).toNat < 32
          rw [show (CompCert.Int.sub (CompCert.Int.repr 32) n) = (UInt32.ofInt 32) - n from rfl,
              UInt32.toNat_sub]
          have h32 : (UInt32.ofInt 32).toNat = 32 := by rfl
          have hnlt : n.toNat < 2^32 := n.toBitVec.isLt
          rw [h32]
          have hpow : (2:Nat)^32 = 4294967296 := by norm_num
          rw [hpow] at *
          have hmod : (4294967296 - n.toNat + 32) % 4294967296 = 32 - n.toNat := by omega
          rw [hmod]; omega
        have hnlt_iws : CompCert.Int.ltu n CompCert.Int.iwordsize = true := by
          unfold CompCert.Int.ltu CompCert.Int.iwordsize
          have hb : (32 : UInt32).toNat = 32 := by rfl
          simp only [decide_eq_true_eq]; show n.toNat < 32; omega
        have heqf : CompCert.Int.eq n CompCert.Int.zero = false := by
          unfold CompCert.Int.eq CompCert.Int.zero
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h; apply hn0; rw [h]; rfl
        simp only [shr, shru, add, hnlt_iws, h31lt, hsub_lt, if_true, Bool.false_eq_true,
          if_false]
    · -- n >= 31, contradiction with H = some
      simp [hltu] at H

theorem or_rolm (x : val) (n m1 m2 : CompCert.Int) :
    or (rolm x n m1) (rolm x n m2) = rolm x n (CompCert.Int.or m1 m2) := by
  cases x <;> simp [rolm, or]
  case Vint i =>
    exact CompCert.Int.or_rolm i n m1 m2

theorem rolm_rolm (x : val) (n1 m1 n2 m2 : CompCert.Int) :
    rolm (rolm x n1 m1) n2 m2 =
      rolm x (CompCert.Int.modu (CompCert.Int.add n1 n2) CompCert.Int.iwordsize)
             (CompCert.Int.and (CompCert.Int.rol m1 n2) m2) := by
  cases x <;> simp [rolm]
  case Vint i =>
    exact CompCert.Int.rolm_rolm i n1 m1 n2 m2

theorem rolm_zero (x : val) (m : CompCert.Int) :
    rolm x CompCert.Int.zero m = and x (.Vint m) := by
  cases x <;> simp [rolm, and]
  case Vint i =>
    simp [CompCert.Int.rolm]
    rw [CompCert.Int.rol_zero]

/- ** Properties of 64-bit integer addition -/

theorem addl_commut (x y : val) :
    addl x y = addl y x := by
  cases x <;> cases y <;> simp [addl]; try rfl
  case Vlong.Vlong i j =>
    show CompCert.Int64.add i j = CompCert.Int64.add j i
    exact CompCert.Int64.add_commut i j

theorem addl_assoc (x y z : val) :
    addl (addl x y) z = addl x (addl y z) := by
  rcases hp : Archi.ptr64 with _ | _ <;>
  cases x <;> cases y <;> cases z <;>
    simp only [addl, hp, if_true, if_false, Bool.false_eq_true]
  -- All remaining goals are val constructor equalities, use congr 1 once
  all_goals (try (congr 1))
  -- Now handle the Ptrofs arithmetic
  all_goals (
    first
    | exact CompCert.Int64.add_assoc _ _ _
    | (rw [Ptrofs.of_int64_add hp, Ptrofs.add_assoc])
    | (rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.of_int64 _) (Ptrofs.of_int64 _)])
  )
  -- Handle remaining goal (if any)
  all_goals (congr 1; rw [Ptrofs.add_commut])

theorem addl_permut (x y z : val) :
    addl x (addl y z) = addl y (addl x z) := by
  rw [← addl_assoc, addl_commut x y, addl_assoc]

theorem addl_permut_4 (x y z t : val) :
    addl (addl x y) (addl z t) = addl (addl x z) (addl y t) := by
  rw [addl_assoc, addl_permut y z, ← addl_assoc, ← addl_assoc]

theorem negl_addl_distr (x y : val) :
    negl (addl x y) = addl (negl x) (negl y) := by
  cases x <;> cases y <;> simp only [negl, addl]
  case Vlong.Vlong i j =>
    congr 1
    exact CompCert.Int64.neg_add_distr i j
  -- All other cases are either Vundef = Vundef directly, or involve pointer arithmetic
  -- Pointer cases: split on Archi.ptr64
  case Vptr.Vlong b o j =>
    by_cases h : Archi.ptr64
    · simp [h]
    · simp [h]
  case Vlong.Vptr i b o =>
    by_cases h : Archi.ptr64
    · simp [h]
    · simp [h]

theorem subl_addl_opp (x : val) (y : CompCert.Int64) :
    subl x (.Vlong y) = addl x (.Vlong (CompCert.Int64.neg y)) := by
  cases x <;> simp [subl, addl] <;> try rfl
  case Vlong i => exact CompCert.Int64.sub_add_opp i y
  case Vptr b ofs =>
    split <;> simp
    case isTrue h =>
      rw [Ptrofs.sub_add_opp, Ptrofs.of_int64_neg h]

theorem subl_opp_addl (x : val) (y : CompCert.Int64) :
    subl x (.Vlong (CompCert.Int64.neg y)) = addl x (.Vlong y) := by
  rw [subl_addl_opp, CompCert.Int64.neg_involutive]

theorem subl_addl_l (v1 v2 : val) (i : CompCert.Int64) :
    subl (addl v1 (.Vlong i)) v2 = addl (subl v1 v2) (.Vlong i) := by
  cases v1 <;> cases v2
  all_goals (first | rfl | skip)
  case Vlong.Vlong a b =>
    simp only [addl, subl]
    congr 1
    exact CompCert.Int64.sub_add_l a b i
  case Vptr.Vlong b1 o1 c =>
    simp only [addl, subl]
    by_cases hp : Archi.ptr64
    · simp [hp]
      show Ptrofs.sub (Ptrofs.add o1 (Ptrofs.of_int64 i)) (Ptrofs.of_int64 c) =
           Ptrofs.add (Ptrofs.of_int64 i) (Ptrofs.sub o1 (Ptrofs.of_int64 c))
      simp only [Ptrofs.of_int64]
      rw [Ptrofs.sub_add_l o1 (Ptrofs.repr c.signed) i.signed]
      rw [Ptrofs.add_commut]
    · simp [hp]
  case Vptr.Vptr b1 o1 b2 o2 =>
    simp only [addl, subl]
    by_cases hp : Archi.ptr64 = true
    · by_cases hb : (b1 == b2) = true
      · simp only [hp, hb, Bool.not_true, Bool.false_eq_true, if_true, if_false]
        congr 1
        simp only [Ptrofs.of_int64]
        rw [Ptrofs.sub_add_l o1 o2 i.signed]
        exact Ptrofs.to_int64_add_of_int64 hp (Ptrofs.sub o1 o2) i
      · simp only [Bool.not_eq_true] at hb
        simp [hp, hb]
    · simp only [Bool.not_eq_true] at hp
      simp [hp]
  all_goals simp only [addl, subl]
  all_goals (first | rfl | (by_cases hp : Archi.ptr64 <;> simp [hp]))

theorem subl_addl_r (v1 v2 : val) (i : CompCert.Int64) :
    subl v1 (addl v2 (.Vlong i)) = addl (subl v1 v2) (.Vlong (CompCert.Int64.neg i)) := by
  cases v1 <;> cases v2
  all_goals (first | rfl | skip)
  case Vlong.Vlong a b =>
    simp only [addl, subl]
    congr 1
    exact CompCert.Int64.sub_add_r a b i
  case Vlong.Vptr a b2 o2 =>
    simp only [addl, subl]
    by_cases hp : Archi.ptr64 <;> simp [hp]
  case Vptr.Vlong b1 o1 c =>
    simp only [addl, subl]
    by_cases hp : Archi.ptr64
    · simp [hp]
      rw [Ptrofs.of_int64_add hp c i]
      simp only [Ptrofs.of_int64]
      rw [Ptrofs.sub_add_r o1 (Ptrofs.repr c.signed) i.signed]
      congr 1
      rw [Ptrofs.repr_eq_iff]
      simp only [Ptrofs.modulus_eq_pow64 hp]
      exact (CompCert.Int64.neg_signed_mod i).symm
    · simp [hp]
  case Vptr.Vptr b1 o1 b2 o2 =>
    simp only [addl, subl]
    by_cases hp : Archi.ptr64 = true
    · by_cases hb : (b1 == b2) = true
      · simp only [hp, hb, Bool.not_true, Bool.false_eq_true, if_true, if_false]
        congr 1
        simp only [Ptrofs.of_int64]
        rw [Ptrofs.sub_add_r o1 o2 i.signed]
        have hneg : Ptrofs.repr (-i.signed) = Ptrofs.repr (CompCert.Int64.neg i).signed := by
          rw [Ptrofs.repr_eq_iff]
          simp only [Ptrofs.modulus_eq_pow64 hp]
          exact (CompCert.Int64.neg_signed_mod i).symm
        rw [hneg]
        rw [← show Ptrofs.of_int64 (CompCert.Int64.neg i)
              = Ptrofs.repr (CompCert.Int64.neg i).signed from rfl]
        exact Ptrofs.to_int64_add_of_int64 hp (Ptrofs.sub o1 o2) (CompCert.Int64.neg i)
      · simp only [Bool.not_eq_true] at hb
        simp [hp, hb]
    · simp only [Bool.not_eq_true] at hp
      simp [hp]

/- ** Properties of 64-bit integer multiplication -/

theorem mull_commut (x y : val) :
    mull x y = mull y x := by
  cases x <;> cases y <;> simp [mull]; try rfl
  case Vlong.Vlong i j =>
    show CompCert.Int64.mul i j = CompCert.Int64.mul j i
    exact CompCert.Int64.mul_commut i j

theorem mull_assoc (x y z : val) :
    mull (mull x y) z = mull x (mull y z) := by
  cases x <;> cases y <;> cases z <;> simp [mull]; try rfl
  case Vlong.Vlong.Vlong i j k =>
    show CompCert.Int64.mul (CompCert.Int64.mul i j) k = CompCert.Int64.mul i (CompCert.Int64.mul j k)
    exact CompCert.Int64.mul_assoc i j k

theorem mull_addl_distr_l (x y z : val) :
    mull (addl x y) z = addl (mull x z) (mull y z) := by
  cases x <;> cases y <;> cases z <;> simp [addl, mull]
  all_goals (try (split_ifs <;> rfl))
  case Vlong.Vlong.Vlong =>
    exact CompCert.Int64.mul_add_distr_l _ _ _

theorem mull_addl_distr_r (x y z : val) :
    mull x (addl y z) = addl (mull x y) (mull x z) := by
  cases x <;> cases y <;> cases z <;> simp [addl, mull]
  all_goals (try (split_ifs <;> rfl))
  case Vlong.Vlong.Vlong =>
    exact CompCert.Int64.mul_add_distr_r _ _ _

/- ** Properties of 64-bit bitwise operations -/

theorem andl_commut (x y : val) :
    andl x y = andl y x := by
  cases x <;> cases y <;> simp [andl]; try rfl
  case Vlong.Vlong => rw [CompCert.Int64.and_commut]

theorem andl_assoc (x y z : val) :
    andl (andl x y) z = andl x (andl y z) := by
  cases x <;> cases y <;> cases z <;> simp [andl]; try rfl
  case Vlong.Vlong.Vlong => rw [CompCert.Int64.and_assoc]

theorem orl_commut (x y : val) :
    orl x y = orl y x := by
  cases x <;> cases y <;> simp [orl]; try rfl
  case Vlong.Vlong => rw [CompCert.Int64.or_commut]

theorem orl_assoc (x y z : val) :
    orl (orl x y) z = orl x (orl y z) := by
  cases x <;> cases y <;> cases z <;> simp [orl]; try rfl
  case Vlong.Vlong.Vlong => rw [CompCert.Int64.or_assoc]

theorem xorl_commut (x y : val) :
    xorl x y = xorl y x := by
  cases x <;> cases y <;> simp [xorl]; try rfl
  case Vlong.Vlong => rw [CompCert.Int64.xor_commut]

theorem xorl_assoc (x y z : val) :
    xorl (xorl x y) z = xorl x (xorl y z) := by
  cases x <;> cases y <;> cases z <;> simp [xorl]; try rfl
  case Vlong.Vlong.Vlong => rw [CompCert.Int64.xor_assoc]

theorem notl_xorl (x : val) :
    notl x = xorl x (.Vlong CompCert.Int64.mone) := by
  cases x <;> simp [notl, xorl, CompCert.Int64.not]

/- ** Properties of 64-bit division and modulus -/

theorem divls_pow2 (x : val) (n : CompCert.Int64) (logn : CompCert.Int) (y : val)
    (H1 : CompCert.Int64.is_power2' n = some logn)
    (H2 : CompCert.Int.ltu logn (CompCert.Int.repr 63) = true)
    (H3 : divls x (.Vlong n) = some y) :
    shrxl x (.Vint logn) = some y := by
  -- Similar to divs_pow2
  cases x with
  | Vundef | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ =>
    unfold divls at H3; contradiction
  | Vlong i =>
    unfold divls at H3
    by_cases hguard : n == CompCert.Int64.zero || (i == CompCert.Int64.repr CompCert.Int64.min_signed && n == CompCert.Int64.mone)
    · simp [hguard] at H3
    · simp [hguard] at H3
      cases H3
      unfold shrxl
      simp only [H2, ite_true]
      congr 2
      have hlogn_lt : logn.toNat < 63 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at H2
        have h63 : (UInt32.ofInt 63).toNat = 63 := by rfl
        simp at H2
        exact H2
      have := CompCert.Int64.divs_pow2'_eq i n logn H1 hlogn_lt
      exact this.symm

theorem divls_one (n : CompCert.Int64) :
    divls (.Vlong n) (.Vlong CompCert.Int64.one) = some (.Vlong n) := by
  simp only [divls]
  have h1 : ¬(CompCert.Int64.one == CompCert.Int64.zero) := by decide
  have h2 : ¬(CompCert.Int64.one == CompCert.Int64.mone) := by decide
  simp [h1, h2, CompCert.Int64.divs_one]

theorem divlu_pow2 (x : val) (n : CompCert.Int64) (logn : CompCert.Int) (y : val)
    (H1 : CompCert.Int64.is_power2' n = some logn)
    (H2 : divlu x (.Vlong n) = some y) :
    shrlu x (.Vint logn) = y := by
  -- From H2, x must be Vlong and n ≠ 0
  cases x with
  | Vundef | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ =>
    unfold divlu at H2; contradiction
  | Vlong i =>
    unfold divlu at H2
    by_cases hn : n == CompCert.Int64.zero
    · simp [hn] at H2
    · simp [hn] at H2
      subst H2
      -- Goal: shrlu (Vlong i) (Vint logn) = Vlong (Int64.divu i n)
      have ⟨hn_eq, hlogn_lt⟩ := CompCert.Int64.is_power2'_pow n logn H1
      simp only [shrlu]
      have h_ltu : CompCert.Int.ltu logn CompCert.Int64.iwordsize' = true := by
        unfold CompCert.Int.ltu CompCert.Int64.iwordsize'
        simp only [decide_eq_true_eq]
        exact hlogn_lt
      rw [if_pos h_ltu]
      congr 1
      exact (CompCert.Int64.divu_pow2 i n logn H1).symm

theorem divlu_one (n : CompCert.Int64) :
    divlu (.Vlong n) (.Vlong CompCert.Int64.one) = some (.Vlong n) := by
  simp [divlu]
  constructor
  · decide
  · exact CompCert.Int64.divu_one n

theorem modlu_pow2 (x : val) (n logn : CompCert.Int64) (y : val)
    (H1 : CompCert.Int64.is_power2 n = some logn)
    (H2 : modlu x (.Vlong n) = some y) :
    andl x (.Vlong (CompCert.Int64.sub n CompCert.Int64.one)) = y := by
  -- From H2, x must be Vlong and n ≠ 0
  cases x with
  | Vundef | Vint _ | Vfloat _ | Vsingle _ | Vptr _ _ =>
    unfold modlu at H2; contradiction
  | Vlong i =>
    unfold modlu at H2
    by_cases hn : n == CompCert.Int64.zero
    · simp [hn] at H2
    · simp [hn] at H2
      subst H2
      -- Goal: andl (Vlong i) (Vlong (sub n one)) = Vlong (Int64.modu i n)
      simp only [andl]
      congr 1
      exact (CompCert.Int64.modu_pow2 i n logn H1).symm

theorem shrxl_carry (x y z : val)
    (H : shrxl x y = some z) :
    addl (shrl x y) (shrl_carry x y) = z := by
  -- From shrxl x y = some z, extract n1, n2
  unfold shrxl at H
  cases x <;> cases y <;> simp at H; try contradiction
  case Vlong.Vint n1 n2 =>
    -- After simp, H is an if-then-else
    by_cases hltu : CompCert.Int.ltu n2 (CompCert.Int.repr 63)
    · -- ltu n2 (repr 63) = true
      simp [hltu] at H
      rw [← H]
      -- Goal: addl (shrl (val.Vlong n1) (val.Vint n2)) (shrl_carry (val.Vlong n1) (val.Vint n2)) = val.Vlong (CompCert.Int64.shrx' n1 n2)
      unfold addl shrl shrl_carry
      simp only []
      -- Need to show the ltu guards pass
      have hbound : n2.toNat < 63 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at hltu
        have : (UInt32.ofInt 63).toNat = 63 := by rfl
        simp at hltu
        exact hltu
      have hltu_iws : CompCert.Int.ltu n2 CompCert.Int64.iwordsize' = true := by
        unfold CompCert.Int.ltu CompCert.Int64.iwordsize'
        have : (64 : UInt32).toNat = 64 := by rfl
        simp
        show n2.toNat < 64
        omega
      simp [hltu_iws]
      -- Apply the Int64-level theorem
      exact CompCert.Int64.shrx_carry'_eq n1 n2 hbound
    · -- ltu n2 (repr 63) = false, contradiction
      simp [hltu] at H

theorem shrxl_shrl_2 (n : CompCert.Int) (x z : val)
    (H : shrxl x (.Vint n) = some z) :
    z = (if CompCert.Int.eq n CompCert.Int.zero then x else
         shrl (addl x (shrlu (shrl x (.Vint (CompCert.Int.repr 63)))
                      (.Vint (CompCert.Int.sub (CompCert.Int.repr 64) n))))
              (.Vint n)) := by
  -- Extract that x = Vlong p
  unfold shrxl at H
  cases x <;> simp at H; try contradiction
  case Vlong p =>
    by_cases hltu : CompCert.Int.ltu n (CompCert.Int.repr 63)
    · -- n < 63, so z = Vlong (shrx' p n)
      simp [hltu] at H
      subst H
      have hbound : n.toNat < 63 := by
        unfold CompCert.Int.ltu CompCert.Int.repr at hltu
        have h63 : (UInt32.ofInt 63).toNat = 63 := by rfl
        simp at hltu; exact hltu
      -- Int-level characterization
      rw [CompCert.Int64.shrx_shr_2'_eq p n hbound]
      by_cases hn : CompCert.Int.eq n CompCert.Int.zero
      · simp only [hn, if_true]
      · simp only [hn]
        have hn0 : n.toNat ≠ 0 := by
          intro h
          apply hn
          unfold CompCert.Int.eq CompCert.Int.zero
          have : n = 0 := by apply UInt32.toNat.inj; simpa using h
          simp [this]
        -- Now push through the val operations
        -- shrl (Vlong p) (Vint (repr 63))
        have hltu_63 : CompCert.Int.ltu (CompCert.Int.repr 63) CompCert.Int64.iwordsize' = true := by
          unfold CompCert.Int.ltu CompCert.Int64.iwordsize'
          decide
        -- shrlu needs ltu check
        have hltu_sub : CompCert.Int.ltu (CompCert.Int.sub (CompCert.Int.repr 64) n) CompCert.Int64.iwordsize' = true := by
          unfold CompCert.Int.ltu CompCert.Int64.iwordsize'
          have h64 : (64 : UInt32).toNat = 64 := by rfl
          simp
          have : (CompCert.Int.sub (CompCert.Int.repr 64) n).toNat < 64 := by
            have h64' : (CompCert.Int.repr 64).toNat = 64 := by decide
            show ((CompCert.Int.repr 64) - n).toNat < 64
            rw [UInt32.toNat_sub, h64']
            omega
          exact this
        -- shrl addl needs ltu check
        have hltu_n : CompCert.Int.ltu n CompCert.Int64.iwordsize' = true := by
          unfold CompCert.Int.ltu CompCert.Int64.iwordsize'
          have h64 : (64 : UInt32).toNat = 64 := by rfl
          simp
          show n.toNat < 64
          omega
        -- Now compute
        show val.Vlong (CompCert.Int64.shr' (CompCert.Int64.add p (CompCert.Int64.shru' (CompCert.Int64.shr' p (CompCert.Int.repr 63)) (CompCert.Int.sub (CompCert.Int.repr 64) n))) n)
              = shrl (addl (val.Vlong p) (shrlu (shrl (val.Vlong p) (val.Vint (CompCert.Int.repr 63))) (val.Vint (CompCert.Int.sub (CompCert.Int.repr 64) n)))) (val.Vint n)
        simp [shrl, hltu_63, hltu_sub, hltu_n, shrlu, addl]
    · -- n >= 63, contradiction with H = some
      simp [hltu] at H

/- ** Properties of comparisons -/

theorem negate_cmp_bool (c : comparison) (x y : val) :
    cmp_bool (negate_comparison c) x y = Option.map not (cmp_bool c x y) := by
  cases x <;> cases y <;> simp [cmp_bool]
  case Vint.Vint n1 n2 =>
    rw [CompCert.Int.cmp_negate]

theorem negate_cmpu_bool (valid_ptr : block → Int → Bool) (c : comparison) (x y : val) :
    cmpu_bool valid_ptr (negate_comparison c) x y = Option.map not (cmpu_bool valid_ptr c x y) := by
  cases x <;> cases y <;>
    simp only [cmpu_bool] <;>
    (try rfl)
  case Vint.Vint n1 n2 =>
    rw [CompCert.Int.cmpu_negate]; rfl
  case Vint.Vptr n1 b2 ofs2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_negate]
      · rfl
  case Vptr.Vint b1 ofs1 n2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_negate]
      · rfl
  case Vptr.Vptr b1 ofs1 b2 ofs2 =>
    split
    · rfl
    · split
      · split
        · rw [Ptrofs.cmpu_negate]; rfl
        · rfl
      · split
        · rw [cmp_different_blocks_negate]
        · rfl

theorem negate_cmpl_bool (c : comparison) (x y : val) :
    cmpl_bool (negate_comparison c) x y = Option.map not (cmpl_bool c x y) := by
  cases x <;> cases y <;> simp [cmpl_bool]
  case Vlong.Vlong n1 n2 =>
    rw [CompCert.Int64.cmp_negate]

theorem negate_cmplu_bool (valid_ptr : block → Int → Bool) (c : comparison) (x y : val) :
    cmplu_bool valid_ptr (negate_comparison c) x y = Option.map not (cmplu_bool valid_ptr c x y) := by
  cases x <;> cases y <;>
    simp only [cmplu_bool] <;>
    (try rfl)
  case Vlong.Vlong n1 n2 =>
    rw [CompCert.Int64.cmpu_negate]; rfl
  case Vlong.Vptr n1 b2 ofs2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_negate]
      · rfl
  case Vptr.Vlong b1 ofs1 n2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_negate]
      · rfl
  case Vptr.Vptr b1 ofs1 b2 ofs2 =>
    split
    · rfl
    · split
      · split
        · rw [Ptrofs.cmpu_negate]; rfl
        · rfl
      · split
        · rw [cmp_different_blocks_negate]
        · rfl

theorem not_of_optbool (ob : Option Bool) :
    of_optbool (Option.map not ob) = notbool (of_optbool ob) := by
  cases ob <;> simp [of_optbool, notbool]
  case some b => cases b <;> rfl

theorem negate_cmp (c : comparison) (x y : val) :
    cmp (negate_comparison c) x y = notbool (cmp c x y) := by
  simp [cmp]
  rw [negate_cmp_bool]
  rw [not_of_optbool]

theorem negate_cmpu (valid_ptr : block → Int → Bool) (c : comparison) (x y : val) :
    cmpu valid_ptr (negate_comparison c) x y = notbool (cmpu valid_ptr c x y) := by
  simp [cmpu]
  rw [negate_cmpu_bool]
  rw [not_of_optbool]

theorem swap_cmp_bool (c : comparison) (x y : val) :
    cmp_bool (swap_comparison c) x y = cmp_bool c y x := by
  cases x <;> cases y <;> simp [cmp_bool]
  case Vint.Vint n1 n2 =>
    rw [CompCert.Int.cmp_swap]

theorem swap_cmpu_bool (valid_ptr : block → Int → Bool) (c : comparison) (x y : val) :
    cmpu_bool valid_ptr (swap_comparison c) x y = cmpu_bool valid_ptr c y x := by
  cases x <;> cases y <;>
    simp only [cmpu_bool]
  case Vint.Vint n1 n2 =>
    rw [CompCert.Int.cmpu_swap]
  case Vint.Vptr n1 b2 ofs2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_swap]
      · rfl
  case Vptr.Vint b1 ofs1 n2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_swap]
      · rfl
  case Vptr.Vptr b1 ofs1 b2 ofs2 =>
    split
    · rfl
    · rw [Bool.beq_comm (a := b1) (b := b2)]
      split
      · rw [Bool.and_comm]
        split
        · rw [Ptrofs.cmpu_swap]
        · rfl
      · rw [Bool.and_comm]
        split
        · rw [cmp_different_blocks_swap]
        · rfl

theorem swap_cmpl_bool (c : comparison) (x y : val) :
    cmpl_bool (swap_comparison c) x y = cmpl_bool c y x := by
  cases x <;> cases y <;> simp [cmpl_bool]
  case Vlong.Vlong n1 n2 =>
    rw [CompCert.Int64.cmp_swap]

theorem swap_cmplu_bool (valid_ptr : block → Int → Bool) (c : comparison) (x y : val) :
    cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x := by
  cases x <;> cases y <;>
    simp only [cmplu_bool]
  case Vlong.Vlong n1 n2 =>
    rw [CompCert.Int64.cmpu_swap]
  case Vlong.Vptr n1 b2 ofs2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_swap]
      · rfl
  case Vptr.Vlong b1 ofs1 n2 =>
    split
    · rfl
    · split
      · rw [cmp_different_blocks_swap]
      · rfl
  case Vptr.Vptr b1 ofs1 b2 ofs2 =>
    split
    · rfl
    · rw [Bool.beq_comm (a := b1) (b := b2)]
      split
      · rw [Bool.and_comm]
        split
        · rw [Ptrofs.cmpu_swap]
        · rfl
      · rw [Bool.and_comm]
        split
        · rw [cmp_different_blocks_swap]
        · rfl

/- ** Properties of floating-point comparisons -/

theorem negate_cmpf_eq (v1 v2 : val) :
    notbool (cmpf .Cne v1 v2) = cmpf .Ceq v1 v2 := by
  cases v1 <;> cases v2 <;> simp [cmpf, cmpf_bool, of_optbool, notbool, of_bool]
  case Vfloat.Vfloat f1 f2 =>
    simp only [CompCert.Float64.cmp, bne]
    cases h : f1 == f2 <;> simp [Vtrue, Vfalse, CompCert.Int.zero, CompCert.Int.one]

theorem negate_cmpf_ne (v1 v2 : val) :
    notbool (cmpf .Ceq v1 v2) = cmpf .Cne v1 v2 := by
  cases v1 <;> cases v2 <;> simp [cmpf, cmpf_bool, of_optbool, notbool, of_bool]
  case Vfloat.Vfloat f1 f2 =>
    simp only [CompCert.Float64.cmp, bne]
    cases h : f1 == f2 <;> simp [Vtrue, Vfalse, CompCert.Int.zero, CompCert.Int.one]

theorem cmpf_le (v1 v2 : val) :
    cmpf .Cle v1 v2 = or (cmpf .Clt v1 v2) (cmpf .Ceq v1 v2) := by
  cases v1 <;> cases v2 <;> simp [cmpf, cmpf_bool, of_optbool, or]
  case Vfloat.Vfloat f1 f2 =>
    simp only [CompCert.Float64.cmp]
    rw [CompCert.Float64.le_eq_lt_or_eq f1 f2]
    cases decide (f1 < f2) <;> cases f1 == f2 <;>
      simp [Vtrue, Vfalse, CompCert.Int.zero, CompCert.Int.one,
        CompCert.Int.or, UInt32.lor]

theorem cmpf_ge (v1 v2 : val) :
    cmpf .Cge v1 v2 = or (cmpf .Cgt v1 v2) (cmpf .Ceq v1 v2) := by
  cases v1 <;> cases v2 <;> simp [cmpf, cmpf_bool, of_optbool, or]
  case Vfloat.Vfloat f1 f2 =>
    simp only [CompCert.Float64.cmp]
    rw [CompCert.Float64.le_eq_lt_or_eq f2 f1, CompCert.Float64.beq_comm f2 f1]
    cases decide (f2 < f1) <;> cases f1 == f2 <;>
      simp [Vtrue, Vfalse, CompCert.Int.zero, CompCert.Int.one,
        CompCert.Int.or, UInt32.lor]

theorem cmp_ne_0_optbool (ob : Option Bool) :
    cmp .Cne (of_optbool ob) (.Vint CompCert.Int.zero) = of_optbool ob := by
  cases ob <;> simp [of_optbool]
  case none => rfl
  case some b =>
    cases b <;> rfl

theorem cmp_eq_1_optbool (ob : Option Bool) :
    cmp .Ceq (of_optbool ob) (.Vint CompCert.Int.one) = of_optbool ob := by
  cases ob <;> simp [of_optbool]
  case none => rfl
  case some b =>
    cases b <;> rfl

theorem cmp_eq_0_optbool (ob : Option Bool) :
    cmp .Ceq (of_optbool ob) (.Vint CompCert.Int.zero) = of_optbool (Option.map not ob) := by
  cases ob <;> simp [of_optbool]
  case none => rfl
  case some b =>
    cases b <;> rfl

theorem cmp_ne_1_optbool (ob : Option Bool) :
    cmp .Cne (of_optbool ob) (.Vint CompCert.Int.one) = of_optbool (Option.map not ob) := by
  cases ob <;> simp [of_optbool]
  case none => rfl
  case some b =>
    cases b <;> rfl

theorem cmpu_ne_0_optbool (valid_ptr : block → Int → Bool) (ob : Option Bool) :
    cmpu valid_ptr .Cne (of_optbool ob) (.Vint CompCert.Int.zero) = of_optbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

theorem cmpu_eq_1_optbool (valid_ptr : block → Int → Bool) (ob : Option Bool) :
    cmpu valid_ptr .Ceq (of_optbool ob) (.Vint CompCert.Int.one) = of_optbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

theorem cmpu_eq_0_optbool (valid_ptr : block → Int → Bool) (ob : Option Bool) :
    cmpu valid_ptr .Ceq (of_optbool ob) (.Vint CompCert.Int.zero) = of_optbool (Option.map not ob) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

theorem cmpu_ne_1_optbool (valid_ptr : block → Int → Bool) (ob : Option Bool) :
    cmpu valid_ptr .Cne (of_optbool ob) (.Vint CompCert.Int.one) = of_optbool (Option.map not ob) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

theorem zero_ext_and (n : Nat) (v : val) (_H : 0 ≤ n) :
    zero_ext n v = and v (.Vint (CompCert.Int.repr (two_p n - 1))) := by
  cases v <;> simp [zero_ext, and]; try rfl
  case Vint i => rw [CompCert.Int.zero_ext_and]

theorem zero_ext_andl (n : Nat) (v : val) (_H : 0 ≤ n) :
    zero_ext_l n v = andl v (.Vlong (CompCert.Int64.repr (two_p n - 1))) := by
  cases v <;> simp [zero_ext_l, andl]; try rfl
  case Vlong i => rw [CompCert.Int64.zero_ext_and]

theorem rolm_lt_zero (v : val) :
    rolm v CompCert.Int.one CompCert.Int.one = cmp .Clt v (.Vint CompCert.Int.zero) := by
  cases v <;>
    simp only [rolm, cmp, cmp_bool, of_optbool]
  case Vint i =>
    rw [CompCert.Int.rolm_one_one_eq_lt]
    show (.Vint (if i.signed < 0 then CompCert.Int.one else CompCert.Int.zero) : val)
       = of_optbool (some (CompCert.Int.cmp .Clt i CompCert.Int.zero))
    simp only [CompCert.Int.cmp]
    show (.Vint (if i.signed < 0 then CompCert.Int.one else CompCert.Int.zero) : val)
       = of_optbool (some (decide (i.signed < CompCert.Int.zero.signed)))
    have hz : CompCert.Int.zero.signed = 0 := by decide
    rw [hz]
    by_cases h : i.signed < 0 <;> simp [h, of_optbool, Vtrue, Vfalse]

theorem rolm_ge_zero (v : val) :
    xor (rolm v CompCert.Int.one CompCert.Int.one) (.Vint CompCert.Int.one) = cmp .Cge v (.Vint CompCert.Int.zero) := by
  cases v <;>
    simp only [rolm, xor, cmp, cmp_bool, of_optbool]
  case Vint i =>
    rw [CompCert.Int.rolm_one_one_eq_lt]
    simp only [CompCert.Int.cmp]
    have hz : CompCert.Int.zero.signed = 0 := by decide
    rw [hz]
    by_cases h : i.signed < 0
    · have hge : ¬ (i.signed ≥ 0) := by omega
      simp only [h, if_true, hge, decide_false]
      show (.Vint (CompCert.Int.xor CompCert.Int.one CompCert.Int.one) : val) = Vfalse
      rfl
    · have hge : i.signed ≥ 0 := by omega
      simp only [h, if_false, hge, decide_true]
      show (.Vint (CompCert.Int.xor CompCert.Int.zero CompCert.Int.one) : val) = Vtrue
      rfl

/- ** The "less defined" relation between values -/

/-- A value is less defined than itself, and [Vundef] is less defined than any value. -/
inductive lessdef : val → val → Prop
  | lessdef_refl (v : val) : lessdef v v
  | lessdef_undef (v : val) : lessdef .Vundef v

theorem lessdef_same (v1 v2 : val) (H : v1 = v2) :
    lessdef v1 v2 := by
  rw [H]
  exact lessdef.lessdef_refl v2

theorem lessdef_trans (v1 v2 v3 : val)
    (H1 : lessdef v1 v2) (H2 : lessdef v2 v3) :
    lessdef v1 v3 := by
  cases H1 with
  | lessdef_refl =>
    -- v1 = v2, so need lessdef v2 v3 which is H2
    exact H2
  | lessdef_undef =>
    -- v1 = Vundef, so lessdef Vundef v3
    exact lessdef.lessdef_undef v3

inductive lessdef_list : List val → List val → Prop
  | lessdef_list_nil : lessdef_list [] []
  | lessdef_list_cons (v1 v2 : val) (vl1 vl2 : List val)
      (H1 : lessdef v1 v2) (H2 : lessdef_list vl1 vl2) :
      lessdef_list (v1 :: vl1) (v2 :: vl2)

theorem lessdef_list_inv (vl1 vl2 : List val)
    (H : lessdef_list vl1 vl2) :
    vl1 = vl2 ∨ .Vundef ∈ vl1 := by
  induction H with
  | lessdef_list_nil => left; rfl
  | lessdef_list_cons v1 v2 vl1 vl2 Hv Hvl IH =>
    cases Hv with
    | lessdef_refl =>
      cases IH with
      | inl h => left; rw [h]
      | inr h => right; exact List.Mem.tail v1 h
    | lessdef_undef =>
      right; exact List.Mem.head vl1

theorem lessdef_list_trans (vl1 vl2 vl3 : List val)
    (H1 : lessdef_list vl1 vl2) (H2 : lessdef_list vl2 vl3) :
    lessdef_list vl1 vl3 := by
  induction H1 generalizing vl3 with
  | lessdef_list_nil =>
    cases H2
    exact lessdef_list.lessdef_list_nil
  | lessdef_list_cons v1 v2 vl1 vl2 Hv Hvl IH =>
    cases H2 with
    | lessdef_list_cons v2' v3 vl2' vl3 Hv' Hvl' =>
      apply lessdef_list.lessdef_list_cons
      · exact lessdef_trans v1 v2 v3 Hv Hv'
      · exact IH vl3 Hvl'

/- ** Compatibility of operations with [lessdef] relation -/

theorem load_result_lessdef (chunk : memory_chunk) (v1 v2 : val)
    (H : lessdef v1 v2) :
    lessdef (load_result chunk v1) (load_result chunk v2) := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef =>
    cases chunk <;> simp [load_result]
    all_goals exact lessdef.lessdef_undef _

theorem norm_bool_is_lessdef (v : val) :
    lessdef (norm_bool v) v := by
  simp [norm_bool]
  split
  · exact lessdef.lessdef_refl _
  · exact lessdef.lessdef_undef _

theorem norm_bool_lessdef (v1 v2 : val)
    (H : lessdef v1 v2) :
    lessdef (norm_bool v1) (norm_bool v2) := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef => exact lessdef.lessdef_undef _

theorem zero_ext_lessdef (n : Nat) (v1 v2 : val)
    (H : lessdef v1 v2) :
    lessdef (zero_ext n v1) (zero_ext n v2) := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef => simp [zero_ext]; exact lessdef.lessdef_undef _

theorem sign_ext_lessdef (n : Nat) (v1 v2 : val)
    (H : lessdef v1 v2) :
    lessdef (sign_ext n v1) (sign_ext n v2) := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef => simp [sign_ext]; exact lessdef.lessdef_undef _

theorem singleoffloat_lessdef (v1 v2 : val)
    (H : lessdef v1 v2) :
    lessdef (singleoffloat v1) (singleoffloat v2) := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef => simp [singleoffloat]; exact lessdef.lessdef_undef _

theorem add_lessdef (v1 v1' v2 v2' : val)
    (H1 : lessdef v1 v1') (H2 : lessdef v2 v2') :
    lessdef (add v1 v2) (add v1' v2') := by
  cases H1 <;> cases H2
  · exact lessdef.lessdef_refl _
  · simp [add]; split <;> exact lessdef.lessdef_undef _
  · simp [add]; split <;> exact lessdef.lessdef_undef _
  · exact lessdef.lessdef_undef _

theorem addl_lessdef (v1 v1' v2 v2' : val)
    (H1 : lessdef v1 v1') (H2 : lessdef v2 v2') :
    lessdef (addl v1 v2) (addl v1' v2') := by
  cases H1 <;> cases H2
  · exact lessdef.lessdef_refl _
  · simp [addl]; split <;> exact lessdef.lessdef_undef _
  · simp [addl]; split <;> exact lessdef.lessdef_undef _
  · exact lessdef.lessdef_undef _

theorem cmpu_bool_lessdef (valid_ptr valid_ptr' : block → Int → Bool)
    (c : comparison) (v1 v1' v2 v2' : val) (b : Bool)
    (H_ptr : ∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true)
    (H1 : lessdef v1 v1') (H2 : lessdef v2 v2')
    (H3 : cmpu_bool valid_ptr c v1 v2 = some b) :
    cmpu_bool valid_ptr' c v1' v2' = some b := by
  -- If v1 or v2 is Vundef, cmpu_bool = none, contradicting H3. So both are refl.
  cases H1 with
  | lessdef_undef =>
    -- v1 = Vundef, so cmpu_bool returns none regardless of v2
    exfalso
    cases v2 <;> simp only [cmpu_bool] at H3 <;>
      cases H3
  | lessdef_refl =>
    cases H2 with
    | lessdef_undef =>
      -- v2 = Vundef, so cmpu_bool returns none regardless of v1
      exfalso
      cases v1 <;> simp only [cmpu_bool] at H3 <;>
        cases H3
    | lessdef_refl =>
      -- v1' = v1, v2' = v2. Now monotonicity in valid_ptr.
      have hweak : ∀ bb oo, weak_valid_ptr valid_ptr bb oo = true →
          weak_valid_ptr valid_ptr' bb oo = true := by
        intro bb oo hh
        simp only [weak_valid_ptr, Bool.or_eq_true] at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (H_ptr _ _ hh)
        · exact Or.inr (H_ptr _ _ hh)
      -- Now case on v1, v2
      cases v1 <;> cases v2 <;> simp only [cmpu_bool] at H3 ⊢
      -- Vint, Vint: no valid_ptr dependence
      case Vint.Vint => exact H3
      -- Handle all none cases (Vundef and incompatible combinations)
      -- Vundef cases
      case Vundef.Vundef | Vundef.Vint | Vundef.Vlong | Vundef.Vfloat | Vundef.Vsingle | Vundef.Vptr => cases H3
      case Vint.Vundef | Vlong.Vundef | Vfloat.Vundef | Vsingle.Vundef | Vptr.Vundef => cases H3
      -- Incompatible type combinations (non-Vint, non-Vptr with each other)
      case Vint.Vlong | Vint.Vfloat | Vint.Vsingle => cases H3
      case Vlong.Vint | Vlong.Vlong | Vlong.Vfloat | Vlong.Vsingle | Vlong.Vptr => cases H3
      case Vfloat.Vint | Vfloat.Vlong | Vfloat.Vfloat | Vfloat.Vsingle | Vfloat.Vptr => cases H3
      case Vsingle.Vint | Vsingle.Vlong | Vsingle.Vfloat | Vsingle.Vsingle | Vsingle.Vptr => cases H3
      case Vptr.Vlong | Vptr.Vfloat | Vptr.Vsingle => cases H3
      -- Vint, Vptr: pointer guard with weak_valid_ptr
      case Vint.Vptr =>
        split at H3; · simp at H3
        rename_i harch
        split at H3
        · rename_i hcond
          -- H3 : cmp_different_blocks c = some b
          simp only [harch]
          simp only [Bool.and_eq_true] at hcond
          have : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hcond.2
          simp [hcond.1, this, H3]
        · simp at H3
      -- Vptr, Vint: pointer guard with weak_valid_ptr
      case Vptr.Vint =>
        split at H3; · simp at H3
        rename_i harch
        split at H3
        · rename_i hcond
          -- H3 : cmp_different_blocks c = some b
          simp only [harch]
          simp only [Bool.and_eq_true] at hcond
          have : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hcond.2
          simp [hcond.1, this, H3]
        · simp at H3
      -- Vptr, Vptr: same-block or different-block
      case Vptr.Vptr =>
        split at H3; · simp at H3
        rename_i harch
        split at H3
        · -- same block case
          rename_i hsame
          split at H3
          · rename_i hweaks
            -- H3 : some (Ptrofs.cmpu c ofs1 ofs2) = some b
            simp only [harch, hsame, ite_true]
            simp only [Bool.and_eq_true] at hweaks
            have h1 : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hweaks.1
            have h2 : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hweaks.2
            simp [h1, h2, H3]
          · simp at H3
        · -- different block case
          rename_i hdiff
          split at H3
          · rename_i hvalids
            -- H3 : cmp_different_blocks c = some b
            simp only [harch, hdiff]
            simp only [Bool.and_eq_true] at hvalids
            have h1 : valid_ptr' _ _ = true := H_ptr _ _ hvalids.1
            have h2 : valid_ptr' _ _ = true := H_ptr _ _ hvalids.2
            simp [h1, h2, H3]
          · simp at H3

theorem cmplu_bool_lessdef (valid_ptr valid_ptr' : block → Int → Bool)
    (c : comparison) (v1 v1' v2 v2' : val) (b : Bool)
    (H_ptr : ∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true)
    (H1 : lessdef v1 v1') (H2 : lessdef v2 v2')
    (H3 : cmplu_bool valid_ptr c v1 v2 = some b) :
    cmplu_bool valid_ptr' c v1' v2' = some b := by
  -- If v1 or v2 is Vundef, cmplu_bool = none, contradicting H3. So both are refl.
  cases H1 with
  | lessdef_undef =>
    -- v1 = Vundef, so cmplu_bool returns none regardless of v2
    exfalso
    cases v2 <;> simp only [cmplu_bool] at H3 <;>
      cases H3
  | lessdef_refl =>
    cases H2 with
    | lessdef_undef =>
      -- v2 = Vundef, so cmplu_bool returns none regardless of v1
      exfalso
      cases v1 <;> simp only [cmplu_bool] at H3 <;>
        cases H3
    | lessdef_refl =>
      -- v1' = v1, v2' = v2. Now monotonicity in valid_ptr.
      have hweak : ∀ bb oo, weak_valid_ptr valid_ptr bb oo = true →
          weak_valid_ptr valid_ptr' bb oo = true := by
        intro bb oo hh
        simp only [weak_valid_ptr, Bool.or_eq_true] at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (H_ptr _ _ hh)
        · exact Or.inr (H_ptr _ _ hh)
      -- Now case on v1, v2
      cases v1 <;> cases v2 <;> simp only [cmplu_bool] at H3 ⊢
      -- Vlong, Vlong: no valid_ptr dependence
      case Vlong.Vlong => exact H3
      -- Handle all none cases (Vundef and incompatible combinations)
      -- Vundef cases
      case Vundef.Vundef | Vundef.Vint | Vundef.Vlong | Vundef.Vfloat | Vundef.Vsingle | Vundef.Vptr => cases H3
      case Vint.Vundef | Vlong.Vundef | Vfloat.Vundef | Vsingle.Vundef | Vptr.Vundef => cases H3
      -- Incompatible type combinations (non-Vlong, non-Vptr with each other)
      case Vint.Vint | Vint.Vlong | Vint.Vfloat | Vint.Vsingle | Vint.Vptr => cases H3
      case Vlong.Vint | Vlong.Vfloat | Vlong.Vsingle => cases H3
      case Vfloat.Vint | Vfloat.Vlong | Vfloat.Vfloat | Vfloat.Vsingle | Vfloat.Vptr => cases H3
      case Vsingle.Vint | Vsingle.Vlong | Vsingle.Vfloat | Vsingle.Vsingle | Vsingle.Vptr => cases H3
      case Vptr.Vint | Vptr.Vfloat | Vptr.Vsingle => cases H3
      -- Vlong, Vptr: pointer guard with weak_valid_ptr (active when !Archi.ptr64, i.e., Archi.ptr64 = false means 64-bit arch)
      case Vlong.Vptr =>
        split at H3; · simp at H3
        rename_i harch
        split at H3
        · rename_i hcond
          -- H3 : cmp_different_blocks c = some b
          simp only [harch]
          simp only [Bool.and_eq_true] at hcond
          have : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hcond.2
          simp [hcond.1, this, H3]
        · simp at H3
      -- Vptr, Vlong: pointer guard with weak_valid_ptr
      case Vptr.Vlong =>
        split at H3; · simp at H3
        rename_i harch
        split at H3
        · rename_i hcond
          -- H3 : cmp_different_blocks c = some b
          simp only [harch]
          simp only [Bool.and_eq_true] at hcond
          have : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hcond.2
          simp [hcond.1, this, H3]
        · simp at H3
      -- Vptr, Vptr: same-block or different-block
      case Vptr.Vptr =>
        split at H3; · simp at H3
        rename_i harch
        split at H3
        · -- same block case
          rename_i hsame
          split at H3
          · rename_i hweaks
            -- H3 : some (Ptrofs.cmpu c ofs1 ofs2) = some b
            simp only [harch, hsame, ite_true]
            simp only [Bool.and_eq_true] at hweaks
            have h1 : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hweaks.1
            have h2 : weak_valid_ptr valid_ptr' _ _ = true := hweak _ _ hweaks.2
            simp [h1, h2, H3]
          · simp at H3
        · -- different block case
          rename_i hdiff
          split at H3
          · rename_i hvalids
            -- H3 : cmp_different_blocks c = some b
            simp only [harch, hdiff]
            simp only [Bool.and_eq_true] at hvalids
            have h1 : valid_ptr' _ _ = true := H_ptr _ _ hvalids.1
            have h2 : valid_ptr' _ _ = true := H_ptr _ _ hvalids.2
            simp [h1, h2, H3]
          · simp at H3

theorem of_optbool_lessdef (ob ob' : Option Bool)
    (H : ∀ b, ob = some b → ob' = some b) :
    lessdef (of_optbool ob) (of_optbool ob') := by
  cases hob : ob with
  | none =>
    simp [of_optbool]
    exact lessdef.lessdef_undef _
  | some b =>
    have h := H b hob
    simp [h, of_optbool]
    exact lessdef.lessdef_refl _

theorem longofwords_lessdef (v1 v2 v1' v2' : val)
    (H1 : lessdef v1 v1') (H2 : lessdef v2 v2') :
    lessdef (longofwords v1 v2) (longofwords v1' v2') := by
  cases H1 <;> cases H2
  · exact lessdef.lessdef_refl _
  · simp [longofwords]; split <;> exact lessdef.lessdef_undef _
  · simp [longofwords]; split <;> exact lessdef.lessdef_undef _
  · exact lessdef.lessdef_undef _

theorem loword_lessdef (v v' : val)
    (H : lessdef v v') :
    lessdef (loword v) (loword v') := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef => simp [loword]; exact lessdef.lessdef_undef _

theorem hiword_lessdef (v v' : val)
    (H : lessdef v v') :
    lessdef (hiword v) (hiword v') := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef => simp [hiword]; exact lessdef.lessdef_undef _

theorem offset_ptr_zero (v : val) :
    lessdef (offset_ptr v Ptrofs.zero) v := by
  cases v <;> simp only [offset_ptr]
  all_goals (try exact lessdef.lessdef_undef _)
  case Vptr b ofs =>
    rw [Ptrofs.add_zero]
    exact lessdef.lessdef_refl _

theorem offset_ptr_assoc (v : val) (d1 d2 : Ptrofs) :
    offset_ptr (offset_ptr v d1) d2 = offset_ptr v (Ptrofs.add d1 d2) := by
  cases v <;> simp only [offset_ptr]
  case Vptr b ofs =>
    rw [Ptrofs.add_assoc]

theorem lessdef_normalize (v : val) (ty : typ) :
    lessdef (normalize v ty) v := by
  cases v <;> cases ty <;> simp [normalize]
  all_goals (try exact lessdef.lessdef_refl _)
  all_goals (try exact lessdef.lessdef_undef _)
  all_goals (try (split <;> (try exact lessdef.lessdef_refl _); (try exact lessdef.lessdef_undef _)))

theorem normalize_lessdef (v v' : val) (ty : typ)
    (H : lessdef v v') :
    lessdef (normalize v ty) (normalize v' ty) := by
  cases H with
  | lessdef_refl => exact lessdef.lessdef_refl _
  | lessdef_undef =>
    simp only [normalize]
    exact lessdef.lessdef_undef _

theorem select_lessdef (ob ob' : Option Bool) (v1 v1' v2 v2' : val) (ty : typ)
    (H_ob : ob = none ∨ ob = ob')
    (H1 : lessdef v1 v1') (H2 : lessdef v2 v2') :
    lessdef (select ob v1 v2 ty) (select ob' v1' v2' ty) := by
  rcases H_ob with hob | hob
  · -- ob = none
    rw [hob]
    simp only [select]
    exact lessdef.lessdef_undef _
  · -- ob = ob'
    rw [hob]
    cases ob'
    · simp only [select]; exact lessdef.lessdef_undef _
    case some b =>
      simp only [select]
      apply normalize_lessdef
      cases b <;> simp
      · exact H2
      · exact H1

theorem has_argtype_lessdef (v v' : val) (r : xtype)
    (H1 : has_argtype v r) (H2 : lessdef v v') :
    has_argtype v' r := by
  cases H2 with
  | lessdef_refl => exact H1
  | lessdef_undef =>
    cases v' <;> cases r <;> simp [has_argtype] at H1 ⊢

theorem has_argtype_list_lessdef (vl vl' : List val) (rl : List xtype)
    (H1 : has_argtype_list vl rl) (H2 : lessdef_list vl vl') :
    has_argtype_list vl' rl := by
  induction H2 generalizing rl with
  | lessdef_list_nil =>
    cases rl
    · exact H1
    · cases H1
  | lessdef_list_cons v1 v2 vl1 vl2 Hv Hvl IH =>
    cases rl with
    | nil => cases H1
    | cons r rl =>
      simp [has_argtype_list] at H1 ⊢
      constructor
      · exact has_argtype_lessdef v1 v2 r H1.1 Hv
      · exact IH rl H1.2

/- ** Values and memory injections -/

/-- A memory injection is a function from addresses to either [None] or [Some] of an address and an offset. -/
def meminj : Type := block → Option (block × Int)

/-- A memory injection defines a relation between values that is the identity relation,
    except for pointer values which are shifted as prescribed by the memory injection.
    Moreover, [Vundef] values inject into any other value. -/
inductive inject (mi : meminj) : val → val → Prop
  | inject_int (i : CompCert.Int) : inject mi (.Vint i) (.Vint i)
  | inject_long (i : CompCert.Int64) : inject mi (.Vlong i) (.Vlong i)
  | inject_float (f : CompCert.Float64) : inject mi (.Vfloat f) (.Vfloat f)
  | inject_single (f : CompCert.Float32) : inject mi (.Vsingle f) (.Vsingle f)
  | inject_ptr (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs) (delta : Int)
      (H1 : mi b1 = some (b2, delta))
      (H2 : ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta)) :
      inject mi (.Vptr b1 ofs1) (.Vptr b2 ofs2)
  | val_inject_undef (v : val) : inject mi .Vundef v

inductive inject_list (mi : meminj) : List val → List val → Prop
  | inject_list_nil : inject_list mi [] []
  | inject_list_cons (v v' : val) (vl vl' : List val)
      (H1 : inject mi v v') (H2 : inject_list mi vl vl') :
      inject_list mi (v :: vl) (v' :: vl')

theorem inject_ptrofs (mi : meminj) (i : Ptrofs) :
    inject mi (Vptrofs i) (Vptrofs i) := by
  simp [Vptrofs]
  split
  · apply inject.inject_long
  · apply inject.inject_int

/-- `Vptrofs` is injective: since a `Ptrofs` value's bit-width exactly matches
    whichever of `Int`/`Int64` it gets encoded into (depending on
    `Archi.ptr64`), no information is lost by the encoding. -/
theorem Vptrofs_inj {n1 n2 : Ptrofs} (h : Vptrofs n1 = Vptrofs n2) : n1 = n2 := by
  rw [Ptrofs.eq_iff_unsigned]
  unfold Vptrofs at h
  by_cases hp : Archi.ptr64
  · simp only [hp, if_true] at h
    injection h with h'
    unfold Ptrofs.to_int64 CompCert.Int64.repr at h'
    have hb1 := Ptrofs.unsigned_range n1
    have hb2 := Ptrofs.unsigned_range n2
    rw [Ptrofs.modulus_eq_pow64 hp] at hb1 hb2
    have e : (UInt64.ofInt (Ptrofs.unsigned n1)).toNat = (UInt64.ofInt (Ptrofs.unsigned n2)).toNat := by
      rw [h']
    simp [UInt64.ofInt, UInt64.toNat_ofNat'] at e
    omega
  · simp only [hp] at h
    injection h with h'
    unfold Ptrofs.to_int CompCert.Int.repr at h'
    have hb1 := Ptrofs.unsigned_range n1
    have hb2 := Ptrofs.unsigned_range n2
    rw [Ptrofs.modulus_eq_pow32 (by simpa using hp)] at hb1 hb2
    have e : (UInt32.ofInt (Ptrofs.unsigned n1)).toNat = (UInt32.ofInt (Ptrofs.unsigned n2)).toNat := by
      rw [h']
    simp [UInt32.ofInt, UInt32.toNat_ofNat'] at e
    omega

section VAL_INJ_OPS

variable (f : meminj)

theorem load_result_inject (chunk : memory_chunk) (v1 v2 : val)
    (H : inject f v1 v2) :
    inject f (load_result chunk v1) (load_result chunk v2) := by
  cases H <;> cases chunk <;> simp only [load_result]
  -- inject_int cases
  case inject_int.Mbool i =>
    by_cases hb : is_bool (val.Vint (CompCert.Int.zero_ext 8 i))
    · simp only [norm_bool, hb, ite_true]; apply inject.inject_int
    · simp only [norm_bool, hb]; apply inject.val_inject_undef
  case inject_int.Mint8signed => apply inject.inject_int
  case inject_int.Mint8unsigned => apply inject.inject_int
  case inject_int.Mint16signed => apply inject.inject_int
  case inject_int.Mint16unsigned => apply inject.inject_int
  case inject_int.Mint32 => apply inject.inject_int
  case inject_int.Mint64 => apply inject.val_inject_undef
  case inject_int.Mfloat32 => apply inject.val_inject_undef
  case inject_int.Mfloat64 => apply inject.val_inject_undef
  case inject_int.Many32 => apply inject.inject_int
  case inject_int.Many64 => apply inject.inject_int
  -- inject_long cases
  case inject_long.Mbool => apply inject.val_inject_undef
  case inject_long.Mint8signed => apply inject.val_inject_undef
  case inject_long.Mint8unsigned => apply inject.val_inject_undef
  case inject_long.Mint16signed => apply inject.val_inject_undef
  case inject_long.Mint16unsigned => apply inject.val_inject_undef
  case inject_long.Mint32 => apply inject.val_inject_undef
  case inject_long.Mint64 => apply inject.inject_long
  case inject_long.Mfloat32 => apply inject.val_inject_undef
  case inject_long.Mfloat64 => apply inject.val_inject_undef
  case inject_long.Many32 => apply inject.val_inject_undef
  case inject_long.Many64 => apply inject.inject_long
  -- inject_float cases
  case inject_float.Mbool => apply inject.val_inject_undef
  case inject_float.Mint8signed => apply inject.val_inject_undef
  case inject_float.Mint8unsigned => apply inject.val_inject_undef
  case inject_float.Mint16signed => apply inject.val_inject_undef
  case inject_float.Mint16unsigned => apply inject.val_inject_undef
  case inject_float.Mint32 => apply inject.val_inject_undef
  case inject_float.Mint64 => apply inject.val_inject_undef
  case inject_float.Mfloat32 => apply inject.val_inject_undef
  case inject_float.Mfloat64 => apply inject.inject_float
  case inject_float.Many32 => apply inject.val_inject_undef
  case inject_float.Many64 => apply inject.inject_float
  -- inject_single cases
  case inject_single.Mbool => apply inject.val_inject_undef
  case inject_single.Mint8signed => apply inject.val_inject_undef
  case inject_single.Mint8unsigned => apply inject.val_inject_undef
  case inject_single.Mint16signed => apply inject.val_inject_undef
  case inject_single.Mint16unsigned => apply inject.val_inject_undef
  case inject_single.Mint32 => apply inject.val_inject_undef
  case inject_single.Mint64 => apply inject.val_inject_undef
  case inject_single.Mfloat32 => apply inject.inject_single
  case inject_single.Mfloat64 => apply inject.val_inject_undef
  case inject_single.Many32 => apply inject.inject_single
  case inject_single.Many64 => apply inject.inject_single
  -- inject_ptr cases
  case inject_ptr.Mbool => apply inject.val_inject_undef
  case inject_ptr.Mint8signed => apply inject.val_inject_undef
  case inject_ptr.Mint8unsigned => apply inject.val_inject_undef
  case inject_ptr.Mint16signed => apply inject.val_inject_undef
  case inject_ptr.Mint16unsigned => apply inject.val_inject_undef
  case inject_ptr.Mint32 b1 ofs1 b2 ofs2 delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]; apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
  case inject_ptr.Mint64 b1 ofs1 b2 ofs2 delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
    · simp [hp]; apply inject.val_inject_undef
  case inject_ptr.Mfloat32 => apply inject.val_inject_undef
  case inject_ptr.Mfloat64 => apply inject.val_inject_undef
  case inject_ptr.Many32 b1 ofs1 b2 ofs2 delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]; apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
  case inject_ptr.Many64 b1 ofs1 b2 ofs2 delta H1 H2 =>
    apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
  -- val_inject_undef cases
  all_goals apply inject.val_inject_undef

theorem add_inject (v1 v1' v2 v2' : val)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2') :
    inject f (add v1 v2) (add v1' v2') := by
  cases H1 <;> cases H2 <;> simp only [add]
  -- Vint + Vint
  case inject_int.inject_int => apply inject.inject_int
  -- Vint + Vlong
  case inject_int.inject_long => apply inject.val_inject_undef
  -- Vint + Vfloat
  case inject_int.inject_float => apply inject.val_inject_undef
  -- Vint + Vsingle
  case inject_int.inject_single => apply inject.val_inject_undef
  -- Vint + Vptr (b2 ofs2 injected to b2' ofs2')
  case inject_int.inject_ptr i b2 ofs2 b2' ofs2' delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]
      apply inject.inject_ptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int i)) b2' (Ptrofs.add ofs2' (Ptrofs.of_int i)) delta H1
      subst H2
      rw [Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int i), ← Ptrofs.add_assoc]
  -- Vint + Vundef
  case inject_int.val_inject_undef => apply inject.val_inject_undef
  -- Vlong + Vint
  case inject_long.inject_int => apply inject.val_inject_undef
  -- Vlong + Vlong
  case inject_long.inject_long => apply inject.val_inject_undef
  -- Vlong + Vfloat
  case inject_long.inject_float => apply inject.val_inject_undef
  -- Vlong + Vsingle
  case inject_long.inject_single => apply inject.val_inject_undef
  -- Vlong + Vptr
  case inject_long.inject_ptr => apply inject.val_inject_undef
  -- Vlong + Vundef
  case inject_long.val_inject_undef => apply inject.val_inject_undef
  -- Vfloat + *
  case inject_float.inject_int => apply inject.val_inject_undef
  case inject_float.inject_long => apply inject.val_inject_undef
  case inject_float.inject_float => apply inject.val_inject_undef
  case inject_float.inject_single => apply inject.val_inject_undef
  case inject_float.inject_ptr => apply inject.val_inject_undef
  case inject_float.val_inject_undef => apply inject.val_inject_undef
  -- Vsingle + *
  case inject_single.inject_int => apply inject.val_inject_undef
  case inject_single.inject_long => apply inject.val_inject_undef
  case inject_single.inject_float => apply inject.val_inject_undef
  case inject_single.inject_single => apply inject.val_inject_undef
  case inject_single.inject_ptr => apply inject.val_inject_undef
  case inject_single.val_inject_undef => apply inject.val_inject_undef
  -- Vptr + Vint
  case inject_ptr.inject_int b1 ofs1 b1' ofs1' delta H1 H2 i =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]
      apply inject.inject_ptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int i)) b1' (Ptrofs.add ofs1' (Ptrofs.of_int i)) delta H1
      subst H2
      rw [Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int i), ← Ptrofs.add_assoc]
  -- Vptr + Vlong
  case inject_ptr.inject_long => apply inject.val_inject_undef
  -- Vptr + Vfloat
  case inject_ptr.inject_float => apply inject.val_inject_undef
  -- Vptr + Vsingle
  case inject_ptr.inject_single => apply inject.val_inject_undef
  -- Vptr + Vptr
  case inject_ptr.inject_ptr => apply inject.val_inject_undef
  -- Vptr + Vundef
  case inject_ptr.val_inject_undef => apply inject.val_inject_undef
  -- Vundef + *
  case val_inject_undef.inject_int => apply inject.val_inject_undef
  case val_inject_undef.inject_long => apply inject.val_inject_undef
  case val_inject_undef.inject_float => apply inject.val_inject_undef
  case val_inject_undef.inject_single => apply inject.val_inject_undef
  case val_inject_undef.inject_ptr => apply inject.val_inject_undef
  case val_inject_undef.val_inject_undef => apply inject.val_inject_undef

theorem sub_inject (v1 v1' v2 v2' : val)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2') :
    inject f (sub v1 v2) (sub v1' v2') := by
  cases H1 <;> cases H2 <;> simp only [sub]
  case inject_int.inject_int i j => apply inject.inject_int
  -- Vptr - Vint : shifted pointer
  case inject_ptr.inject_int b1 ofs1 b1' ofs1' delta H1 H2 n =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]
      apply inject.inject_ptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int n)) b1'
        (Ptrofs.sub ofs1' (Ptrofs.of_int n)) delta H1
      subst H2
      rw [Ptrofs.sub_add_l ofs1 (Ptrofs.of_int n) delta]
  -- Vptr - Vptr
  case inject_ptr.inject_ptr b1 ofs1 b1' ofs1' d1 H1a H1b b2 ofs2 b2' ofs2' d2 H2a H2b =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp only [hp, Bool.false_eq_true, if_false]
      by_cases hb : b1 == b2
      · -- same source block ⇒ same target block & delta
        have hbeq : b1 = b2 := by simpa using hb
        subst hbeq
        rw [H1a] at H2a
        obtain ⟨hb', hd'⟩ := Prod.mk.injEq .. ▸ (Option.some.injEq .. ▸ H2a)
        subst hb'; subst hd'
        subst H1b; subst H2b
        simp only [hb, if_true, beq_self_eq_true]
        rw [Ptrofs.sub_add_cancel]
        apply inject.inject_int
      · simp only [hb]
        apply inject.val_inject_undef
  all_goals apply inject.val_inject_undef

theorem addl_inject (v1 v1' v2 v2' : val)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2') :
    inject f (addl v1 v2) (addl v1' v2') := by
  cases H1 <;> cases H2 <;> simp only [addl]
  -- Vint + Vint
  case inject_int.inject_int => apply inject.val_inject_undef
  -- Vint + Vlong
  case inject_int.inject_long => apply inject.val_inject_undef
  -- Vint + Vfloat
  case inject_int.inject_float => apply inject.val_inject_undef
  -- Vint + Vsingle
  case inject_int.inject_single => apply inject.val_inject_undef
  -- Vint + Vptr
  case inject_int.inject_ptr => apply inject.val_inject_undef
  -- Vint + Vundef
  case inject_int.val_inject_undef => apply inject.val_inject_undef
  -- Vlong + Vint
  case inject_long.inject_int => apply inject.val_inject_undef
  -- Vlong + Vlong
  case inject_long.inject_long => apply inject.inject_long
  -- Vlong + Vfloat
  case inject_long.inject_float => apply inject.val_inject_undef
  -- Vlong + Vsingle
  case inject_long.inject_single => apply inject.val_inject_undef
  -- Vlong + Vptr (b2 ofs2 injected to b2' ofs2')
  case inject_long.inject_ptr i b2 ofs2 b2' ofs2' delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]
      apply inject.inject_ptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 i)) b2' (Ptrofs.add ofs2' (Ptrofs.of_int64 i)) delta H1
      subst H2
      rw [Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 i), ← Ptrofs.add_assoc]
    · simp [hp]; apply inject.val_inject_undef
  -- Vlong + Vundef
  case inject_long.val_inject_undef => apply inject.val_inject_undef
  -- Vfloat + *
  case inject_float.inject_int => apply inject.val_inject_undef
  case inject_float.inject_long => apply inject.val_inject_undef
  case inject_float.inject_float => apply inject.val_inject_undef
  case inject_float.inject_single => apply inject.val_inject_undef
  case inject_float.inject_ptr => apply inject.val_inject_undef
  case inject_float.val_inject_undef => apply inject.val_inject_undef
  -- Vsingle + *
  case inject_single.inject_int => apply inject.val_inject_undef
  case inject_single.inject_long => apply inject.val_inject_undef
  case inject_single.inject_float => apply inject.val_inject_undef
  case inject_single.inject_single => apply inject.val_inject_undef
  case inject_single.inject_ptr => apply inject.val_inject_undef
  case inject_single.val_inject_undef => apply inject.val_inject_undef
  -- Vptr + Vint
  case inject_ptr.inject_int => apply inject.val_inject_undef
  -- Vptr + Vlong
  case inject_ptr.inject_long b1 ofs1 b1' ofs1' delta H1 H2 i =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]
      apply inject.inject_ptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int64 i)) b1' (Ptrofs.add ofs1' (Ptrofs.of_int64 i)) delta H1
      subst H2
      rw [Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta) (Ptrofs.of_int64 i), ← Ptrofs.add_assoc]
    · simp [hp]; apply inject.val_inject_undef
  -- Vptr + Vfloat
  case inject_ptr.inject_float => apply inject.val_inject_undef
  -- Vptr + Vsingle
  case inject_ptr.inject_single => apply inject.val_inject_undef
  -- Vptr + Vptr
  case inject_ptr.inject_ptr => apply inject.val_inject_undef
  -- Vptr + Vundef
  case inject_ptr.val_inject_undef => apply inject.val_inject_undef
  -- Vundef + *
  case val_inject_undef.inject_int => apply inject.val_inject_undef
  case val_inject_undef.inject_long => apply inject.val_inject_undef
  case val_inject_undef.inject_float => apply inject.val_inject_undef
  case val_inject_undef.inject_single => apply inject.val_inject_undef
  case val_inject_undef.inject_ptr => apply inject.val_inject_undef
  case val_inject_undef.val_inject_undef => apply inject.val_inject_undef

theorem subl_inject (v1 v1' v2 v2' : val)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2') :
    inject f (subl v1 v2) (subl v1' v2') := by
  cases H1 <;> cases H2 <;> simp only [subl]
  case inject_long.inject_long i j => apply inject.inject_long
  -- Vptr - Vlong : shifted pointer (active when ptr64 = true)
  case inject_ptr.inject_long b1 ofs1 b1' ofs1' delta H1 H2 n =>
    by_cases hp : Archi.ptr64 = true
    · simp only [hp, if_true]
      apply inject.inject_ptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int64 n)) b1'
        (Ptrofs.sub ofs1' (Ptrofs.of_int64 n)) delta H1
      subst H2
      rw [Ptrofs.sub_add_l ofs1 (Ptrofs.of_int64 n) delta]
    · simp only [hp, Bool.false_eq_true, if_false]; apply inject.val_inject_undef
  -- Vptr - Vptr
  case inject_ptr.inject_ptr b1 ofs1 b1' ofs1' d1 H1a H1b b2 ofs2 b2' ofs2' d2 H2a H2b =>
    by_cases hp : Archi.ptr64 = true
    · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false]
      by_cases hb : b1 == b2
      · have hbeq : b1 = b2 := by simpa using hb
        subst hbeq
        rw [H1a] at H2a
        have hpair : (b1', d1) = (b2', d2) := Option.some.inj H2a
        have hb' : b1' = b2' := congrArg Prod.fst hpair
        have hd' : d1 = d2 := congrArg Prod.snd hpair
        subst hb'; subst hd'
        subst H1b; subst H2b
        simp only [hb, if_true, beq_self_eq_true]
        rw [Ptrofs.sub_add_cancel]
        apply inject.inject_long
      · simp only [hb]
        apply inject.val_inject_undef
    · simp only [hp, Bool.not_false, if_true]; apply inject.val_inject_undef
  all_goals apply inject.val_inject_undef

theorem offset_ptr_inject (v v' : val) (ofs : Ptrofs)
    (H : inject f v v') :
    inject f (offset_ptr v ofs) (offset_ptr v' ofs) := by
  cases H <;> simp only [offset_ptr]
  case inject_ptr b1 ofs1 b2 ofs2 delta H1 H2 =>
    apply inject.inject_ptr b1 (Ptrofs.add ofs1 ofs) b2 (Ptrofs.add ofs2 ofs) delta H1
    subst H2
    rw [Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta) ofs, ← Ptrofs.add_assoc]
  all_goals apply inject.val_inject_undef

theorem cmp_bool_inject (c : comparison) (v1 v2 v1' v2' : val) (b : Bool)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2')
    (H3 : cmp_bool c v1 v2 = some b) :
    cmp_bool c v1' v2' = some b := by
  cases H1 <;> cases H2 <;> simp [cmp_bool] at H3 ⊢
  case inject_int.inject_int => exact H3

variable (valid_ptr1 valid_ptr2 : block → Int → Bool)

def weak_valid_ptr1 (b : block) (ofs : Int) : Bool :=
  valid_ptr1 b ofs || valid_ptr1 b (ofs - 1)

def weak_valid_ptr2 (b : block) (ofs : Int) : Bool :=
  valid_ptr2 b ofs || valid_ptr2 b (ofs - 1)

variable (valid_ptr_inj : ∀ b1 (ofs : Ptrofs) b2 delta,
  f b1 = some (b2, delta) →
  valid_ptr1 b1 ofs.unsigned = true →
  valid_ptr2 b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned = true)

variable (weak_valid_ptr_inj : ∀ b1 (ofs : Ptrofs) b2 delta,
  f b1 = some (b2, delta) →
  (valid_ptr1 b1 ofs.unsigned || valid_ptr1 b1 (ofs.unsigned - 1)) = true →
  (valid_ptr2 b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned ||
   valid_ptr2 b2 ((Ptrofs.add ofs (Ptrofs.repr delta)).unsigned - 1)) = true)

variable (weak_valid_ptr_no_overflow : ∀ b1 (ofs : Ptrofs) b2 delta,
  f b1 = some (b2, delta) →
  (valid_ptr1 b1 ofs.unsigned || valid_ptr1 b1 (ofs.unsigned - 1)) = true →
  0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
  Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)

variable (valid_different_ptrs_inj : ∀ b1 (ofs1 : Ptrofs) b2 (ofs2 : Ptrofs) b1' delta1 b2' delta2,
  b1 ≠ b2 →
  valid_ptr1 b1 ofs1.unsigned = true →
  valid_ptr1 b2 ofs2.unsigned = true →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' ≠ b2' ∨
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))

theorem cmpu_bool_inject
    (valid_ptr_inj : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      valid_ptr1 b1 ofs.unsigned = true →
      valid_ptr2 b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned = true)
    (weak_valid_ptr_inj : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      (valid_ptr1 b1 ofs.unsigned || valid_ptr1 b1 (ofs.unsigned - 1)) = true →
      (valid_ptr2 b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned ||
       valid_ptr2 b2 ((Ptrofs.add ofs (Ptrofs.repr delta)).unsigned - 1)) = true)
    (weak_valid_ptr_no_overflow : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      (valid_ptr1 b1 ofs.unsigned || valid_ptr1 b1 (ofs.unsigned - 1)) = true →
      0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)
    (valid_different_ptrs_inj : ∀ b1 (ofs1 : Ptrofs) b2 (ofs2 : Ptrofs) b1' delta1 b2' delta2,
      b1 ≠ b2 →
      valid_ptr1 b1 ofs1.unsigned = true →
      valid_ptr1 b2 ofs2.unsigned = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
      Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))
    (c : comparison) (v1 v2 v1' v2' : val) (bresult : Bool)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2')
    (H3 : cmpu_bool valid_ptr1 c v1 v2 = some bresult) :
    cmpu_bool valid_ptr2 c v1' v2' = some bresult := by
  cases H1 with
  | inject_int i =>
    cases H2 with
    | inject_int j =>
      -- Vint, Vint: comparison result is identical
      simp only [cmpu_bool] at H3 ⊢
      exact H3
    | inject_ptr blk2 ofs2 blk2' ofs2' delta2 hf2 ho2 =>
      -- Vint, Vptr: requires ptr64=false, i=0, weak_valid_ptr
      simp only [cmpu_bool, weak_valid_ptr] at H3 ⊢
      split at H3
      · contradiction
      · rename_i hp64
        obtain ⟨hcond, H3⟩ := Option.ite_none_right_eq_some.mp H3
        have ⟨hi0, hwvp⟩ := Bool.and_eq_true_iff.mp hcond
        -- Apply weak_valid_ptr_inj
        have hwvp2' := weak_valid_ptr_inj blk2 ofs2 blk2' delta2 hf2 hwvp
        subst ho2
        simp only [hp64, hi0, hwvp2', Bool.true_and]
        exact H3
    | val_inject_undef =>
      simp only [cmpu_bool] at H3
      contradiction
    | _ =>
      simp only [cmpu_bool] at H3
      contradiction
  | inject_ptr blk1 ofs1 blk1' ofs1' delta1 hf1 ho1 =>
    cases H2 with
    | inject_int j =>
      -- Vptr, Vint: symmetric to Vint, Vptr
      simp only [cmpu_bool, weak_valid_ptr] at H3 ⊢
      split at H3
      · contradiction
      · rename_i hp64
        obtain ⟨hcond, H3⟩ := Option.ite_none_right_eq_some.mp H3
        have ⟨hj0, hwvp⟩ := Bool.and_eq_true_iff.mp hcond
        have hwvp2' := weak_valid_ptr_inj blk1 ofs1 blk1' delta1 hf1 hwvp
        subst ho1
        simp only [hp64, hj0, hwvp2', Bool.true_and]
        exact H3
    | inject_ptr blk2 ofs2 blk2' ofs2' delta2 hf2 ho2 =>
      -- Vptr, Vptr: the hard case
      simp only [cmpu_bool, weak_valid_ptr] at H3 ⊢
      split at H3
      · contradiction
      · rename_i hp64
        -- Split on whether blk1 == blk2
        by_cases hbeq : blk1 == blk2
        · -- Same source block
          have hb1b2 : blk1 = blk2 := by simpa using hbeq
          subst hb1b2
          -- f blk2 maps to same target block with same delta
          rw [hf1] at hf2
          have hpair : (blk1', delta1) = (blk2', delta2) := Option.some.inj hf2
          have hb' : blk1' = blk2' := congrArg Prod.fst hpair
          have hd' : delta1 = delta2 := congrArg Prod.snd hpair
          subst hb'; subst hd'
          simp only [hbeq, ite_true, beq_self_eq_true] at H3 ⊢
          obtain ⟨hwvp, H3⟩ := Option.ite_none_right_eq_some.mp H3
          have ⟨hwvp1, hwvp2⟩ := Bool.and_eq_true_iff.mp hwvp
          have hwvp1'' := weak_valid_ptr_inj blk1 ofs1 blk1' delta1 hf1 hwvp1
          have hwvp2'' := weak_valid_ptr_inj blk1 ofs2 blk1' delta1 hf1 hwvp2
          subst ho1; subst ho2
          simp only [hp64, ite_true, hwvp1'', hwvp2'', Bool.true_and]
          have hno1 := weak_valid_ptr_no_overflow blk1 ofs1 blk1' delta1 hf1 hwvp1
          have hno2 := weak_valid_ptr_no_overflow blk1 ofs2 blk1' delta1 hf1 hwvp2
          have hrepr : Ptrofs.repr (Ptrofs.repr delta1).unsigned = Ptrofs.repr delta1 :=
            Ptrofs.repr_unsigned _
          rw [← hrepr, Ptrofs.cmpu_add_shift c ofs1 ofs2 (Ptrofs.repr delta1).unsigned hno1 hno2]
          exact H3
        · -- Different source blocks
          have hp64_false : Archi.ptr64 = false := by
            cases h : Archi.ptr64
            · rfl
            · rw [h] at hp64; exact absurd rfl hp64
          have hbeq_false : (blk1 == blk2) = false := by
            cases h : (blk1 == blk2)
            · rfl
            · rw [h] at hbeq; exact absurd rfl hbeq
          have hb1ne : blk1 ≠ blk2 := by simpa using hbeq
          -- reduce H3 fully to `cmp_different_blocks c = some bresult` (guard must hold)
          simp only [hbeq_false, if_false, Bool.false_eq_true] at H3
          by_cases hvp : (valid_ptr1 blk1 ofs1.unsigned && valid_ptr1 blk2 ofs2.unsigned) = true
          · rw [if_pos hvp] at H3
            have ⟨hvp1, hvp2⟩ := Bool.and_eq_true_iff.mp hvp
            have hvp1' : valid_ptr2 blk1' ofs1'.unsigned = true := by
              rw [ho1]; exact valid_ptr_inj blk1 ofs1 blk1' delta1 hf1 hvp1
            have hvp2' : valid_ptr2 blk2' ofs2'.unsigned = true := by
              rw [ho2]; exact valid_ptr_inj blk2 ofs2 blk2' delta2 hf2 hvp2
            have hdiff : blk1' ≠ blk2' ∨ ofs1' ≠ ofs2' := by
              rw [ho1, ho2]
              rcases valid_different_ptrs_inj blk1 ofs1 blk2 ofs2 blk1' delta1 blk2' delta2
                  hb1ne hvp1 hvp2 hf1 hf2 with h | h
              · exact Or.inl h
              · exact Or.inr (fun heq => h (congrArg Ptrofs.unsigned heq))
            have hwv1 : weak_valid_ptr valid_ptr2 blk1' ofs1' = true := by
              unfold weak_valid_ptr; rw [hvp1']; rfl
            have hwv2 : weak_valid_ptr valid_ptr2 blk2' ofs2' = true := by
              unfold weak_valid_ptr; rw [hvp2']; rfl
            -- reduce the goal
            simp only [hp64_false, if_false, Bool.false_eq_true]
            by_cases hbeq' : blk1' == blk2'
            · have hb'eq : blk1' = blk2' := by simpa using hbeq'
              have hoff_ne : ofs1' ≠ ofs2' := by
                rcases hdiff with hbd | hod
                · exact absurd hb'eq hbd
                · exact hod
              subst hb'eq
              simp only [beq_self_eq_true, if_true, hvp1', hvp2', Bool.true_or, Bool.and_self]
              -- H3 : cmp_different_blocks c = some bresult; only Ceq/Cne give some
              cases c
              · -- Ceq
                simp only [cmp_different_blocks] at H3
                have hbr : bresult = false := by injection H3 with h; exact h.symm
                have hc : Ptrofs.cmpu .Ceq ofs1' ofs2' = false := by
                  unfold Ptrofs.cmpu
                  simp only [beq_eq_false_iff_ne, ne_eq]
                  intro hu; exact hoff_ne ((Ptrofs.eq_iff_unsigned).mpr hu)
                rw [hc, hbr]
              · -- Cne
                simp only [cmp_different_blocks] at H3
                have hbr : bresult = true := by injection H3 with h; exact h.symm
                have hc : Ptrofs.cmpu .Cne ofs1' ofs2' = true := by
                  unfold Ptrofs.cmpu
                  simp only [bne_iff_ne, ne_eq]
                  intro hu; exact hoff_ne ((Ptrofs.eq_iff_unsigned).mpr hu)
                rw [hc, hbr]
              · exact absurd H3 (by simp [cmp_different_blocks])
              · exact absurd H3 (by simp [cmp_different_blocks])
              · exact absurd H3 (by simp [cmp_different_blocks])
              · exact absurd H3 (by simp [cmp_different_blocks])
            · have hbeq'_false : (blk1' == blk2') = false := by
                cases h : (blk1' == blk2')
                · rfl
                · rw [h] at hbeq'; exact absurd rfl hbeq'
              simp only [hbeq'_false, hvp1', hvp2', Bool.and_self]
              exact H3
          · rw [if_neg hvp] at H3
            exact absurd H3 (by simp)
    | val_inject_undef =>
      simp only [cmpu_bool] at H3
      contradiction
    | _ =>
      simp only [cmpu_bool] at H3
      contradiction
  | val_inject_undef =>
    simp only [cmpu_bool] at H3
    contradiction
  | _ =>
    simp only [cmpu_bool] at H3
    contradiction

theorem cmplu_bool_inject
    (valid_ptr_inj : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      valid_ptr1 b1 ofs.unsigned = true →
      valid_ptr2 b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned = true)
    (weak_valid_ptr_inj : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      (valid_ptr1 b1 ofs.unsigned || valid_ptr1 b1 (ofs.unsigned - 1)) = true →
      (valid_ptr2 b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned ||
       valid_ptr2 b2 ((Ptrofs.add ofs (Ptrofs.repr delta)).unsigned - 1)) = true)
    (weak_valid_ptr_no_overflow : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      (valid_ptr1 b1 ofs.unsigned || valid_ptr1 b1 (ofs.unsigned - 1)) = true →
      0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)
    (valid_different_ptrs_inj : ∀ b1 (ofs1 : Ptrofs) b2 (ofs2 : Ptrofs) b1' delta1 b2' delta2,
      b1 ≠ b2 →
      valid_ptr1 b1 ofs1.unsigned = true →
      valid_ptr1 b2 ofs2.unsigned = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
      Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))
    (c : comparison) (v1 v2 v1' v2' : val) (bresult : Bool)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2')
    (H3 : cmplu_bool valid_ptr1 c v1 v2 = some bresult) :
    cmplu_bool valid_ptr2 c v1' v2' = some bresult := by
  cases H1 with
  | inject_long i =>
    cases H2 with
    | inject_long j =>
      simp only [cmplu_bool] at H3 ⊢
      exact H3
    | inject_ptr blk2 ofs2 blk2' ofs2' delta2 hf2 ho2 =>
      simp only [cmplu_bool, weak_valid_ptr] at H3 ⊢
      split at H3
      · contradiction
      · rename_i hp64
        obtain ⟨hcond, H3⟩ := Option.ite_none_right_eq_some.mp H3
        have ⟨hi0, hwvp⟩ := Bool.and_eq_true_iff.mp hcond
        have hwvp2' := weak_valid_ptr_inj blk2 ofs2 blk2' delta2 hf2 hwvp
        subst ho2
        simp only [hp64, hi0, hwvp2', Bool.true_and]
        exact H3
    | val_inject_undef =>
      simp only [cmplu_bool] at H3
      contradiction
    | _ =>
      simp only [cmplu_bool] at H3
      contradiction
  | inject_ptr blk1 ofs1 blk1' ofs1' delta1 hf1 ho1 =>
    cases H2 with
    | inject_long j =>
      simp only [cmplu_bool, weak_valid_ptr] at H3 ⊢
      split at H3
      · contradiction
      · rename_i hp64
        obtain ⟨hcond, H3⟩ := Option.ite_none_right_eq_some.mp H3
        have ⟨hj0, hwvp⟩ := Bool.and_eq_true_iff.mp hcond
        have hwvp2' := weak_valid_ptr_inj blk1 ofs1 blk1' delta1 hf1 hwvp
        subst ho1
        simp only [hp64, hj0, hwvp2', Bool.true_and]
        exact H3
    | inject_ptr blk2 ofs2 blk2' ofs2' delta2 hf2 ho2 =>
      simp only [cmplu_bool, weak_valid_ptr] at H3 ⊢
      split at H3
      · contradiction
      · rename_i hp64
        by_cases hbeq : blk1 == blk2
        · have hb1b2 : blk1 = blk2 := by simpa using hbeq
          subst hb1b2
          rw [hf1] at hf2
          have hpair : (blk1', delta1) = (blk2', delta2) := Option.some.inj hf2
          have hb' : blk1' = blk2' := congrArg Prod.fst hpair
          have hd' : delta1 = delta2 := congrArg Prod.snd hpair
          subst hb'; subst hd'
          simp only [hbeq, ite_true, beq_self_eq_true] at H3 ⊢
          obtain ⟨hwvp, H3⟩ := Option.ite_none_right_eq_some.mp H3
          have ⟨hwvp1, hwvp2⟩ := Bool.and_eq_true_iff.mp hwvp
          have hwvp1'' := weak_valid_ptr_inj blk1 ofs1 blk1' delta1 hf1 hwvp1
          have hwvp2'' := weak_valid_ptr_inj blk1 ofs2 blk1' delta1 hf1 hwvp2
          subst ho1; subst ho2
          simp only [hp64, ite_true, hwvp1'', hwvp2'', Bool.true_and]
          have hno1 := weak_valid_ptr_no_overflow blk1 ofs1 blk1' delta1 hf1 hwvp1
          have hno2 := weak_valid_ptr_no_overflow blk1 ofs2 blk1' delta1 hf1 hwvp2
          have hrepr : Ptrofs.repr (Ptrofs.repr delta1).unsigned = Ptrofs.repr delta1 :=
            Ptrofs.repr_unsigned _
          rw [← hrepr, Ptrofs.cmpu_add_shift c ofs1 ofs2 (Ptrofs.repr delta1).unsigned hno1 hno2]
          exact H3
        · have hp64_true : Archi.ptr64 = true := by
            cases h : Archi.ptr64
            · rw [h] at hp64; simp at hp64
            · rfl
          have hbeq_false : (blk1 == blk2) = false := by
            cases h : (blk1 == blk2)
            · rfl
            · rw [h] at hbeq; exact absurd rfl hbeq
          have hb1ne : blk1 ≠ blk2 := by simpa using hbeq
          simp only [hbeq_false, if_false, Bool.false_eq_true] at H3
          by_cases hvp : (valid_ptr1 blk1 ofs1.unsigned && valid_ptr1 blk2 ofs2.unsigned) = true
          · rw [if_pos hvp] at H3
            have ⟨hvp1, hvp2⟩ := Bool.and_eq_true_iff.mp hvp
            have hvp1' : valid_ptr2 blk1' ofs1'.unsigned = true := by
              rw [ho1]; exact valid_ptr_inj blk1 ofs1 blk1' delta1 hf1 hvp1
            have hvp2' : valid_ptr2 blk2' ofs2'.unsigned = true := by
              rw [ho2]; exact valid_ptr_inj blk2 ofs2 blk2' delta2 hf2 hvp2
            have hdiff : blk1' ≠ blk2' ∨ ofs1' ≠ ofs2' := by
              rw [ho1, ho2]
              rcases valid_different_ptrs_inj blk1 ofs1 blk2 ofs2 blk1' delta1 blk2' delta2
                  hb1ne hvp1 hvp2 hf1 hf2 with h | h
              · exact Or.inl h
              · exact Or.inr (fun heq => h (congrArg Ptrofs.unsigned heq))
            simp only [hp64_true, Bool.not_true, if_false, Bool.false_eq_true]
            by_cases hbeq' : blk1' == blk2'
            · have hb'eq : blk1' = blk2' := by simpa using hbeq'
              have hoff_ne : ofs1' ≠ ofs2' := by
                rcases hdiff with hbd | hod
                · exact absurd hb'eq hbd
                · exact hod
              subst hb'eq
              simp only [beq_self_eq_true, if_true, hvp1', hvp2', Bool.true_or, Bool.and_self]
              cases c
              · simp only [cmp_different_blocks] at H3
                have hbr : bresult = false := by injection H3 with h; exact h.symm
                have hc : Ptrofs.cmpu .Ceq ofs1' ofs2' = false := by
                  unfold Ptrofs.cmpu
                  simp only [beq_eq_false_iff_ne, ne_eq]
                  intro hu; exact hoff_ne ((Ptrofs.eq_iff_unsigned).mpr hu)
                rw [hc, hbr]
              · simp only [cmp_different_blocks] at H3
                have hbr : bresult = true := by injection H3 with h; exact h.symm
                have hc : Ptrofs.cmpu .Cne ofs1' ofs2' = true := by
                  unfold Ptrofs.cmpu
                  simp only [bne_iff_ne, ne_eq]
                  intro hu; exact hoff_ne ((Ptrofs.eq_iff_unsigned).mpr hu)
                rw [hc, hbr]
              · exact absurd H3 (by simp [cmp_different_blocks])
              · exact absurd H3 (by simp [cmp_different_blocks])
              · exact absurd H3 (by simp [cmp_different_blocks])
              · exact absurd H3 (by simp [cmp_different_blocks])
            · have hbeq'_false : (blk1' == blk2') = false := by
                cases h : (blk1' == blk2')
                · rfl
                · rw [h] at hbeq'; exact absurd rfl hbeq'
              simp only [hbeq'_false, hvp1', hvp2', Bool.and_self]
              exact H3
          · rw [if_neg hvp] at H3
            exact absurd H3 (by simp)
    | val_inject_undef =>
      simp only [cmplu_bool] at H3
      contradiction
    | _ =>
      simp only [cmplu_bool] at H3
      contradiction
  | val_inject_undef =>
    simp only [cmplu_bool] at H3
    contradiction
  | _ =>
    simp only [cmplu_bool] at H3
    contradiction

theorem longofwords_inject (v1 v2 v1' v2' : val)
    (H1 : inject f v1 v1') (H2 : inject f v2 v2') :
    inject f (longofwords v1 v2) (longofwords v1' v2') := by
  cases H1 with
  | inject_int i1 =>
    cases H2 with
    | inject_int i2 =>
      simp only [longofwords]
      exact inject.inject_long _
    | _ => simp only [longofwords]; exact inject.val_inject_undef _
  | _ =>
    cases H2 <;> simp only [longofwords] <;> exact inject.val_inject_undef _

theorem loword_inject (v v' : val)
    (H : inject f v v') :
    inject f (loword v) (loword v') := by
  cases H with
  | inject_long i =>
    simp only [loword]
    exact inject.inject_int _
  | _ =>
    simp only [loword]
    exact inject.val_inject_undef _

theorem hiword_inject (v v' : val)
    (H : inject f v v') :
    inject f (hiword v) (hiword v') := by
  cases H with
  | inject_long i =>
    simp only [hiword]
    exact inject.inject_int _
  | _ =>
    simp only [hiword]
    exact inject.val_inject_undef _

theorem normalize_inject (v v' : val) (ty : typ)
    (H : inject f v v') :
    inject f (normalize v ty) (normalize v' ty) := by
  cases H <;> cases ty <;> simp only [normalize]
  -- inject_int cases
  case inject_int.Tint => apply inject.inject_int
  case inject_int.Tlong => apply inject.val_inject_undef
  case inject_int.Tfloat => apply inject.val_inject_undef
  case inject_int.Tsingle => apply inject.val_inject_undef
  case inject_int.Tany32 => apply inject.inject_int
  case inject_int.Tany64 => apply inject.inject_int
  -- inject_long cases
  case inject_long.Tint => apply inject.val_inject_undef
  case inject_long.Tlong => apply inject.inject_long
  case inject_long.Tfloat => apply inject.val_inject_undef
  case inject_long.Tsingle => apply inject.val_inject_undef
  case inject_long.Tany32 => apply inject.val_inject_undef
  case inject_long.Tany64 => apply inject.inject_long
  -- inject_float cases
  case inject_float.Tint => apply inject.val_inject_undef
  case inject_float.Tlong => apply inject.val_inject_undef
  case inject_float.Tfloat => apply inject.inject_float
  case inject_float.Tsingle => apply inject.val_inject_undef
  case inject_float.Tany32 => apply inject.val_inject_undef
  case inject_float.Tany64 => apply inject.inject_float
  -- inject_single cases
  case inject_single.Tint => apply inject.val_inject_undef
  case inject_single.Tlong => apply inject.val_inject_undef
  case inject_single.Tfloat => apply inject.val_inject_undef
  case inject_single.Tsingle => apply inject.inject_single
  case inject_single.Tany32 => apply inject.inject_single
  case inject_single.Tany64 => apply inject.inject_single
  -- inject_ptr cases
  case inject_ptr.Tint b1 ofs1 b2 ofs2 delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]; apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
  case inject_ptr.Tlong b1 ofs1 b2 ofs2 delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
    · simp [hp]; apply inject.val_inject_undef
  case inject_ptr.Tfloat => apply inject.val_inject_undef
  case inject_ptr.Tsingle => apply inject.val_inject_undef
  case inject_ptr.Tany32 b1 ofs1 b2 ofs2 delta H1 H2 =>
    by_cases hp : Archi.ptr64 = true
    · simp [hp]; apply inject.val_inject_undef
    · simp [hp]; apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
  case inject_ptr.Tany64 b1 ofs1 b2 ofs2 delta H1 H2 =>
    apply inject.inject_ptr b1 ofs1 b2 ofs2 delta H1 H2
  -- val_inject_undef cases
  all_goals apply inject.val_inject_undef

theorem select_inject (ob ob' : Option Bool) (v1 v1' v2 v2' : val) (ty : typ)
    (H_ob : ob = none ∨ ob = ob')
    (H1 : inject f v1 v1') (H2 : inject f v2 v2') :
    inject f (select ob v1 v2 ty) (select ob' v1' v2' ty) := by
  cases H_ob with
  | inl h =>
    rw [h]
    simp [select]
    apply inject.val_inject_undef
  | inr h =>
    rw [h]
    cases ob' <;> simp [select]
    · apply inject.val_inject_undef
    case some b =>
      cases b <;> simp
      · exact normalize_inject f v2 v2' ty H2
      · exact normalize_inject f v1 v1' ty H1

theorem has_argtype_inject (v v' : val) (r : xtype)
    (H1 : has_argtype v r) (H2 : inject f v v') :
    has_argtype v' r := by
  cases H2 <;> cases r <;> simp [has_argtype] at H1 ⊢
  all_goals (try trivial)

theorem has_argtype_list_inject (vl vl' : List val) (rl : List xtype)
    (H1 : has_argtype_list vl rl) (H2 : inject_list f vl vl') :
    has_argtype_list vl' rl := by
  induction H2 generalizing rl with
  | inject_list_nil =>
    cases rl
    · exact H1
    · cases H1
  | inject_list_cons v v' vl vl' Hv Hvl IH =>
    cases rl with
    | nil => cases H1
    | cons r rl =>
      simp [has_argtype_list] at H1 ⊢
      constructor
      · exact has_argtype_inject f v v' r H1.1 Hv
      · exact IH rl H1.2

end VAL_INJ_OPS

end Val

/- Notation -/
notation "meminj" => Val.meminj

/- ** Monotone evolution of a memory injection -/

def inject_incr (f1 f2 : meminj) : Prop :=
  ∀ b b' delta, f1 b = some (b', delta) → f2 b = some (b', delta)

omit [Archi] in
theorem inject_incr_refl (f : meminj) :
    inject_incr f f := by
  intro b b' delta h
  exact h

omit [Archi] in
theorem inject_incr_trans (f1 f2 f3 : meminj)
    (H1 : inject_incr f1 f2) (H2 : inject_incr f2 f3) :
    inject_incr f1 f3 := by
  intro b b' delta h
  exact H2 b b' delta (H1 b b' delta h)

theorem val_inject_incr (f1 f2 : meminj) (v v' : val)
    (H1 : inject_incr f1 f2) (H2 : Val.inject f1 v v') :
    Val.inject f2 v v' := by
  cases H2
  · exact Val.inject.inject_int _
  · exact Val.inject.inject_long _
  · exact Val.inject.inject_float _
  · exact Val.inject.inject_single _
  case inject_ptr b1 ofs1 b2 ofs2 delta Hinj Hofs =>
    apply Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta
    · exact H1 b1 b2 delta Hinj
    · exact Hofs
  · exact Val.inject.val_inject_undef _

theorem val_inject_list_incr (f1 f2 : meminj) (vl vl' : List val)
    (H1 : inject_incr f1 f2) (H2 : Val.inject_list f1 vl vl') :
    Val.inject_list f2 vl vl' := by
  induction H2 with
  | inject_list_nil => exact Val.inject_list.inject_list_nil
  | inject_list_cons v v' vl vl' Hv Hvl IH =>
    apply Val.inject_list.inject_list_cons
    · exact val_inject_incr f1 f2 v v' H1 Hv
    · exact IH

theorem val_inject_lessdef (v1 v2 : val) :
    Val.lessdef v1 v2 ↔ Val.inject (fun b => some (b, 0)) v1 v2 := by
  have refl_inj : ∀ w : val, Val.inject (fun b => some (b, 0)) w w := by
    intro w
    cases w with
    | Vundef => exact Val.inject.val_inject_undef _
    | Vint i => exact Val.inject.inject_int _
    | Vlong i => exact Val.inject.inject_long _
    | Vfloat f => exact Val.inject.inject_float _
    | Vsingle f => exact Val.inject.inject_single _
    | Vptr b ofs =>
      apply Val.inject.inject_ptr b ofs b ofs 0 rfl
      rw [Ptrofs.add_commut, show Ptrofs.repr 0 = Ptrofs.zero from rfl, Ptrofs.zero_add]
  constructor
  · intro h
    cases h with
    | lessdef_refl => exact refl_inj _
    | lessdef_undef => exact Val.inject.val_inject_undef _
  · intro h
    cases h with
    | inject_int i => exact Val.lessdef.lessdef_refl _
    | inject_long i => exact Val.lessdef.lessdef_refl _
    | inject_float f => exact Val.lessdef.lessdef_refl _
    | inject_single f => exact Val.lessdef.lessdef_refl _
    | inject_ptr b1 ofs1 b2 ofs2 delta H1 H2 =>
      have hpair : (b1, (0 : Int)) = (b2, delta) := Option.some.inj H1
      have hb : b1 = b2 := congrArg Prod.fst hpair
      have hd : (0 : Int) = delta := congrArg Prod.snd hpair
      subst hb; subst hd
      rw [H2, Ptrofs.add_commut, show Ptrofs.repr 0 = Ptrofs.zero from rfl, Ptrofs.zero_add]
      exact Val.lessdef.lessdef_refl _
    | val_inject_undef v => exact Val.lessdef.lessdef_undef _

theorem val_inject_list_lessdef (vl1 vl2 : List val) :
    Val.lessdef_list vl1 vl2 ↔ Val.inject_list (fun b => some (b, 0)) vl1 vl2 := by
  constructor
  · intro h
    induction h with
    | lessdef_list_nil => exact Val.inject_list.inject_list_nil
    | lessdef_list_cons v1 v2 vl1 vl2 Hv Hvl IH =>
      apply Val.inject_list.inject_list_cons
      · exact val_inject_lessdef v1 v2 |>.mp Hv
      · exact IH
  · intro h
    induction h with
    | inject_list_nil => exact Val.lessdef_list.lessdef_list_nil
    | inject_list_cons v v' vl vl' Hv Hvl IH =>
      apply Val.lessdef_list.lessdef_list_cons
      · exact val_inject_lessdef v v' |>.mpr Hv
      · exact IH

/- ** The identity injection gives rise to the "less defined than" relation -/

def inject_id : meminj := fun b => some (b, 0)

theorem val_inject_id (v1 v2 : val) :
    Val.inject inject_id v1 v2 ↔ Val.lessdef v1 v2 := by
  unfold inject_id
  exact (val_inject_lessdef v1 v2).symm

/- ** Composing two memory injections -/

def compose_meminj (f f' : meminj) : meminj :=
  fun b =>
    match f b with
    | none => none
    | some (b', delta) =>
        match f' b' with
        | none => none
        | some (b'', delta') => some (b'', delta + delta')

theorem val_inject_compose (f f' : meminj) (v1 v2 v3 : val)
    (H1 : Val.inject f v1 v2) (H2 : Val.inject f' v2 v3) :
    Val.inject (compose_meminj f f') v1 v3 := by
  cases H1
  case inject_int i =>
    cases H2; constructor
  case inject_long i =>
    cases H2; constructor
  case inject_float f =>
    cases H2; constructor
  case inject_single f =>
    cases H2; constructor
  case inject_ptr b1 ofs1 b2 ofs2 delta1 Hinj1 Hofs1 =>
    cases H2
    case inject_ptr b3 ofs3 delta2 Hinj2 Hofs2 =>
      apply Val.inject.inject_ptr b1 ofs1 b3 ofs3 (delta1 + delta2)
      · unfold compose_meminj
        simp only [Hinj1, Hinj2]
      · rw [Hofs2, Hofs1]
        rw [Ptrofs.add_assoc, ← Ptrofs.repr_add]
  case val_inject_undef v =>
    cases H2 <;> constructor
