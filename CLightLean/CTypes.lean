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

-- Type expressions for the Compcert C and Clight languages

import CLightLean.AST
import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas

variable [Archi]

-- Syntax of types

/-
Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16, or 32 bits, or the special [IBool] size
  standing for the C99 [_Bool] type.  64-bit integers are treated separately.
-/

inductive signedness : Type where
  | Signed
  | Unsigned
  deriving DecidableEq

inductive intsize : Type where
  | I8
  | I16
  | I32
  | IBool
  deriving DecidableEq

/- Float types come in two sizes: 32 bits (single precision)
  and 64-bit (double precision). -/

inductive floatsize : Type where
  | F32
  | F64
  deriving DecidableEq

/- Every type carries a set of attributes. Currently, only two
  attributes are modeled: [volatile] and [_Alignas(n)] (from ISO C 2011). -/

structure attr : Type where
  attr_volatile : Bool
  attr_alignas: Option Nat
  deriving DecidableEq

def noattr : attr := { attr_volatile := false, attr_alignas := none}

/- The syntax of type expressions.  Some points to note:
- Array types [Tarray n] carry the size [n] of the array.
  Arrays with unknown sizes are represented by pointer types.
- Function types [Tfunction targs tres] specify the number and types
  of the function arguments (list [targs]), and the type of the
  function result ([tres]).  Variadic functions and old-style unprototyped
  functions are not supported.
-/

inductive type : Type where
  | Tvoid : type
  | Tint (i : intsize) (s : signedness) (a : attr)
  | Tlong (s : signedness) (a : attr)
  | Tfloat (f : floatsize) (a : attr)
  | Tpointer (t : type) (a : attr)
  | Tarray (t : type) (z : Int) (a : attr)
  | Tfunction (params : List type) (t : type) (c : calling_convention)
  | Tstruct (i : ident) (a : attr)
  | Tunion (i : ident) (a : attr)

mutual
  def typeDecEq (a b : type) : Decidable (a = b) := by
    cases a <;> cases b <;>
      first
      | exact isTrue rfl
      | exact isFalse type.noConfusion
      | skip
    case Tint i1 s1 at1 i2 s2 at2 =>
      exact if h : i1 = i2 ∧ s1 = s2 ∧ at1 = at2
        then isTrue (by obtain ⟨h1,h2,h3⟩ := h; subst_vars; rfl)
        else isFalse (by intro heq; injection heq with h1 h2 h3; exact h ⟨h1,h2,h3⟩)
    case Tlong s1 at1 s2 at2 =>
      exact if h : s1 = s2 ∧ at1 = at2
        then isTrue (by obtain ⟨h1,h2⟩ := h; subst_vars; rfl)
        else isFalse (by intro heq; injection heq with h1 h2; exact h ⟨h1,h2⟩)
    case Tfloat f1 at1 f2 at2 =>
      exact if h : f1 = f2 ∧ at1 = at2
        then isTrue (by obtain ⟨h1,h2⟩ := h; subst_vars; rfl)
        else isFalse (by intro heq; injection heq with h1 h2; exact h ⟨h1,h2⟩)
    case Tpointer t1 at1 t2 at2 =>
      exact match typeDecEq t1 t2 with
        | isTrue h1 =>
            if h2 : at1 = at2 then isTrue (by subst h1 h2; rfl)
            else isFalse (by intro heq; injection heq with _ h2'; exact h2 h2')
        | isFalse h1 => isFalse (by intro heq; injection heq with h1' _; exact h1 h1')
    case Tarray t1 z1 at1 t2 z2 at2 =>
      exact match typeDecEq t1 t2 with
        | isTrue h1 =>
            if h : z1 = z2 ∧ at1 = at2 then
              isTrue (by obtain ⟨h2,h3⟩ := h; subst h1 h2 h3; rfl)
            else isFalse (by intro heq; injection heq with _ h2 h3; exact h ⟨h2,h3⟩)
        | isFalse h1 => isFalse (by intro heq; injection heq with h1' _ _; exact h1 h1')
    case Tfunction ps1 t1 c1 ps2 t2 c2 =>
      exact match typeDecEq t1 t2 with
        | isTrue h1 =>
            match listTypeDecEq ps1 ps2 with
            | isTrue h2 =>
                if h3 : c1 = c2 then isTrue (by subst h1 h2 h3; rfl)
                else isFalse (by intro heq; injection heq with h2' h1' h3'; exact h3 h3')
            | isFalse h2 => isFalse (by intro heq; injection heq with h2' h1' h3'; exact h2 h2')
        | isFalse h1 => isFalse (by intro heq; injection heq with h2' h1' h3'; exact h1 h1')
    case Tstruct i1 at1 i2 at2 =>
      exact if h : i1 = i2 ∧ at1 = at2
        then isTrue (by obtain ⟨h1,h2⟩ := h; subst_vars; rfl)
        else isFalse (by intro heq; injection heq with h1 h2; exact h ⟨h1,h2⟩)
    case Tunion i1 at1 i2 at2 =>
      exact if h : i1 = i2 ∧ at1 = at2
        then isTrue (by obtain ⟨h1,h2⟩ := h; subst_vars; rfl)
        else isFalse (by intro heq; injection heq with h1 h2; exact h ⟨h1,h2⟩)

  def listTypeDecEq (xs ys : List type) : Decidable (xs = ys) := by
    cases xs with
    | nil => cases ys with
      | nil => exact isTrue rfl
      | cons _ _ => exact isFalse (fun h => nomatch h)
    | cons x xs => cases ys with
      | nil => exact isFalse (fun h => nomatch h)
      | cons y ys =>
        exact match typeDecEq x y with
          | isTrue hxy =>
              match listTypeDecEq xs ys with
              | isTrue hxsys => isTrue (by subst hxy hxsys; rfl)
              | isFalse hxsys => isFalse (by intro h; injection h with _ h'; exact hxsys h')
          | isFalse hxy => isFalse (by intro h; injection h with h' _; exact hxy h')
end

instance : DecidableEq type := typeDecEq

-- Extract the attributes of a type.

def attr_of_type (ty : type) : attr :=
  match ty with
  | .Tvoid => noattr
  | .Tint _ _ a => a
  | .Tlong _ a => a
  | .Tfloat _ a => a
  | .Tpointer _ a => a
  | .Tarray _ _ a => a
  | .Tfunction _ _ _ => noattr
  | .Tstruct _ a => a
  | .Tunion _ a => a

-- Change the top-level attributes of a type

def change_attributes (f : attr -> attr) (ty : type) : type :=
  match ty with
  | .Tvoid => ty
  | .Tint sz si a => .Tint sz si (f a)
  | .Tlong si a => .Tlong si (f a)
  | .Tfloat sz a => .Tfloat sz (f a)
  | .Tpointer elt a => .Tpointer elt (f a)
  | .Tarray elt sz a => .Tarray elt sz (f a)
  | .Tfunction _ _ _ => ty
  | .Tstruct id a => .Tstruct id (f a)
  | .Tunion id a => .Tunion id (f a)

-- Erase the top-level attributes of a type

def remove_attributes (ty : type) : type :=
  change_attributes (fun _ => noattr) ty

-- Add extra attributes to the top-level attributes of a type

def attr_union (a1 a2 : attr) : attr :=
  {attr_volatile := a1.attr_volatile || a2.attr_volatile ,
    attr_alignas :=
      match a1.attr_alignas, a2.attr_alignas with
      | none, al => al
      | al, none => al
      | some n1, some n2 => some (max n1 n2)}

def merge_attributes (ty : type) (a : attr) : type :=
  change_attributes (attr_union a) ty

-- Maximal size in bits of a bitfield of type [sz].
def bitsize_intsize (sz : intsize) : Int :=
  match sz with
  | .I8 => 8
  | .I16 => 16
  | .I32 => 32
  | .IBool => 1

/- Syntax for [struct] and [union] definitions.  [struct] and [union]
  are collectively called "composites".  Each compilation unit
  comes with a list of top-level definitions of composites. -/

inductive struct_or_union : Type where
  | Struct
  | Union
  deriving DecidableEq

inductive member : Type where
  | Member_plain (id : ident) (t : type)
  | Member_bitfield (id : ident) (sz : intsize) (sg : signedness) (a : attr) (width : Int) (padding : Bool)
  deriving DecidableEq

abbrev members : Type := List member

inductive composite_definition : Type where
  | Composite (id : ident) (su : struct_or_union) (m : members) (a : attr)
  deriving DecidableEq

def name_member (m : member) : ident :=
  match m with
  | .Member_plain id _ => id
  | .Member_bitfield id _ _ _ _ _ => id

def type_member (m : member) : type :=
  match m with
  | .Member_plain _ t => t
  | .Member_bitfield _ sz sg a w _ =>
    -- An unsigned bitfield of width < size of type reads with a signed type
    let sg' := if w < bitsize_intsize sz then .Signed else sg
    .Tint sz sg' a

def member_is_padding (m: member) : Bool :=
  match m with
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ _ p => p

def name_composite_def (c : composite_definition) : ident :=
  match c with
  | .Composite id _ _ _ => id

/- For type-checking, compilation and semantics purposes, the composite
  definitions are collected in the following [composite_env] environment.
  The [composite] record contains additional information compared with
  the [composite_definition], such as size and alignment information. -/
structure composite : Type where
  co_su: struct_or_union
  co_members: members
  co_attr: attr
  co_sizeof: Int
  co_alignof: Int
  co_rank: Nat
  co_sizeof_pos: co_sizeof >= 0
  co_alignof_two_p: ∃ n : Nat, co_alignof = 2^n
  co_sizeof_alignof: co_alignof ∣ co_sizeof

def test : composite := { co_su := struct_or_union.Struct, co_members := [], co_attr := noattr, co_sizeof := 8, co_alignof := 4, co_rank := 0, co_sizeof_pos := by omega, co_alignof_two_p := ⟨2, rfl⟩ , co_sizeof_alignof := by norm_num }

/- `ident := Nat` is a plain `def` (not `@[reducible]`), so typeclass
   resolution at "instances" transparency does not automatically unfold it
   to `Nat` when looking for `Std.TransCmp compare`/etc. instances already
   registered for `Nat`. Register them explicitly at `ident` itself, by
   forwarding to `Nat`'s instances (checked via full defeq at elaboration
   time, which does unfold `ident`). -/
instance : Std.TransCmp (compare (α := ident)) :=
  inferInstanceAs (Std.TransCmp (compare (α := Nat)))

instance : Std.LawfulEqCmp (compare (α := ident)) :=
  inferInstanceAs (Std.LawfulEqCmp (compare (α := Nat)))

abbrev composite_env : Type := Std.TreeMap ident composite

def empty_composite_env : composite_env := ∅

/- Access modes for members of structs or unions: either a plain field
    or a bitfield -/
inductive bitfield : Type where
  | Full
  | Bits (sz : intsize) (sg : signedness) (pos : Int) (width : Int)

-- * Operations over types

-- ** Conversions

def type_int32s : type := .Tint .I32 .Signed noattr
def type_bool : type := .Tint .IBool .Signed noattr

/- The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types.
  Attributes are erased. -/
def typeconv (ty : type) : type :=
  match ty with
  | .Tint .I8 _ _ => .Tint .I32 .Signed noattr
  | .Tint .I16 _ _ => .Tint .I32 .Signed noattr
  | .Tint .IBool _ _ => .Tint .I32 .Signed noattr
  | .Tarray t _ _ => .Tpointer t noattr
  | .Tfunction _ _ _ => .Tpointer ty noattr
  | _ => remove_attributes ty

/- Default conversion for arguments to an unprototyped or variadic function.
  Like [typeconv] but also converts single floats to double floats. -/

def default_argument_conversion (ty : type) : type :=
  match ty with
  | .Tint _ .Signed _ => .Tint .I32 .Signed noattr
  | .Tint _ .Unsigned _ => .Tint .I32 .Unsigned noattr
  | .Tarray t _ _ => .Tpointer t noattr
  | .Tfunction _ _ _ => .Tpointer ty noattr
  | .Tfloat _ _ => .Tfloat .F64 noattr
  | _ => remove_attributes ty

-- ** Complete types

/- A type is complete if it fully describes an object.
  All struct and union names appearing in the type must be defined,
  unless they occur under a pointer or function type.  [void] and
  function types are incomplete types. -/

def complete_type (env : composite_env) (t : type) : Bool :=
  match t with
    | .Tvoid => false
    | .Tint _ _ _ => true
    | .Tlong _ _ => true
    | .Tfloat _ _ => true
    | .Tpointer _ _ => true
    | .Tarray t' _ _ => complete_type env t'
    | .Tfunction _ _ _ => false
    | .Tstruct id _ => env.contains id
    | .Tunion id _ => env.contains id

def complete_or_function_type (env : composite_env) (t : type) : Bool :=
  match t with
  | .Tfunction _ _ _ => true
  | _ => complete_type env t

-- ** Alignment of a type

/- Adjust the natural alignment [al] based on the attributes [a] attached
  to the type.  If an "alignas" attribute is given, use it as alignment
  in preference to [al]. -/

def align_attr (a : attr) (al : Int) : Int :=
  match a.attr_alignas with
  | some l => 2^l
  | none => al

/- In the ISO C standard, alignment is defined only for complete
  types.  However, it is convenient that [alignof] is a total
  function.  For incomplete types, it returns 1. -/

def alignof (env : composite_env) (t : type) : Int :=
  align_attr (attr_of_type t) <| match t with
    | .Tvoid => 1
    | .Tint .I8 _ _ => 1
    | .Tint .I16 _ _ => 2
    | .Tint .I32 _ _ => 4
    | .Tint .IBool _ _ => 1
    | .Tlong _ _ => Archi.align_int64
    | .Tfloat .F32 _ => 4
    | .Tfloat .F64 _ => Archi.align_float64
    | .Tpointer _ _ => if Archi.ptr64 then 8 else 4
    | .Tarray t' _ _ => alignof env t'
    | .Tfunction _ _ _ => 1
    | .Tstruct id _ | .Tunion id _ =>
        match env.get? id with
        | some co => co.co_alignof
        | none => 1

omit [Archi] in
theorem align_attr_two_p (al : Int) (a : attr) (h : ∃ n : Nat, al = 2^n) :
    ∃ n : Nat, align_attr a al = 2^n := by
  unfold align_attr
  cases a.attr_alignas with
  | some l => exact ⟨l, rfl⟩
  | none => exact h

theorem alignof_two_p (env : composite_env) (t : type) :
    ∃ n : Nat, alignof env t = 2^n := by
    match t with
    | .Tvoid => apply align_attr_two_p; exact ⟨0, by norm_num⟩
    | .Tint sz _ _ => cases sz <;> (apply align_attr_two_p)
                      . exact ⟨0, by norm_num⟩
                      . exact ⟨1, by norm_num⟩
                      . exact ⟨2, by norm_num⟩
                      . exact ⟨0, by norm_num⟩
    | .Tlong _ _ => apply align_attr_two_p; obtain ⟨n, h⟩ := Archi.align_int64_two_p; exact ⟨n, by simp [h]⟩
    | .Tfloat sz _ => cases sz <;> apply align_attr_two_p
                      . exact ⟨2, by norm_num⟩
                      . obtain ⟨n, h⟩ := Archi.align_float64_two_p; exact ⟨n, by simp [h]⟩
    | .Tpointer t' _ => apply align_attr_two_p; cases Archi.ptr64
                        . simp; exact ⟨2, by simp⟩
                        . simp; exact ⟨3, by simp⟩
    | .Tarray t' _ _ => apply align_attr_two_p; exact alignof_two_p env t'
    | .Tstruct id _ => apply align_attr_two_p; cases h : env.get? id with
                        | some co => exact co.co_alignof_two_p
                        | none => exact ⟨0, by norm_num⟩
    | .Tunion id _ => apply align_attr_two_p; cases h : env.get? id with
                        | some co => exact co.co_alignof_two_p
                        | none => exact ⟨0, by norm_num⟩
    | .Tfunction _ _ _ => apply align_attr_two_p; exact ⟨0, by simp⟩

theorem alignof_pos (env : composite_env) (t : type) :
    alignof env t > 0 := by
  obtain ⟨n, h⟩ := alignof_two_p env t
  rw [h]
  simp

-- ** Size of a type
/- In the ISO C standard, size is defined only for complete
  types.  However, it is convenient that [sizeof] is a total
  function.  For [void] and function types, we follow GCC and define
  their size to be 1.  For undefined structures and unions, the size is
  arbitrarily taken to be 0. -/

def sizeof (env : composite_env) (t : type) : Int :=
  match t with
  | .Tvoid => 1
  | .Tint .I8 _ _ => 1
  | .Tint .I16 _ _ => 2
  | .Tint .I32 _ _ => 4
  | .Tint .IBool _ _ => 1
  | .Tlong _ _ => 8
  | .Tfloat .F32 _ => 4
  | .Tfloat .F64 _ => 8
  | .Tpointer _ _ => if Archi.ptr64 then 8 else 4
  | .Tarray t' n _ => sizeof env t' * (max 0 n)
  | .Tfunction _ _ _ => 1
  | .Tstruct id _ | .Tunion id _ =>
      match env.get? id with
      | some co => co.co_sizeof
      | none => 0

theorem sizeof_pos (env : composite_env) (t : type):
  sizeof env t >= 0 := by
  match t with
  | .Tvoid => unfold sizeof; omega
  | .Tint sz _ _ => unfold sizeof; grind
  | .Tlong _ _ => unfold sizeof; omega
  | .Tfloat sz _ => unfold sizeof; grind
  | .Tpointer _ _ => unfold sizeof; grind
  | .Tfunction _ _ _ => unfold sizeof; omega
  | .Tarray t' n _ =>
      unfold sizeof
      have ih := sizeof_pos env t'
      apply Int.mul_nonneg ih
      simp
  | .Tstruct id _ | .Tunion id _ =>
      unfold sizeof
      match h : env.get? id with
      | some co => exact co.co_sizeof_pos
      | none => grind

/- The size of a type is an integral multiple of its alignment,
  unless the alignment was artificially increased with the [__Alignas]
  attribute. -/

def naturally_aligned (t: type) : Prop :=
  (attr_of_type t).attr_alignas = none /\
  match t with
  | .Tarray t' _ _ => naturally_aligned t'
  | _ => True

theorem sizeof_alignof_compat (env : composite_env) (t : type):
  naturally_aligned t -> (alignof env t ∣ sizeof env t) := by
  intro h
  unfold naturally_aligned at h
  have ⟨ha, hb⟩ := h
  match t with
  | .Tarray t' _ _ =>
      -- ha : (attr_of_type (.Tarray t' _ _)).attr_alignas = none
      -- hb : naturally_aligned t'
      -- alignof can raise it to another power of 2 or leave unchanged
      -- 2^2^n is always divisible by 2^n
      -- maybe I can then make use of align_attr_two_p and/or alignof_two_p
    simp [alignof, align_attr, ha, sizeof]
    apply Int.dvd_mul_of_dvd_left
    exact sizeof_alignof_compat env t' hb
  | .Tvoid => simp [alignof, align_attr, ha, sizeof]
  | .Tpointer _ _ => simp [alignof, align_attr, ha, sizeof]
  | .Tfunction _ _ _ => simp [alignof, align_attr, ha, sizeof]
  | .Tint .I8 _ _ => simp [alignof, align_attr, ha, sizeof]
  | .Tint .IBool _ _ => simp [alignof, align_attr, ha]
  | .Tint .I16 _ _ => simp [alignof, align_attr, ha, sizeof]
  | .Tint .I32 _ _ => simp [alignof, align_attr, ha, sizeof]
  | .Tfloat .F32 _ => simp [alignof, align_attr, ha, sizeof]
  -- | .Tfloat .F64 _ => cases Archi.ptr64; simp [alignof]; simp [align_attr]; simp only [ha]; simp only [sizeof]; have := Archi.align_float64_bound; exact Int.coe_nat_dvd.mpr this; simp [alignof]; simp [align_attr];
  -- | .Tfloat .F64 _ => cases Archi.ptr64;
  --                     . have := Archi.align_float64_bound; simp [alignof, align_attr, ha, sizeof]; obtain ⟨k, hk⟩ := this; use (k : Int); norm_cast;
  --                     . have := Archi.align_float64_bound; simp [alignof, align_attr, ha, sizeof]; obtain ⟨k, hk⟩ := this; use (k : Int); norm_cast;
  | .Tfloat .F64 _ => have := Archi.align_float64_bound; simp [alignof, align_attr, ha, sizeof]; obtain ⟨k, hk⟩ := this; use (k : Int); norm_cast;
  | .Tlong _ _ => have := Archi.align_int64_bound; simp [alignof, align_attr, ha, sizeof]; obtain ⟨k, hk⟩ := this; use (k : Int); norm_cast;
  | .Tstruct id _ | .Tunion id _ =>
      simp [alignof, align_attr, ha, sizeof]
      split
      · exact composite.co_sizeof_alignof _
      · exact Int.dvd_zero _

-- ** Layout of struct fields

section LAYOUT

variable (env : composite_env)

def bitalignof (t : type) : Int := alignof env t * 8

def bitsizeof (t : type) : Int := sizeof env t * 8

def bitalignof_intsize (sz : intsize) : Int :=
  match sz with
  | .I8 | .IBool => 8
  | .I16 => 16
  | .I32 => 32

/- Align n to the next multiple of amount -/
def align (n : Int) (amount : Int) : Int :=
  ((n + amount - 1) / amount) * amount

/- Round down n to a multiple of amount -/
def floor (n : Int) (amount : Int) : Int :=
  (n / amount) * amount

def next_field (pos : Int) (m : member) : Int :=
  match m with
  | .Member_plain _ t =>
      align pos (bitalignof env t) + bitsizeof env t
  | .Member_bitfield _ sz _ _ w _ =>
      let s := bitalignof_intsize sz
      if w <= 0 then
        align pos s
      else
        let curr := floor pos s
        let next := curr + s
        if pos + w <= next then pos + w else next + w

def layout_field (pos : Int) (m : member) : Except String (Int × bitfield) :=
  match m with
  | .Member_plain _ t =>
      Except.ok (align pos (bitalignof env t) / 8, .Full)
  | .Member_bitfield _ sz sg _ w _ =>
      if w <= 0 then
        Except.error "accessing zero-width bitfield"
      else if bitsize_intsize sz < w then
        Except.error "bitfield too wide"
      else
        let s := bitalignof_intsize sz
        let start := floor pos s
        let next := start + s
        if pos + w <= next then
          Except.ok (start / 8, .Bits sz sg (pos - start) w)
        else
          Except.ok (next / 8, .Bits sz sg 0 w)

/- Starting bit position of a field -/
def layout_start (p : Int) (bf : bitfield) : Int :=
  p * 8 + match bf with
  | .Full => 0
  | .Bits _ _ pos _ => pos

/- Width in bits of a field -/
def layout_width (t : type) (bf : bitfield) : Int :=
  match bf with
  | .Full => bitsizeof env t
  | .Bits _ _ _ w => w

/- Alignment requirement for a field -/
def layout_alignment (t : type) (bf : bitfield) : Int :=
  match bf with
  | .Full => alignof env t
  | .Bits sz _ _ _ => bitalignof_intsize sz / 8


-- Some properties
omit [Archi] in
theorem bitalignof_intsize_pos (sz : intsize) :
    bitalignof_intsize sz > 0 := by
  cases sz <;> decide

-- Helper theorems for division and alignment properties
omit [Archi] in
theorem div_add_mod (a b : Int) : a = a / b * b + a % b := by
  exact Eq.symm (Int.ediv_mul_add_emod a b)

omit [Archi] in
theorem align_le (n amount : Int) (h : amount > 0) : n <= align n amount := by
  unfold align
  -- Let q = (n+amount-1)/amount, r = (n+amount-1)%amount
  -- Then q*amount = (n+amount-1) - r, and since 0 ≤ r < amount,
  -- we get q*amount = n + (amount-1-r) ≥ n
  have e : amount * ((n + amount - 1) / amount) + (n + amount - 1) % amount = n + amount - 1 := by
    have h := Int.ediv_mul_add_emod (n + amount - 1) amount
    linear_combination h
  have hm0 := Int.emod_nonneg (n + amount - 1) (by omega : amount ≠ 0)
  have hml := Int.emod_lt_of_pos (n + amount - 1) h
  nlinarith [e, hm0, hml]

omit [Archi] in
theorem floor_le (n amount : Int) (h : amount > 0) : floor n amount <= n := by
  unfold floor
  exact Int.ediv_mul_le n (Int.ne_of_gt h)

theorem next_field_incr (pos : Int) (m : member) :
    pos <= next_field env pos m := by
  unfold next_field
  cases m with
  | Member_plain id t =>
      have h : bitalignof env t > 0 := by
        unfold bitalignof
        have := alignof_pos env t
        omega
      have align_bound := align_le pos (bitalignof env t) h
      have bitsizeof_nonneg : bitsizeof env t >= 0 := by
        unfold bitsizeof
        have := sizeof_pos env t
        omega
      calc pos
          <= align pos (bitalignof env t) := align_bound
        _ <= align pos (bitalignof env t) + bitsizeof env t := by linarith
  | Member_bitfield id sz sg a w p =>
      simp
      split
      · have h : bitalignof_intsize sz > 0 := bitalignof_intsize_pos sz
        exact align_le pos (bitalignof_intsize sz) h
      · split
        · omega
        · have hs : bitalignof_intsize sz > 0 := bitalignof_intsize_pos sz
          have hf : floor pos (bitalignof_intsize sz) <= pos := floor_le pos (bitalignof_intsize sz) hs
          have div_spec := div_add_mod pos (bitalignof_intsize sz)
          have mod_bound := Int.emod_lt_of_pos pos hs
          -- floor pos s = pos / s * s
          -- pos = pos / s * s + pos % s
          -- so pos < pos / s * s + s = floor pos s + s
          have floor_bound : pos < floor pos (bitalignof_intsize sz) + bitalignof_intsize sz := by
            unfold floor
            calc pos
                = pos / bitalignof_intsize sz * bitalignof_intsize sz + pos % bitalignof_intsize sz := div_spec
              _ < pos / bitalignof_intsize sz * bitalignof_intsize sz + bitalignof_intsize sz := by
                  have : pos % bitalignof_intsize sz < bitalignof_intsize sz := mod_bound
                  linarith
          -- Goal: pos <= floor pos s + s + w
          -- We have: pos < floor pos s + s and w > 0 (from split condition)
          have : pos < floor pos (bitalignof_intsize sz) + bitalignof_intsize sz + w := by
            have w_pos : w > 0 := by omega  -- from ¬(w <= 0)
            calc pos
                < floor pos (bitalignof_intsize sz) + bitalignof_intsize sz := floor_bound
              _ <= floor pos (bitalignof_intsize sz) + bitalignof_intsize sz + w := by linarith
          linarith

theorem layout_field_range (pos : Int) (m : member) (ofs : Int) (bf : bitfield) :
    layout_field env pos m = Except.ok (ofs, bf) ->
    pos <= layout_start ofs bf ∧
    layout_start ofs bf + layout_width env (type_member m) bf <= next_field env pos m := by
  intro h
  unfold layout_field at h
  unfold layout_start layout_width next_field type_member
  cases m with
  | Member_plain id t =>
      simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      simp [bitsizeof]
      constructor
      · -- Goal: pos <= align pos (bitalignof env t) / 8 * 8
        have ha : bitalignof env t > 0 := by
          unfold bitalignof
          have := alignof_pos env t
          omega
        have align_bound := align_le pos (bitalignof env t) ha
        -- align returns a multiple of bitalignof, and bitalignof is a multiple of 8
        have bitalign_div_8 : 8 ∣ bitalignof env t := by
          unfold bitalignof
          use alignof env t
          ring
        have align_div : bitalignof env t ∣ align pos (bitalignof env t) := by
          unfold align
          use ((pos + bitalignof env t - 1) / bitalignof env t)
          ring
        have align_div_8 : 8 ∣ align pos (bitalignof env t) := by
          exact Int.dvd_trans bitalign_div_8 align_div
        obtain ⟨k, hk⟩ := align_div_8
        have : align pos (bitalignof env t) / 8 * 8 = align pos (bitalignof env t) := by
          rw [hk]
          omega
        rw [this]
        exact align_bound
      · -- Goal: align pos (bitalignof env t) / 8 * 8 + sizeof env t * 8 <= align pos (bitalignof env t) + sizeof env t * 8
        have bitalign_div_8 : 8 ∣ bitalignof env t := by
          unfold bitalignof
          use alignof env t
          ring
        have align_div : bitalignof env t ∣ align pos (bitalignof env t) := by
          unfold align
          use ((pos + bitalignof env t - 1) / bitalignof env t)
          ring
        have align_div_8 : 8 ∣ align pos (bitalignof env t) := by
          exact Int.dvd_trans bitalign_div_8 align_div
        obtain ⟨k, hk⟩ := align_div_8
        rw [hk]
        simp
        omega
  | Member_bitfield id sz sg a w p =>
      simp at h
      split at h
      · contradiction -- w <= 0 case gives error
      · split at h
        · contradiction -- bitsize_intsize sz < w case gives error
        · split at h
          · -- Case: pos + w <= floor pos s + s
            simp at h
            obtain ⟨hofs, hbf⟩ := h
            subst hofs hbf
            simp
            constructor
            · -- Goal: pos <= floor pos (bitalignof_intsize sz) / 8 * 8 + (pos - floor pos (bitalignof_intsize sz))
              have hs : bitalignof_intsize sz > 0 := bitalignof_intsize_pos sz
              have s_div_8 : 8 ∣ bitalignof_intsize sz := by
                cases sz <;> norm_num [bitalignof_intsize]
              have floor_div : bitalignof_intsize sz ∣ floor pos (bitalignof_intsize sz) := by
                unfold floor
                use (pos / bitalignof_intsize sz)
                ring
              have floor_div_8 : 8 ∣ floor pos (bitalignof_intsize sz) := by
                exact Int.dvd_trans s_div_8 floor_div
              obtain ⟨k, hk⟩ := floor_div_8
              rw [hk]
              simp
              omega
            · -- Goal: floor pos s / 8 * 8 + (pos - floor pos s) + w <= pos + w
              have hs : bitalignof_intsize sz > 0 := bitalignof_intsize_pos sz
              have s_div_8 : 8 ∣ bitalignof_intsize sz := by
                cases sz <;> norm_num [bitalignof_intsize]
              have floor_div : bitalignof_intsize sz ∣ floor pos (bitalignof_intsize sz) := by
                unfold floor
                use (pos / bitalignof_intsize sz)
                ring
              have floor_div_8 : 8 ∣ floor pos (bitalignof_intsize sz) := by
                exact Int.dvd_trans s_div_8 floor_div
              obtain ⟨k, hk⟩ := floor_div_8
              rw [hk]
              simp
              omega
          · -- Case: pos + w > floor pos s + s, need to align to next
            simp at h
            obtain ⟨hofs, hbf⟩ := h
            subst hofs hbf
            simp
            constructor
            · -- Goal: pos <= (floor pos s + s) / 8 * 8
              have hs : bitalignof_intsize sz > 0 := bitalignof_intsize_pos sz
              have s_div_8 : 8 ∣ bitalignof_intsize sz := by
                cases sz <;> norm_num [bitalignof_intsize]
              have floor_div : bitalignof_intsize sz ∣ floor pos (bitalignof_intsize sz) := by
                unfold floor
                use (pos / bitalignof_intsize sz)
                ring
              have sum_div_8 : 8 ∣ (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz) := by
                have : bitalignof_intsize sz ∣ (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz) := by
                  exact Int.dvd_add floor_div (Int.dvd_refl _)
                exact Int.dvd_trans s_div_8 this
              obtain ⟨k, hk⟩ := sum_div_8
              rw [hk]
              have : pos < floor pos (bitalignof_intsize sz) + bitalignof_intsize sz := by
                have div_spec := div_add_mod pos (bitalignof_intsize sz)
                have mod_bound := Int.emod_lt_of_pos pos hs
                unfold floor
                calc pos
                    = pos / bitalignof_intsize sz * bitalignof_intsize sz + pos % bitalignof_intsize sz := div_spec
                  _ < pos / bitalignof_intsize sz * bitalignof_intsize sz + bitalignof_intsize sz := by linarith
              simp
              omega
            · -- Goal: (floor pos s + s) / 8 * 8 + w <= floor pos s + s + w
              have hs : bitalignof_intsize sz > 0 := bitalignof_intsize_pos sz
              have s_div_8 : 8 ∣ bitalignof_intsize sz := by
                cases sz <;> norm_num [bitalignof_intsize]
              have floor_div : bitalignof_intsize sz ∣ floor pos (bitalignof_intsize sz) := by
                unfold floor
                use (pos / bitalignof_intsize sz)
                ring
              have sum_div_8 : 8 ∣ (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz) := by
                have : bitalignof_intsize sz ∣ (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz) := by
                  exact Int.dvd_add floor_div (Int.dvd_refl _)
                exact Int.dvd_trans s_div_8 this
              obtain ⟨k, hk⟩ := sum_div_8
              rw [hk]
              simp
              omega

theorem layout_field_alignment (pos : Int) (m : member) (ofs : Int) (bf : bitfield) :
    layout_field env pos m = Except.ok (ofs, bf) ->
    layout_alignment env (type_member m) bf ∣ ofs := by
  intro h
  unfold layout_field at h
  cases m with
  | Member_plain id t =>
      simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      unfold layout_alignment type_member
      simp
      -- Goal: alignof env t ∣ align pos (bitalignof env t) / 8
      have align_div : bitalignof env t ∣ align pos (bitalignof env t) := by
        unfold align
        use ((pos + bitalignof env t - 1) / bitalignof env t)
        ring
      have bitalign_eq : bitalignof env t = alignof env t * 8 := by
        unfold bitalignof
        rfl
      rw [bitalign_eq] at align_div
      obtain ⟨k, hk⟩ := align_div
      have : align pos (bitalignof env t) = alignof env t * 8 * k := by
        rw [← bitalign_eq]; exact hk
      rw [this]
      use k
      have h8 : (8 : Int) ≠ 0 := by decide
      have : alignof env t * 8 * k = alignof env t * (8 * k) := by ring
      rw [this, Int.mul_ediv_assoc]
      · rw [Int.mul_ediv_cancel_left k h8]
      · use k
  | Member_bitfield id sz sg a w p =>
      unfold layout_alignment type_member
      simp at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · -- Case: pos + w <= next, so ofs = floor pos s / 8
            simp at h
            obtain ⟨h1, h2⟩ := h
            subst h1 h2
            simp
            -- Goal: bitalignof_intsize sz / 8 ∣ floor pos (bitalignof_intsize sz) / 8
            have s_div_8 : 8 ∣ bitalignof_intsize sz := by
              cases sz <;> decide
            have floor_div : bitalignof_intsize sz ∣ floor pos (bitalignof_intsize sz) := by
              unfold floor
              use (pos / bitalignof_intsize sz)
              ring
            obtain ⟨k1, hk1⟩ := s_div_8
            obtain ⟨k2, hk2⟩ := floor_div
            rw [hk2, hk1]
            use k2
            have h8 : (8 : Int) ≠ 0 := by decide
            have : 8 * k1 * k2 / 8 = k1 * k2 := by
              have : 8 * k1 * k2 = 8 * (k1 * k2) := by ring
              rw [this, Int.mul_ediv_cancel_left (k1 * k2) h8]
            rw [this]
            have : 8 * k1 / 8 = k1 := Int.mul_ediv_cancel_left k1 h8
            rw [this]
          · -- Case: pos + w > next, so ofs = (floor pos s + s) / 8
            simp at h
            obtain ⟨h1, h2⟩ := h
            subst h1 h2
            simp
            -- Goal: bitalignof_intsize sz / 8 ∣ (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz) / 8
            have s_div_8 : 8 ∣ bitalignof_intsize sz := by
              cases sz <;> decide
            have sum_div_s : bitalignof_intsize sz ∣ (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz) := by
              have floor_div : bitalignof_intsize sz ∣ floor pos (bitalignof_intsize sz) := by
                unfold floor
                use (pos / bitalignof_intsize sz)
                ring
              exact Int.dvd_add floor_div (Int.dvd_refl _)
            obtain ⟨k1, hk1⟩ := s_div_8
            obtain ⟨k2, hk2⟩ := sum_div_s
            rw [hk2, hk1]
            use k2
            have h8 : (8 : Int) ≠ 0 := by decide
            have : 8 * k1 * k2 / 8 = k1 * k2 := by
              have : 8 * k1 * k2 = 8 * (k1 * k2) := by ring
              rw [this, Int.mul_ediv_cancel_left (k1 * k2) h8]
            rw [this]
            have : 8 * k1 / 8 = k1 := Int.mul_ediv_cancel_left k1 h8
            rw [this]

end LAYOUT

-- ** Size and alignment for composite definitions

/- The alignment for a structure or union is the max of the alignment
   of its members. Padding bitfields are ignored. -/
def alignof_composite (env : composite_env) (ms : members) : Int :=
  match ms with
  | [] => 1
  | m :: ms =>
      if member_is_padding m then
        alignof_composite env ms
      else
        max (alignof env (type_member m)) (alignof_composite env ms)

/- The size of a structure corresponds to its layout: fields are
   laid out consecutively, and padding is inserted to align
   each field to the alignment for its type. Bitfields are packed
   as described above. -/
def bitsizeof_struct (env : composite_env) (cur : Int) (ms : members) : Int :=
  match ms with
  | [] => cur
  | m :: ms => bitsizeof_struct env (next_field env cur m) ms

def bytes_of_bits (n : Int) : Int := (n + 7) / 8

def sizeof_struct (env : composite_env) (m : members) : Int :=
  bytes_of_bits (bitsizeof_struct env 0 m)

/- The size of an union is the max of the sizes of its members. -/
def sizeof_union (env : composite_env) (ms : members) : Int :=
  match ms with
  | [] => 0
  | m :: ms => max (sizeof env (type_member m)) (sizeof_union env ms)

omit [Archi] in
lemma max_pow_two (n1 n2 : Nat) : max (2^n1 : Int) (2^n2) = 2^(max n1 n2) := by
  rcases Nat.le_total n1 n2 with h | h
  · rw [Nat.max_eq_right h, Int.max_eq_right]
    have : (2 : Nat) ^ n1 ≤ 2 ^ n2 := Nat.pow_le_pow_right (by norm_num : 2 > 0) h
    exact Int.ofNat_le_ofNat_of_le this
  · rw [Nat.max_eq_left h, Int.max_eq_left]
    have : (2 : Nat) ^ n2 ≤ 2 ^ n1 := Nat.pow_le_pow_right (by norm_num : 2 > 0) h
    exact Int.ofNat_le_ofNat_of_le this

theorem alignof_composite_two_p (env : composite_env) (m : members) :
    ∃ n : Nat, alignof_composite env m = 2^n := by
  induction m with
  | nil =>
      use 0
      unfold alignof_composite
      norm_num
  | cons m ms ih =>
      unfold alignof_composite
      by_cases h : member_is_padding m
      · simp [h]
        exact ih
      · simp [h]
        obtain ⟨n1, h1⟩ := alignof_two_p env (type_member m)
        obtain ⟨n2, h2⟩ := ih
        use max n1 n2
        rw [h1, h2]
        exact max_pow_two n1 n2

theorem alignof_composite_pos (env : composite_env) (m : members) (a : attr) :
    align_attr a (alignof_composite env m) > 0 := by
  obtain ⟨n, hn⟩ := alignof_composite_two_p env m
  obtain ⟨k, hk⟩ := align_attr_two_p (alignof_composite env m) a ⟨n, hn⟩
  rw [hk]
  apply Nat.cast_pos.mpr
  exact Nat.two_pow_pos k

theorem bitsizeof_struct_incr (env : composite_env) (m : members) (cur : Int) :
    cur <= bitsizeof_struct env cur m := by
  induction m generalizing cur with
  | nil =>
      unfold bitsizeof_struct
      omega
  | cons m ms ih =>
      unfold bitsizeof_struct
      have h1 : cur <= next_field env cur m := next_field_incr env cur m
      have h2 : next_field env cur m <= bitsizeof_struct env (next_field env cur m) ms := ih (next_field env cur m)
      linarith

theorem sizeof_union_pos (env : composite_env) (m : members) :
    0 <= sizeof_union env m := by
  induction m with
  | nil =>
      unfold sizeof_union
      omega
  | cons m ms ih =>
      unfold sizeof_union
      have h1 : 0 <= sizeof env (type_member m) := sizeof_pos env (type_member m)
      omega

-- ** Byte offset and bitfield designator for a field of a structure

def field_type (id : ident) (ms : members) : Except String type :=
  match ms with
  | [] => Except.error s!"Unknown field {id}"
  | m :: ms => if id == name_member m then Except.ok (type_member m) else field_type id ms

/- [field_offset env id fld] returns the byte offset for field [id]
   in a structure whose members are [fld]. It also returns a
   bitfield designator, giving the location of the bits to access
   within the storage unit for the bitfield. -/

def field_offset_rec (env : composite_env) (id : ident) (ms : members) (pos : Int) : Except String (Int × bitfield) :=
  match ms with
  | [] => Except.error s!"Unknown field {id}"
  | m :: ms =>
      if id == name_member m then
        layout_field env pos m
      else
        field_offset_rec env id ms (next_field env pos m)

def field_offset (env : composite_env) (id : ident) (ms : members) : Except String (Int × bitfield) :=
  field_offset_rec env id ms 0

/- [field_zero_or_padding m] returns true if the field is a zero length bitfield
   or does not have a name -/
def field_zero_or_padding (m : member) : Bool :=
  match m with
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ w p => w <= 0 || p

/- [layout_struct env ms accu pos] computes the layout of all fields of a struct that
   are not unnamed or zero width bitfield members -/
def layout_struct_rec (env : composite_env) (ms : members) (accu : List (ident × Int × bitfield)) (pos : Int) :
    Except String (List (ident × Int × bitfield)) :=
  match ms with
  | [] => Except.ok accu
  | m :: ms =>
      if field_zero_or_padding m then
        layout_struct_rec env ms accu (next_field env pos m)
      else
        match layout_field env pos m with
        | Except.error e => Except.error e
        | Except.ok (p, b) =>
            layout_struct_rec env ms ((name_member m, p, b) :: accu) (next_field env pos m)

def layout_struct (env : composite_env) (ms : members) : Except String (List (ident × Int × bitfield)) :=
  layout_struct_rec env ms [] 0

theorem field_offset_rec_in_range (env : composite_env) (id : ident) (ofs : Int) (bf : bitfield)
    (ty : type) (ms : members) (pos : Int) :
    field_offset_rec env id ms pos = Except.ok (ofs, bf) ->
    field_type id ms = Except.ok ty ->
    pos <= layout_start ofs bf ∧
    layout_start ofs bf + layout_width env ty bf <= bitsizeof_struct env pos ms := by
  induction ms generalizing pos with
  | nil =>
      intro h1 h2
      unfold field_offset_rec at h1
      contradiction
  | cons m ms ih =>
      intro h1 h2
      unfold field_offset_rec at h1
      unfold field_type at h2
      split at h1
      · split at h2
        · obtain ⟨h_lf_range1, h_lf_range2⟩ := layout_field_range env pos m ofs bf h1
          injection h2 with h_ty_eq
          subst h_ty_eq
          unfold bitsizeof_struct
          constructor
          · exact h_lf_range1
          · have h_incr := bitsizeof_struct_incr env ms (next_field env pos m)
            linarith
        · contradiction
      · split at h2
        · contradiction
        · unfold bitsizeof_struct
          have ih_applied := ih (next_field env pos m) h1 h2
          obtain ⟨ih_left, ih_right⟩ := ih_applied
          constructor
          · have h_next := next_field_incr env pos m
            linarith
          · exact ih_right

theorem field_offset_in_range_gen (env : composite_env) (ms : members) (id : ident) (ofs : Int)
    (bf : bitfield) (ty : type) :
    field_offset env id ms = Except.ok (ofs, bf) ->
    field_type id ms = Except.ok ty ->
    0 <= layout_start ofs bf ∧
    layout_start ofs bf + layout_width env ty bf <= bitsizeof_struct env 0 ms := by
  unfold field_offset
  exact field_offset_rec_in_range env id ofs bf ty ms 0

theorem field_offset_in_range (env : composite_env) (ms : members) (id : ident) (ofs : Int) (ty : type) :
    field_offset env id ms = Except.ok (ofs, .Full) ->
    field_type id ms = Except.ok ty ->
    0 <= ofs ∧ ofs + sizeof env ty <= sizeof_struct env ms := by
  intro hofs hty
  have hgen := field_offset_in_range_gen env ms id ofs .Full ty hofs hty
  simp [layout_start, layout_width, bitsizeof] at hgen
  constructor
  · omega
  · unfold sizeof_struct bytes_of_bits
    have : (ofs + sizeof env ty) * 8 <= bitsizeof_struct env 0 ms := by omega
    have hsizeof_pos : sizeof env ty >= 0 := sizeof_pos env ty
    have hofs_nonneg : ofs >= 0 := by omega
    have : ofs + sizeof env ty >= 0 := by omega
    have hbits_pos : bitsizeof_struct env 0 ms >= 0 := by
      have : (ofs + sizeof env ty) * 8 >= 0 := by omega
      omega
    have key : (ofs + sizeof env ty) * 8 <= bitsizeof_struct env 0 ms →
               ofs + sizeof env ty <= (bitsizeof_struct env 0 ms + 7) / 8 := by
      intro h
      have : (ofs + sizeof env ty) <= bitsizeof_struct env 0 ms / 8 := by
        have h8_pos : (8 : Int) > 0 := by omega
        have div_mono := Int.ediv_le_ediv h8_pos h
        simp at div_mono
        omega
      calc ofs + sizeof env ty
          <= bitsizeof_struct env 0 ms / 8 := this
        _ <= (bitsizeof_struct env 0 ms + 7) / 8 := by
          have : bitsizeof_struct env 0 ms <= bitsizeof_struct env 0 ms + 7 := by omega
          exact Int.ediv_le_ediv (by omega : (8 : Int) > 0) this
    exact key (by omega)

theorem field_offset_no_overlap_rec (env : composite_env) (id1 : ident) (ofs1 : Int) (bf1 : bitfield)
    (ty1 : type) (id2 : ident) (ofs2 : Int) (bf2 : bitfield) (ty2 : type) (fld : members) (pos : Int) :
    field_offset_rec env id1 fld pos = Except.ok (ofs1, bf1) ->
    field_type id1 fld = Except.ok ty1 ->
    field_offset_rec env id2 fld pos = Except.ok (ofs2, bf2) ->
    field_type id2 fld = Except.ok ty2 ->
    id1 ≠ id2 ->
    layout_start ofs1 bf1 + layout_width env ty1 bf1 <= layout_start ofs2 bf2 ∨
    layout_start ofs2 bf2 + layout_width env ty2 bf2 <= layout_start ofs1 bf1 := by
  induction fld generalizing pos with
  | nil =>
      intro h1 _ _ _ _
      unfold field_offset_rec at h1
      contradiction
  | cons m ms ih =>
      intro h_fo1_rec h_ft1_rec h_fo2_rec h_ft2_rec h_neq
      unfold field_offset_rec at h_fo1_rec h_fo2_rec
      unfold field_type at h_ft1_rec h_ft2_rec
      split at h_fo1_rec
      · split at h_fo2_rec
        · split at h_ft1_rec
          · split at h_ft2_rec
            · rename_i h1 h2 h3 h4
              have : id1 = id2 := by
                simp [beq_iff_eq] at h1 h2
                exact Eq.trans h1 (Eq.symm h2)
              contradiction
            · contradiction
          · contradiction
        · split at h_ft1_rec
          · split at h_ft2_rec
            · contradiction
            · rename_i h1 h2 h3 h4
              have h_lf1 := layout_field_range env pos m ofs1 bf1 h_fo1_rec
              injection h_ft1_rec with h_ty1_eq
              subst h_ty1_eq
              have h_fo2_range := field_offset_rec_in_range env id2 ofs2 bf2 ty2 ms (next_field env pos m) h_fo2_rec h_ft2_rec
              left
              obtain ⟨h_lf1_start, h_lf1_end⟩ := h_lf1
              obtain ⟨h_fo2_start, _⟩ := h_fo2_range
              linarith
          · contradiction
      · split at h_fo2_rec
        · split at h_ft1_rec
          · contradiction
          · split at h_ft2_rec
            · rename_i h1 h2 h3 h4
              have h_lf2 := layout_field_range env pos m ofs2 bf2 h_fo2_rec
              injection h_ft2_rec with h_ty2_eq
              subst h_ty2_eq
              have h_fo1_range := field_offset_rec_in_range env id1 ofs1 bf1 ty1 ms (next_field env pos m) h_fo1_rec h_ft1_rec
              right
              obtain ⟨h_lf2_start, h_lf2_end⟩ := h_lf2
              obtain ⟨h_fo1_start, _⟩ := h_fo1_range
              linarith
            · contradiction
        · split at h_ft1_rec
          · contradiction
          · split at h_ft2_rec
            · contradiction
            · exact ih (next_field env pos m) h_fo1_rec h_ft1_rec h_fo2_rec h_ft2_rec h_neq

theorem field_offset_no_overlap (env : composite_env) (id1 : ident) (ofs1 : Int) (bf1 : bitfield)
    (ty1 : type) (id2 : ident) (ofs2 : Int) (bf2 : bitfield) (ty2 : type) (fld : members) :
    field_offset env id1 fld = Except.ok (ofs1, bf1) ->
    field_type id1 fld = Except.ok ty1 ->
    field_offset env id2 fld = Except.ok (ofs2, bf2) ->
    field_type id2 fld = Except.ok ty2 ->
    id1 ≠ id2 ->
    layout_start ofs1 bf1 + layout_width env ty1 bf1 <= layout_start ofs2 bf2 ∨
    layout_start ofs2 bf2 + layout_width env ty2 bf2 <= layout_start ofs1 bf1 := by
  intro h_fo1 h_ft1 h_fo2 h_ft2 h_neq
  unfold field_offset at h_fo1 h_fo2
  exact field_offset_no_overlap_rec env id1 ofs1 bf1 ty1 id2 ofs2 bf2 ty2 fld 0 h_fo1 h_ft1 h_fo2 h_ft2 h_neq

theorem field_offset_rec_prefix (env : composite_env) (id : ident) (ofs : Int) (bf : bitfield)
    (fld2 fld1 : members) (pos : Int) :
    field_offset_rec env id fld1 pos = Except.ok (ofs, bf) ->
    field_offset_rec env id (fld1.append fld2) pos = Except.ok (ofs, bf) := by
  intro h
  induction fld1 generalizing pos with
  | nil =>
    unfold field_offset_rec at h
    contradiction
  | cons m ms ih =>
    unfold members at fld2
    have h_append : (m :: ms).append fld2 = m :: (ms.append fld2) := rfl
    rw [h_append]
    unfold field_offset_rec at h ⊢
    by_cases h_eq : id == name_member m
    · rw [if_pos h_eq] at h ⊢
      exact h
    · rw [if_neg h_eq] at h ⊢
      exact ih (next_field env pos m) h

theorem field_offset_prefix (env : composite_env) (id : ident) (ofs : Int) (bf : bitfield)
    (fld2 fld1 : members) :
    field_offset env id fld1 = Except.ok (ofs, bf) ->
    field_offset env id (fld1.append fld2) = Except.ok (ofs, bf) := by
  intro h
  unfold field_offset at h ⊢
  exact field_offset_rec_prefix env id ofs bf fld2 fld1 0 h

theorem field_offset_rec_aligned (env : composite_env) (id : ident) (ofs : Int) (bf : bitfield)
    (ty : type) (ms : members) (pos : Int) :
    field_offset_rec env id ms pos = Except.ok (ofs, bf) ->
    field_type id ms = Except.ok ty ->
    layout_alignment env ty bf ∣ ofs := by
  induction ms generalizing pos with
  | nil =>
      intro h1 h2
      unfold field_offset_rec at h1
      contradiction
  | cons m ms ih =>
      intro h1 h2
      unfold field_offset_rec at h1
      unfold field_type at h2
      split at h1
      · split at h2
        · injection h2 with h_ty_eq
          subst h_ty_eq
          exact layout_field_alignment env pos m ofs bf h1
        · contradiction
      · split at h2
        · contradiction
        · exact ih (next_field env pos m) h1 h2

theorem field_offset_aligned_gen (env : composite_env) (id : ident) (fld : members) (ofs : Int)
    (bf : bitfield) (ty : type) :
    field_offset env id fld = Except.ok (ofs, bf) ->
    field_type id fld = Except.ok ty ->
    layout_alignment env ty bf ∣ ofs := by
  unfold field_offset
  exact field_offset_rec_aligned env id ofs bf ty fld 0

theorem field_offset_aligned (env : composite_env) (id : ident) (fld : members) (ofs : Int) (ty : type) :
    field_offset env id fld = Except.ok (ofs, .Full) ->
    field_type id fld = Except.ok ty ->
    alignof env ty ∣ ofs := by
  intro h_off h_ty
  exact field_offset_aligned_gen env id fld ofs .Full ty h_off h_ty

/- [union_field_offset env id ms] returns the byte offset and
   bitfield designator for accessing a member named [id] of a union
   whose members are [ms]. The byte offset is always 0. -/

def union_field_offset (env : composite_env) (id : ident) (ms : members) : Except String (Int × bitfield) :=
  match ms with
  | [] => Except.error s!"Unknown field {id}"
  | m :: ms =>
      if id == name_member m then
        layout_field env 0 m
      else
        union_field_offset env id ms

omit [Archi] in
lemma align_zero (n : Int) (h : n > 0) : align 0 n = 0 := by
  unfold align
  simp
  have : (n - 1) / n = 0 := by
    have : 0 ≤ n - 1 ∧ n - 1 < n := by omega
    exact Int.ediv_eq_zero_of_lt this.1 this.2
  rw [this]
  simp

omit [Archi] in
lemma floor_zero (n : Int) : floor 0 n = 0 := by
  unfold floor
  simp

lemma layout_field_at_zero_offset (env : composite_env) (m : member) (ofs : Int) (bf : bitfield) :
    layout_field env 0 m = Except.ok (ofs, bf) -> ofs = 0 := by
  intro h
  unfold layout_field at h
  cases m with
  | Member_plain id t =>
      simp at h
      obtain ⟨h1, _⟩ := h
      subst h1
      have ha : bitalignof env t > 0 := by
        unfold bitalignof
        have := alignof_pos env t
        omega
      rw [align_zero (bitalignof env t) ha]
      simp
  | Member_bitfield id sz sg a w p =>
      simp at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · rw [floor_zero (bitalignof_intsize sz)] at h
          simp at h
          split at h
          · obtain ⟨h1, _⟩ := h
            omega
          · -- This branch should be unreachable
            -- The condition is: 0 + w <= 0 + s, i.e., w <= s
            -- We have ¬(bitsize_intsize sz < w), so w <= bitsize_intsize sz
            -- And bitsize_intsize sz <= bitalignof_intsize sz = s
            -- But the split says ¬(0 + w <= 0 + s), i.e., w > s
            rename_i h_neg_cond h_not_wide
            simp at h_neg_cond h_not_wide
            -- h_not_wide: ¬(bitsize_intsize sz < w)
            -- h_neg_cond: ¬(w <= bitalignof_intsize sz)
            have w_le_bitsize : w <= bitsize_intsize sz := by omega
            have bitsize_le_bitalign : bitsize_intsize sz <= bitalignof_intsize sz := by
              cases sz <;> decide
            have : w <= bitalignof_intsize sz := by omega
            omega

theorem union_field_offset_in_range_gen (env : composite_env) (id : ident) (ofs : Int) (bf : bitfield)
    (ty : type) (ms : members) :
    union_field_offset env id ms = Except.ok (ofs, bf) ->
    field_type id ms = Except.ok ty ->
    ofs = 0 ∧ 0 <= layout_start ofs bf ∧
    layout_start ofs bf + layout_width env ty bf <= sizeof_union env ms * 8 := by
  intro h_union h_field
  induction ms with
  | nil =>
      unfold union_field_offset at h_union
      contradiction
  | cons m ms ih =>
      unfold union_field_offset at h_union
      unfold field_type at h_field
      split at h_union <;> split at h_field
      · rename_i h_eq _
        injection h_field with h_ty_eq
        subst h_ty_eq
        have h_ofs_eq : ofs = 0 := layout_field_at_zero_offset env m ofs bf h_union
        constructor
        · exact h_ofs_eq
        · have h_range := layout_field_range env 0 m ofs bf h_union
          constructor
          · subst h_ofs_eq
            unfold layout_start
            cases bf with
            | Full => simp
            | Bits sz sg pos w =>
                simp
                have : 0 <= 0 * 8 + pos := h_range.1
                omega
          · unfold sizeof_union
            have h_le : layout_start ofs bf + layout_width env (type_member m) bf <= next_field env 0 m := h_range.2
            have h_next_le : next_field env 0 m <= bitsizeof env (type_member m) := by
              cases m with
              | Member_plain id t =>
                  unfold next_field type_member bitsizeof sizeof
                  simp
                  have ha : bitalignof env t > 0 := by
                    unfold bitalignof
                    have := alignof_pos env t
                    omega
                  rw [align_zero (bitalignof env t) ha]
              | Member_bitfield id sz sg a w p =>
                  unfold next_field type_member bitsizeof sizeof
                  -- Extract constraints from h_union (layout_field succeeded)
                  unfold layout_field at h_union
                  simp at h_union
                  split at h_union
                  · contradiction  -- w > 0 because layout_field succeeded
                  · split at h_union
                    · contradiction  -- w <= bitsize_intsize sz
                    · rename_i h_w_pos h_w_bounded
                      simp at h_w_pos h_w_bounded
                      -- h_w_pos: ¬(w ≤ 0), so w > 0
                      -- h_w_bounded: ¬(bitsize_intsize sz < w), so w ≤ bitsize_intsize sz
                      have w_pos : w > 0 := by omega
                      have w_not_le_0 : ¬(w <= 0) := by omega
                      cases sz
                      · have ha : align 0 (bitalignof_intsize .I8) = 0 := align_zero _ (by decide)
                        have hf : floor 0 (bitalignof_intsize .I8) = 0 := floor_zero _
                        have w_le : w <= 8 := by
                          unfold bitsize_intsize at h_w_bounded
                          omega
                        have w_le_ba : w <= bitalignof_intsize .I8 := by
                          unfold bitalignof_intsize; omega
                        simp [ha, hf]
                        rw [if_neg w_not_le_0, if_pos w_le_ba]; omega
                      · have ha : align 0 (bitalignof_intsize .I16) = 0 := align_zero _ (by decide)
                        have hf : floor 0 (bitalignof_intsize .I16) = 0 := floor_zero _
                        have w_le : w <= 16 := by
                          unfold bitsize_intsize at h_w_bounded
                          omega
                        have w_le_ba : w <= bitalignof_intsize .I16 := by
                          unfold bitalignof_intsize; omega
                        simp [ha, hf]
                        rw [if_neg w_not_le_0, if_pos w_le_ba]; omega
                      · have ha : align 0 (bitalignof_intsize .I32) = 0 := align_zero _ (by decide)
                        have hf : floor 0 (bitalignof_intsize .I32) = 0 := floor_zero _
                        have w_le : w <= 32 := by
                          unfold bitsize_intsize at h_w_bounded
                          omega
                        have w_le_ba : w <= bitalignof_intsize .I32 := by
                          unfold bitalignof_intsize; omega
                        simp [ha, hf]
                        rw [if_neg w_not_le_0, if_pos w_le_ba]; omega
                      · have ha : align 0 (bitalignof_intsize .IBool) = 0 := align_zero _ (by decide)
                        have hf : floor 0 (bitalignof_intsize .IBool) = 0 := floor_zero _
                        have w_le : w <= 1 := by
                          unfold bitsize_intsize at h_w_bounded
                          omega
                        have w_le_ba : w <= bitalignof_intsize .IBool := by
                          unfold bitalignof_intsize; simp; omega
                        simp [ha, hf]
                        rw [if_neg w_not_le_0, if_pos w_le_ba]; omega
            have size_le : sizeof env (type_member m) <= sizeof_union env (m :: ms) := by
              unfold sizeof_union
              omega
            have bound1 : layout_start ofs bf + layout_width env (type_member m) bf <= bitsizeof env (type_member m) := by
              calc layout_start ofs bf + layout_width env (type_member m) bf
                  <= next_field env 0 m := h_le
                _ <= bitsizeof env (type_member m) := h_next_le
            have bound2 : bitsizeof env (type_member m) = sizeof env (type_member m) * 8 := by
              unfold bitsizeof
              rfl
            rw [bound2] at bound1
            calc layout_start ofs bf + layout_width env (type_member m) bf
                <= sizeof env (type_member m) * 8 := bound1
              _ <= sizeof_union env (m :: ms) * 8 := by omega
      · rename_i h_ne h_eq
        contradiction
      · rename_i h_eq h_ne
        contradiction
      · rename_i h_ne _
        have ⟨h_ofs_eq, h_start_nonneg, h_bound⟩ := ih h_union h_field
        constructor
        · exact h_ofs_eq
        · constructor
          · exact h_start_nonneg
          · unfold sizeof_union
            omega

theorem union_field_offset_in_range (env : composite_env) (ms : members) (id : ident) (ofs : Int) (ty : type) :
    union_field_offset env id ms = Except.ok (ofs, .Full) ->
    field_type id ms = Except.ok ty ->
    ofs = 0 ∧ sizeof env ty <= sizeof_union env ms := by
  intro h_union h_field
  obtain ⟨h_ofs_eq, h_start_nonneg, h_bound⟩ := union_field_offset_in_range_gen env id ofs .Full ty ms h_union h_field
  constructor
  exact h_ofs_eq
  unfold layout_start layout_width bitsizeof at h_bound
  simp at h_bound
  have : ofs * 8 + sizeof env ty * 8 <= sizeof_union env ms * 8 := h_bound
  omega

-- ** Access modes

/- The [access_mode] function describes how a l-value of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the l-value using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the l-value (used for arrays and functions);
- [By_copy]: access is by reference, assignment is by copy
  (used for [struct] and [union] types)
- [By_nothing]: no access is possible, e.g. for the [void] type.
-/

inductive mode: Type where
  | By_value (m : memory_chunk)
  | By_reference
  | By_copy
  | By_nothing

def access_mode (ty: type) : mode :=
  match ty with
  | .Tint .I8 .Signed _ => .By_value .Mint8signed
  | .Tint .I8 .Unsigned _ => .By_value .Mint8unsigned
  | .Tint .I16 .Signed _ => .By_value .Mint16signed
  | .Tint .I16 .Unsigned _ => .By_value .Mint16unsigned
  | .Tint .I32 _ _ => .By_value .Mint32
  | .Tint .IBool _ _ => .By_value .Mbool
  | .Tlong _ _ => .By_value .Mint64
  | .Tfloat .F32 _ => .By_value .Mfloat32
  | .Tfloat .F64 _ => .By_value .Mfloat64
  | .Tvoid => .By_nothing
  | .Tpointer _ _ => .By_value Mptr
  | .Tarray _ _ _ => .By_reference
  | .Tfunction _ _ _ => .By_reference
  | .Tstruct _ _ => .By_copy
  | .Tunion _ _ => .By_copy

/- For the purposes of the semantics and the compiler, a type denotes
  a volatile access if it carries the [volatile] attribute and it is
  accessed by value. -/

def type_is_volatile (ty: type) : Bool :=
  match access_mode ty with
  | .By_value _ => attr.attr_volatile (attr_of_type ty)
  | _          => false

/- ** Alignment for block copy operations -/

/- A variant of [alignof] for use in block copy operations.
  Block copy operations do not support alignments greater than 8,
  and require the size to be an integral multiple of the alignment. -/

def alignof_blockcopy (env: composite_env) (t: type) : Int :=
  match t with
  | .Tvoid => 1
  | .Tint .I8 _ _ => 1
  | .Tint .I16 _ _ => 2
  | .Tint .I32 _ _ => 4
  | .Tint .IBool _ _ => 1
  | .Tlong _ _ => Archi.align_int64
  | .Tfloat .F32 _ => 4
  | .Tfloat .F64 _ => Archi.align_float64
  | .Tpointer _ _ => if Archi.ptr64 then 8 else 4
  | .Tarray t' _ _ => alignof_blockcopy env t'
  | .Tfunction _ _ _ => 1
  | .Tstruct id _ | .Tunion id _ =>
      match env.get? id with
      | some co => min 8 (co.co_alignof)
      | none => 1

theorem alignof_blockcopy_1248 (env : composite_env) (ty : type) :
  alignof_blockcopy env ty = 1 ∨ alignof_blockcopy env ty = 2 ∨ alignof_blockcopy env ty = 4 ∨ alignof_blockcopy env ty = 8 := by
    cases ty with
    | Tvoid => simp [alignof_blockcopy]
    | Tint sz _ _ =>
      cases sz <;> simp [alignof_blockcopy]
    | Tlong _ _ =>
      simp only [alignof_blockcopy]
      have h1 : Archi.align_int64 ∣ 8 := Archi.align_int64_bound
      obtain ⟨n, h2⟩ := Archi.align_int64_two_p
      rw [h2]
      obtain ⟨k, hk⟩ := h1
      rw [h2] at hk
      have : k = 0 ∨ k ≥ 1 := by omega
      rcases this with rfl | hk1
      · omega
      · have : n ≤ 3 := by
          by_contra hc
          have := Nat.pow_le_pow_right (by omega : 2 > 0) (Nat.not_le.mp hc)
          nlinarith
        interval_cases n <;> omega
    | Tfloat sz _ =>
      cases sz
      · simp [alignof_blockcopy]
      · simp only [alignof_blockcopy]
        have h1 : Archi.align_float64 ∣ 8 := Archi.align_float64_bound
        obtain ⟨n, h2⟩ := Archi.align_float64_two_p
        rw [h2]
        obtain ⟨k, hk⟩ := h1
        rw [h2] at hk
        have : k = 0 ∨ k ≥ 1 := by omega
        rcases this with rfl | hk1
        · omega
        · have : n ≤ 3 := by
            by_contra hc
            have := Nat.pow_le_pow_right (by omega : 2 > 0) (Nat.not_le.mp hc)
            nlinarith
          interval_cases n <;> omega
    | Tpointer _ _ =>
      simp only [alignof_blockcopy]
      split <;> omega
    | Tarray t' _ _ =>
      simp only [alignof_blockcopy]
      exact alignof_blockcopy_1248 env t'
    | Tfunction _ _ _ =>
      simp [alignof_blockcopy]
    | Tstruct id _ =>
      unfold alignof_blockcopy
      cases h : env.get? id with
      | some co =>
        simp only []
        have ⟨n, hn⟩ := co.co_alignof_two_p
        rw [hn]
        by_cases h4 : n ≤ 3
        · interval_cases n <;> simp [min]
        · push Not at h4
          have hpow : 2 ^ n ≥ 2 ^ 4 := Nat.pow_le_pow_right (by omega) h4
          have : min 8 (2 ^ n : Int) = 8 := by
            simp [min]
            norm_cast
            omega
          simp [this]
      | none => simp
    | Tunion id _ =>
      unfold alignof_blockcopy
      cases h : env.get? id with
      | some co =>
        simp only []
        have ⟨n, hn⟩ := co.co_alignof_two_p
        rw [hn]
        by_cases h4 : n ≤ 3
        · interval_cases n <;> simp [min]
        · push Not at h4
          have hpow : 2 ^ n ≥ 2 ^ 4 := Nat.pow_le_pow_right (by omega) h4
          have : min 8 (2 ^ n : Int) = 8 := by
            simp [min]
            norm_cast
            omega
          simp [this]
      | none => simp

theorem alignof_blockcopy_pos (env : composite_env) (ty : type) :
  alignof_blockcopy env ty > 0 := by
  obtain h := alignof_blockcopy_1248 env ty
  omega

theorem sizeof_alignof_blockcopy_compat (env : composite_env) (ty : type) :
  (alignof_blockcopy env ty) ∣ (sizeof env ty) := by
  match ty with
  | .Tvoid => simp [alignof_blockcopy, sizeof]
  | .Tint .I8 _ _ => simp [alignof_blockcopy, sizeof]
  | .Tint .I16 _ _ => simp [alignof_blockcopy, sizeof]
  | .Tint .I32 _ _ => simp [alignof_blockcopy, sizeof]
  | .Tint .IBool _ _ => simp [alignof_blockcopy, sizeof]
  | .Tlong _ _ =>
      have := Archi.align_int64_bound
      simp only [alignof_blockcopy, sizeof]
      obtain ⟨k, hk⟩ := this
      use (k : Int)
      norm_cast
  | .Tfloat .F32 _ => simp [alignof_blockcopy, sizeof]
  | .Tfloat .F64 _ =>
      have := Archi.align_float64_bound
      simp only [alignof_blockcopy, sizeof]
      obtain ⟨k, hk⟩ := this
      use (k : Int)
      norm_cast
  | .Tpointer _ _ =>
      simp [alignof_blockcopy, sizeof]
  | .Tarray t' n _ =>
      simp [alignof_blockcopy, sizeof]
      apply Int.dvd_mul_of_dvd_left
      exact sizeof_alignof_blockcopy_compat env t'
  | .Tfunction _ _ _ => simp [alignof_blockcopy, sizeof]
  | .Tstruct id _ =>
      unfold alignof_blockcopy sizeof
      cases h : env.get? id with
      | some co =>
        simp only []
        have ⟨n, hn⟩ := co.co_alignof_two_p
        have hdvd : co.co_alignof ∣ co.co_sizeof := co.co_sizeof_alignof
        rw [hn] at hdvd
        rw [hn]
        by_cases h4 : n ≤ 3
        · interval_cases n <;> (simp [min] <;> try exact hdvd)
        · push Not at h4
          have hpow : 2 ^ n ≥ 2 ^ 4 := Nat.pow_le_pow_right (by omega) h4
          have hmin : min 8 (2 ^ n : Int) = 8 := by
            simp [min]; norm_cast; omega
          rw [hmin]
          have : (8 : Int) ∣ (2 ^ n : Int) := by
            have : n ≥ 4 := h4
            have : ∃ k, n = 3 + (k + 1) := ⟨n - 4, by omega⟩
            obtain ⟨k, hk⟩ := this
            rw [hk]
            norm_cast
            rw [pow_add]
            use (2 ^ (k + 1) : Nat)
            ring
          exact Int.dvd_trans this hdvd
      | none => simp
  | .Tunion id _ =>
      unfold alignof_blockcopy sizeof
      cases h : env.get? id with
      | some co =>
        simp only []
        have ⟨n, hn⟩ := co.co_alignof_two_p
        have hdvd : co.co_alignof ∣ co.co_sizeof := co.co_sizeof_alignof
        rw [hn] at hdvd
        rw [hn]
        by_cases h4 : n ≤ 3
        · interval_cases n <;> (simp [min] <;> try exact hdvd)
        · push Not at h4
          have hpow : 2 ^ n ≥ 2 ^ 4 := Nat.pow_le_pow_right (by omega) h4
          have hmin : min 8 (2 ^ n : Int) = 8 := by
            simp [min]; norm_cast; omega
          rw [hmin]
          have : (8 : Int) ∣ (2 ^ n : Int) := by
            have : n ≥ 4 := h4
            have : ∃ k, n = 3 + (k + 1) := ⟨n - 4, by omega⟩
            obtain ⟨k, hk⟩ := this
            rw [hk]
            norm_cast
            rw [pow_add]
            use (2 ^ (k + 1) : Nat)
            ring
          exact Int.dvd_trans this hdvd
      | none => simp

theorem alignof_alignof_blockcopy_compat (env : composite_env) (ty : type) :
  naturally_aligned ty → alignof_blockcopy env ty = min 8 (alignof env ty) := by
  intro h
  unfold naturally_aligned at h
  have ⟨ha, hb⟩ := h
  cases ty with
  | Tvoid =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
  | Tint sz _ _ =>
    cases sz <;> simp [alignof_blockcopy, alignof, align_attr, ha]
  | Tlong _ _ =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
    have h1 : Archi.align_int64 ∣ 8 := Archi.align_int64_bound
    obtain ⟨n, h2⟩ := Archi.align_int64_two_p
    rw [h2]
    obtain ⟨k, hk⟩ := h1
    rw [h2] at hk
    have : k = 0 ∨ k ≥ 1 := by omega
    rcases this with rfl | hk1
    · omega
    · have : n ≤ 3 := by
        by_contra hc
        have := Nat.pow_le_pow_right (by omega : 2 > 0) (Nat.not_le.mp hc)
        nlinarith
      interval_cases n <;> omega
  | Tfloat sz _ =>
    cases sz
    · simp [alignof_blockcopy, alignof, align_attr, ha]
    · simp [alignof_blockcopy, alignof, align_attr, ha]
      have h1 : Archi.align_float64 ∣ 8 := Archi.align_float64_bound
      obtain ⟨n, h2⟩ := Archi.align_float64_two_p
      rw [h2]
      obtain ⟨k, hk⟩ := h1
      rw [h2] at hk
      have : k = 0 ∨ k ≥ 1 := by omega
      rcases this with rfl | hk1
      · omega
      · have : n ≤ 3 := by
          by_contra hc
          have := Nat.pow_le_pow_right (by omega : 2 > 0) (Nat.not_le.mp hc)
          nlinarith
        interval_cases n <;> omega
  | Tpointer _ _ =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
    cases Archi.ptr64 <;> simp
  | Tarray t' _ _ =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
    exact alignof_alignof_blockcopy_compat env t' hb
  | Tfunction _ _ _ =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
  | Tstruct id _ =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
    split <;> simp
  | Tunion id _ =>
    simp [alignof_blockcopy, alignof, align_attr, ha]
    split <;> simp


-- Type ranks

/- The rank of a type is a nonnegative integer that measures the direct nesting
  of arrays, struct and union types.  It does not take into account indirect
  nesting such as a struct type that appears under a pointer or function type.
  Type ranks ensure that type expressions (ignoring pointer and function types)
  have an inductive structure. -/

def rank_type (ce : composite_env) (t : type) : Nat :=
  match t with
  | .Tarray t' _ _ => (rank_type ce t') + 1
  | .Tstruct id _ | .Tunion id _ =>
    match ce.get? id with
    | none => 0
    | some co => co.co_rank + 1
  | _ => 0

def rank_members (ce : composite_env) (m : members) : Nat :=
  match m with
  | [] => 0
  | .Member_plain _ t :: m => max (rank_type ce t) (rank_members ce m)
  | .Member_bitfield _ _ _ _ _ _ :: m => rank_members ce m

-- C types and back-end types

-- Extracting a type list from a function parameter declaration.

def type_of_params (params : List (ident × type)) : List type :=
  List.map (λ (_, snd) => snd) params

-- WARNING: TODO remove? this may not be needed for verification in lean
-- Translating C types to Cminor types and function signatures.

def typ_of_type (t : type) : typ :=
  match t with
  | .Tvoid => .Tint
  | .Tint _ _ _ => .Tint
  | .Tlong _ _ => .Tlong
  | .Tfloat .F32 _ => .Tsingle
  | .Tfloat .F64 _ => .Tfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => Tptr

-- Translating C types to Cminor types and function signatures.
def argtype_of_type (t : type) : xtype :=
  match t with
  | .Tvoid => .Xvoid
  | .Tint .I32 _ _ => .Xint
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .IBool _ _ => .Xbool
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ => .Xptr
  | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => .Xptr

/- In CompCert C, array, function, struct and union types cannot
    appear as function return types. -/

def rettype_of_type (t : type) : xtype :=
  match t with
  | .Tvoid => .Xvoid
  | .Tint .I32 _ _ => .Xint
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .IBool _ _ => .Xbool
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ => .Xptr
  | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => .Xvoid

def signature_of_type (args : List type) (res : type) (cc : calling_convention) : signature :=
  signature.mksignature (List.map argtype_of_type args) (rettype_of_type res) cc

-- Construction of the composite environment

def sizeof_composite (env: composite_env) (su: struct_or_union) (m: members) : Int :=
  match su with
  | .Struct => sizeof_struct env m
  | .Union => sizeof_union env m

lemma sizeof_struct_pos (env : composite_env) (m : members) :
  0 <= sizeof_struct env m := by
  unfold sizeof_struct bytes_of_bits
  have h : 0 <= bitsizeof_struct env 0 m := bitsizeof_struct_incr env m 0
  omega

lemma sizeof_composite_pos (env: composite_env) (su: struct_or_union) (m: members) :
  0 <= sizeof_composite env su m := by
  unfold sizeof_composite
  cases su
  · apply sizeof_struct_pos
  · apply sizeof_union_pos

def complete_members (env : composite_env) (ms : members) : Bool :=
  match ms with
  | [] => true
  | m :: ms => complete_type env (type_member m) ∧ complete_members env ms

omit [Archi] in
lemma complete_member (env: composite_env) (m: member) (ms: members) :
  List.contains ms m → complete_members env ms = true → complete_type env (type_member m) = true := by
  intro h_contains h_complete
  generalize hlen : ms.length = n
  revert ms m
  induction n with
  | zero =>
    intro m ms h_contains h_complete hlen
    cases ms
    · cases h_contains
    · simp at hlen
  | succ n' ih =>
    intro m ms h_contains h_complete hlen
    cases ms with
    | nil =>
      cases h_contains
    | cons m' ms' =>
      unfold complete_members at h_complete
      have h_and : complete_type env (type_member m') = true ∧ complete_members env ms' = true := by
        cases h : (complete_type env (type_member m') && complete_members env ms') with
        | false =>
          simp [h] at h_complete
        | true =>
          exact Bool.and_eq_true_iff.mp h
      have h_head := h_and.1
      have h_tail := h_and.2
      unfold List.contains at h_contains
      rw [List.elem_cons] at h_contains
      split at h_contains
      · rename_i h_eq
        have : m = m' := beq_iff_eq.mp h_eq
        rw [this]
        exact h_head
      · have hlen' : ms'.length = n' := by
          simp at hlen
          omega
        exact ih m ms' h_contains h_tail hlen'

/- Convert a composite definition to its internal representation.
  The size and alignment of the composite are determined at this time.
  The alignment takes into account the [__Alignas] attributes
  associated with the definition.  The size is rounded up to a multiple
  of the alignment.

  The conversion fails if a type of a member is not complete.  This rules
  out incorrect recursive definitions such as
<<
    struct s { int x; struct s next; }
>>
  Here, when we process the definition of [struct s], the identifier [s]
  is not bound yet in the composite environment, hence field [next]
  has an incomplete type.  However, recursions that go through a pointer type
  are correctly handled:
<<
    struct s { int x; struct s * next; }
>>
  Here, [next] has a pointer type, which is always complete, even though
  [s] is not yet bound to a composite.
-/

def composite_of_def (env : composite_env) (id : ident) (su : struct_or_union) (m : members) (a : attr) : Except String composite :=
  match env.get? id, complete_members env m with
  | some _, _ => Except.error ("Multiple definitions of struct or union ")
  | none, false => Except.error ("Incomplete struct or union ")
  | none, true =>
    let al := align_attr a (alignof_composite env m)
    Except.ok { co_su := su, co_members := m,
                co_attr := a, co_sizeof := align (sizeof_composite env su m) al,
                co_alignof := al, co_rank := rank_members env m,
                co_sizeof_pos := by
                  have h_pos : 0 <= sizeof_composite env su m := sizeof_composite_pos env su m
                  have h_al_pos : al > 0 := alignof_composite_pos env m a
                  unfold align
                  have h_div : (sizeof_composite env su m + al - 1) / al >= 0 := by
                    apply Int.ediv_nonneg
                    · omega
                    · omega
                  apply Int.mul_nonneg h_div
                  omega
                co_alignof_two_p := by
                  obtain ⟨n, hn⟩ := alignof_composite_two_p env m
                  exact align_attr_two_p (alignof_composite env m) a ⟨n, hn⟩
                co_sizeof_alignof := by
                  unfold align
                  use ((sizeof_composite env su m + al - 1) / al)
                  ring
              }

/- The composite environment for a program is obtained by entering
  its composite definitions in sequence.  The definitions are assumed
  to be listed in dependency order: the definition of a composite
  must precede all uses of this composite, unless the use is under
  a pointer or function type. -/

def add_composite_definitions (env : composite_env) (defs : List composite_definition) : Except String composite_env :=
  match defs with
  | [] => Except.ok env
  | .Composite id su m a :: defs =>
      match composite_of_def env id su m a with
      | Except.error e => Except.error e
      | Except.ok co => add_composite_definitions (env.insert id co) defs

def build_composite_env (defs : List composite_definition) : Except String composite_env :=
  add_composite_definitions ∅ defs

/- Stability properties for alignments, sizes, and ranks. If the type is
   complete in a composite environment [env], its size, alignment, and rank
   are unchanged if we add more definitions to [env]. -/

section STABILITY

variable (env env' : composite_env)
variable (env_extends : ∀ id co, env.get? id = some co → env'.get? id = some co)

include env_extends in
theorem alignof_stable (t : type) :
    complete_type env t = true → alignof env' t = alignof env t := by
  intro h
  cases t with
  | Tvoid => unfold complete_type at h; contradiction
  | Tint sz _ _ => unfold alignof; cases sz <;> rfl
  | Tlong _ _ => unfold alignof; rfl
  | Tfloat sz _ => unfold alignof; cases sz <;> rfl
  | Tpointer _ _ => unfold alignof; rfl
  | Tarray t' _ _ =>
      unfold alignof
      congr 1
      exact alignof_stable t' h
  | Tfunction _ _ _ => unfold complete_type at h; contradiction
  | Tstruct id a =>
      unfold complete_type at h
      unfold alignof align_attr attr_of_type
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only []
          rw [h_env, env_extends id co h_env]
  | Tunion id a =>
      unfold complete_type at h
      unfold alignof align_attr attr_of_type
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only []
          rw [h_env, env_extends id co h_env]

include env_extends in
theorem sizeof_stable (t : type) :
    complete_type env t = true → sizeof env' t = sizeof env t := by
  intro h
  cases t with
  | Tvoid => unfold complete_type at h; contradiction
  | Tint sz _ _ => unfold sizeof; cases sz <;> rfl
  | Tlong _ _ => unfold sizeof; rfl
  | Tfloat sz _ => unfold sizeof; cases sz <;> rfl
  | Tpointer _ _ => unfold sizeof; rfl
  | Tarray t' n a =>
      unfold sizeof
      unfold complete_type at h
      congr 1
      exact sizeof_stable t' h
  | Tfunction _ _ _ => unfold complete_type at h; contradiction
  | Tstruct id a =>
      unfold complete_type at h
      unfold sizeof
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only []
          rw [env_extends id co h_env]
  | Tunion id a =>
      unfold complete_type at h
      unfold sizeof
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only []
          rw [env_extends id co h_env]

omit [Archi] in
include env_extends in
theorem complete_type_stable (t : type) :
    complete_type env t = true → complete_type env' t = true := by
  intro h
  cases t with
  | Tvoid => unfold complete_type at h; contradiction
  | Tint _ _ _ => unfold complete_type; trivial
  | Tlong _ _ => unfold complete_type; trivial
  | Tfloat _ _ => unfold complete_type; trivial
  | Tpointer _ _ => unfold complete_type; trivial
  | Tarray t' _ _ =>
      unfold complete_type at h ⊢
      exact complete_type_stable t' h
  | Tfunction _ _ _ => unfold complete_type at h; contradiction
  | Tstruct id a =>
      unfold complete_type at h ⊢
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only [Std.TreeMap.contains_eq_isSome_getElem?,
                     ← Std.TreeMap.get?_eq_getElem?]
          rw [env_extends id co h_env]
          rfl
  | Tunion id a =>
      unfold complete_type at h ⊢
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only [Std.TreeMap.contains_eq_isSome_getElem?,
                     ← Std.TreeMap.get?_eq_getElem?]
          rw [env_extends id co h_env]
          rfl

omit [Archi] in
include env_extends in
theorem rank_type_stable (t : type) :
    complete_type env t = true → rank_type env' t = rank_type env t := by
  intro h
  cases t with
  | Tvoid => unfold complete_type at h; contradiction
  | Tint _ _ _ => unfold rank_type; rfl
  | Tlong _ _ => unfold rank_type; rfl
  | Tfloat _ _ => unfold rank_type; rfl
  | Tpointer _ _ => unfold rank_type; rfl
  | Tarray t' _ _ =>
      unfold rank_type
      unfold complete_type at h
      congr 1
      exact rank_type_stable t' h
  | Tfunction _ _ _ => unfold complete_type at h; contradiction
  | Tstruct id a =>
      unfold complete_type at h
      unfold rank_type
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only []
          rw [env_extends id co h_env]
  | Tunion id a =>
      unfold complete_type at h
      unfold rank_type
      cases h_env : env.get? id with
      | none =>
          simp [Std.TreeMap.contains_eq_isSome_getElem?,
                ← Std.TreeMap.get?_eq_getElem?, h_env] at h
      | some co =>
          simp only []
          rw [env_extends id co h_env]

include env_extends in
theorem alignof_composite_stable (ms : members) :
    complete_members env ms = true → alignof_composite env' ms = alignof_composite env ms := by
  intro h
  induction ms with
  | nil => unfold alignof_composite; rfl
  | cons m ms ih =>
      unfold alignof_composite
      by_cases h_pad : member_is_padding m
      · simp [h_pad]
        apply ih
        unfold complete_members at h
        by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
        · exact h_and.2
        · simp [h_and] at h
      · simp [h_pad]
        unfold complete_members at h
        by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
        · obtain ⟨h1, h2⟩ := h_and
          congr 1
          · exact alignof_stable env env' env_extends (type_member m) h1
          · exact ih h2
        · simp [h_and] at h

include env_extends in
theorem next_field_stable (pos : Int) (m : member) :
    complete_type env (type_member m) = true → next_field env' pos m = next_field env pos m := by
  intro h
  unfold next_field
  cases m with
  | Member_plain _ t =>
      unfold type_member at h
      have h_align := alignof_stable env env' env_extends t h
      have h_size := sizeof_stable env env' env_extends t h
      unfold bitalignof bitsizeof
      simp [h_align, h_size]
  | Member_bitfield _ sz _ _ w _ =>
      rfl

include env_extends in
theorem bitsizeof_struct_stable (ms : members) (pos : Int) :
    complete_members env ms = true → bitsizeof_struct env' pos ms = bitsizeof_struct env pos ms := by
  intro h
  induction ms generalizing pos with
  | nil => unfold bitsizeof_struct; rfl
  | cons m ms ih =>
      unfold bitsizeof_struct
      unfold complete_members at h
      by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
      · obtain ⟨h1, h2⟩ := h_and
        have h_next := next_field_stable env env' env_extends pos m h1
        rw [h_next]
        exact ih (next_field env pos m) h2
      · simp [h_and] at h

include env_extends in
theorem sizeof_union_stable (ms : members) :
    complete_members env ms = true → sizeof_union env' ms = sizeof_union env ms := by
  intro h
  induction ms with
  | nil => unfold sizeof_union; rfl
  | cons m ms ih =>
      unfold sizeof_union
      unfold complete_members at h
      by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
      · obtain ⟨h1, h2⟩ := h_and
        congr 1
        · exact sizeof_stable env env' env_extends (type_member m) h1
        · exact ih h2
      · simp [h_and] at h

include env_extends in
theorem sizeof_composite_stable (su : struct_or_union) (ms : members) :
    complete_members env ms = true → sizeof_composite env' su ms = sizeof_composite env su ms := by
  intro h
  cases su
  · simp only [sizeof_composite, sizeof_struct]
    congr 1
    exact bitsizeof_struct_stable env env' env_extends ms 0 h
  · simp only [sizeof_composite]
    exact sizeof_union_stable env env' env_extends ms h

omit [Archi] in
include env_extends in
theorem complete_members_stable (ms : members) :
    complete_members env ms = true → complete_members env' ms = true := by
  intro h
  induction ms with
  | nil => unfold complete_members; trivial
  | cons m ms ih =>
      unfold complete_members at h ⊢
      by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
      · obtain ⟨h1, h2⟩ := h_and
        simp only [complete_type_stable env env' env_extends (type_member m) h1, ih h2]
        trivial
      · simp [h_and] at h

omit [Archi] in
include env_extends in
theorem rank_members_stable (ms : members) :
    complete_members env ms = true → rank_members env' ms = rank_members env ms := by
  intro h
  induction ms with
  | nil => unfold rank_members; rfl
  | cons m ms ih =>
      cases m with
      | Member_plain _ t =>
          unfold complete_members at h
          by_cases h_and : complete_type env t = true ∧ complete_members env ms = true
          · obtain ⟨h1, h2⟩ := h_and
            simp only [rank_members]
            congr 1
            · exact rank_type_stable env env' env_extends t h1
            · exact ih h2
          · unfold type_member at h
            simp [h_and] at h
      | Member_bitfield id' sz sg a width padding =>
          unfold complete_members at h
          by_cases h_and : complete_type env (type_member (.Member_bitfield id' sz sg a width padding)) = true ∧ complete_members env ms = true
          · simp only [rank_members]
            exact ih h_and.2
          · exfalso
            apply h_and
            exact of_decide_eq_true h

include env_extends in
theorem layout_field_stable (pos : Int) (m : member) :
    complete_type env (type_member m) = true → layout_field env' pos m = layout_field env pos m := by
  intro h
  unfold layout_field
  cases m with
  | Member_plain _ t =>
      unfold type_member at h
      have h_align := alignof_stable env env' env_extends t h
      unfold bitalignof
      simp [h_align]
  | Member_bitfield _ sz sg _ w _ =>
      rfl

include env_extends in
theorem field_offset_rec_stable (f : ident) (ms : members) (pos : Int) :
    complete_members env ms = true → field_offset_rec env' f ms pos = field_offset_rec env f ms pos := by
  intro h
  induction ms generalizing pos with
  | nil => unfold field_offset_rec; rfl
  | cons m ms ih =>
      unfold field_offset_rec
      unfold complete_members at h
      by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
      · obtain ⟨h1, h2⟩ := h_and
        by_cases h_eq : f == name_member m
        · simp [h_eq]
          exact layout_field_stable env env' env_extends pos m h1
        · simp [h_eq]
          have h_next := next_field_stable env env' env_extends pos m h1
          rw [h_next]
          exact ih (next_field env pos m) h2
      · simp [h_and] at h

include env_extends in
theorem field_offset_stable (f : ident) (ms : members) :
    complete_members env ms = true → field_offset env' f ms = field_offset env f ms := by
  intro h
  unfold field_offset
  exact field_offset_rec_stable env env' env_extends f ms 0 h

include env_extends in
theorem union_field_offset_stable (f : ident) (ms : members) :
    complete_members env ms = true → union_field_offset env' f ms = union_field_offset env f ms := by
  intro h
  induction ms with
  | nil => unfold union_field_offset; rfl
  | cons m ms ih =>
      unfold union_field_offset
      unfold complete_members at h
      by_cases h_and : complete_type env (type_member m) = true ∧ complete_members env ms = true
      · obtain ⟨h1, h2⟩ := h_and
        by_cases h_eq : f == name_member m
        · simp [h_eq]
          exact layout_field_stable env env' env_extends 0 m h1
        · simp [h_eq]
          exact ih h2
      · simp [h_and] at h

end STABILITY

theorem add_composite_definitions_incr (id : ident) (co : composite) (defs : List composite_definition) (env1 env2 : composite_env) :
    add_composite_definitions env1 defs = Except.ok env2 →
    env1.get? id = some co →
    env2.get? id = some co := by
  intro h_add h_env1
  revert env1 env2
  induction defs with
  | nil =>
      intro env1 env2 h_add h_env1
      unfold add_composite_definitions at h_add
      simp at h_add
      rw [← h_add]
      exact h_env1
  | cons d defs ih =>
      intro env1 env2 h_add h_env1
      obtain ⟨id', su, m, a⟩ := d
      unfold add_composite_definitions at h_add
      split at h_add
      · -- composite_of_def returned error
        simp at h_add
      · -- composite_of_def returned ok co'
        rename_i co' heq_ok
        unfold composite_of_def at heq_ok
        split at heq_ok
        · -- env1.get? id' = some _ => error, contradiction
          simp at heq_ok
        · -- env1.get? id' = none, complete_members env1 m = false => error, contradiction
          simp at heq_ok
        · -- env1.get? id' = none, complete_members env1 m = true => ok, apply IH
          rename_i heq_get heq_comp
          apply ih _ _ h_add
          by_cases h_eq : id = id'
          · -- id = id' contradicts heq_get: env1.get? id' = none
            subst h_eq
            rw [h_env1] at heq_get
            simp at heq_get
          · -- id ≠ id', so insert doesn't affect lookup
            rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
            have h_ne : compare id' id ≠ Ordering.eq := by
              intro hc
              exact h_eq (Std.LawfulEqCmp.eq_of_compare hc).symm
            simp only [h_ne, if_false]
            rw [← Std.TreeMap.get?_eq_getElem?]
            exact h_env1

/- It follows that the sizes and alignments contained in the composite
   environment produced by [build_composite_env] are consistent with
   the sizes and alignments of the members of the composite types. -/

structure composite_consistent (env : composite_env) (co : composite) : Prop where
  co_consistent_complete : complete_members env (co.co_members) = true
  co_consistent_alignof : co.co_alignof = align_attr (co.co_attr) (alignof_composite env (co.co_members))
  co_consistent_sizeof : co.co_sizeof = align (sizeof_composite env (co.co_su) (co.co_members)) (co.co_alignof)
  co_consistent_rank : co.co_rank = rank_members env (co.co_members)

def composite_env_consistent (env : composite_env) : Prop :=
  ∀ id co, env.get? id = some co → composite_consistent env co

theorem composite_consistent_stable (env env' : composite_env)
    (env_extends : ∀ id co, env.get? id = some co → env'.get? id = some co)
    (co : composite) :
    composite_consistent env co → composite_consistent env' co := by
  intro h
  obtain ⟨hA, hB, hC, hD⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- complete_members env' co.co_members = true
    exact complete_members_stable env env' env_extends co.co_members hA
  · -- co.co_alignof = align_attr co.co_attr (alignof_composite env' co.co_members)
    rw [alignof_composite_stable env env' env_extends co.co_members hA]
    exact hB
  · -- co.co_sizeof = align (sizeof_composite env' co.co_su co.co_members) co.co_alignof
    rw [sizeof_composite_stable env env' env_extends co.co_su co.co_members hA]
    exact hC
  · -- co.co_rank = rank_members env' co.co_members
    rw [rank_members_stable env env' env_extends co.co_members hA]
    exact hD

theorem composite_of_def_consistent (env : composite_env) (id : ident) (su : struct_or_union) (m : members) (a : attr) (co : composite) :
    composite_of_def env id su m a = Except.ok co →
    composite_consistent env co := by
  intro h_def
  unfold composite_of_def at h_def
  split at h_def
  · -- env.get? id = some _ => error, contradiction
    simp at h_def
  · -- env.get? id = none, complete_members env m = false => error, contradiction
    simp at h_def
  · -- env.get? id = none, complete_members env m = true => ok
    rename_i h_none h_complete
    injection h_def with h_co_eq
    subst h_co_eq
    -- Now co is the composite built in composite_of_def
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- complete_members env co.co_members = true
      simp [h_complete]
    · -- co.co_alignof = align_attr co.co_attr (alignof_composite env co.co_members)
      simp
    · -- co.co_sizeof = align (sizeof_composite env co.co_su co.co_members) co.co_alignof
      simp
    · -- co.co_rank = rank_members env co.co_members
      simp

-- Helper lemma: add_composite_definitions preserves consistency
theorem add_composite_definitions_consistent (defs : List composite_definition) (env0 env : composite_env) :
    add_composite_definitions env0 defs = Except.ok env →
    composite_env_consistent env0 →
    composite_env_consistent env := by
  intro h_add h_cons0
  revert env0 env
  induction defs with
  | nil =>
    intro env0 env h_add h_cons0
    unfold add_composite_definitions at h_add
    injection h_add with h_eq
    rw [← h_eq]
    exact h_cons0
  | cons d defs ih =>
    intro env0 env h_add h_cons0
    cases d with
    | Composite id su m a =>
      unfold add_composite_definitions at h_add
      split at h_add
      · -- composite_of_def returned error
        contradiction
      · -- composite_of_def returned ok co
        rename_i co h_def
        -- h_add : add_composite_definitions (env0.insert id co) defs = Except.ok env
        -- h_def : composite_of_def env0 id su m a = Except.ok co
        have h_cons_env1 : composite_env_consistent (env0.insert id co) := by
          -- Need to show: composite_env_consistent (env0.insert id co)
          intro id' co' h_get'
          -- h_get' : (env0.insert id co).get? id' = some co'
          rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at h_get'
          by_cases h_eq : compare id id' = Ordering.eq
          · -- id = id' (via compare), so co' = co (the newly created composite)
            rw [if_pos h_eq] at h_get'
            injection h_get' with h_co_eq
            rw [← h_co_eq]
            -- co is consistent in env0 by composite_of_def_consistent
            have h_cons_co_env0 : composite_consistent env0 co :=
              composite_of_def_consistent env0 id su m a co h_def
            -- Lift to env1 = env0.insert id co using composite_consistent_stable
            apply composite_consistent_stable env0 (env0.insert id co) ?_ co h_cons_co_env0
            -- Show: env0 extends to env0.insert id co
            intro id'' co'' h_get''
            rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
            by_cases h_eq'' : compare id id'' = Ordering.eq
            · -- id = id'', but we know env0.get? id = none from composite_of_def
              have h_id_eq'' : id = id'' := Std.LawfulEqCmp.compare_eq_iff_eq.mp h_eq''
              have h_none : env0.get? id = none := by
                unfold composite_of_def at h_def
                split at h_def <;> try contradiction
                rename_i h_get_none _
                exact h_get_none
              rw [← h_id_eq''] at h_get''
              rw [h_none] at h_get''
              contradiction
            · rw [if_neg h_eq'']
              rw [← Std.TreeMap.get?_eq_getElem?]
              exact h_get''
          · -- id ≠ id' (via compare), so co' was already in env0
            rw [if_neg h_eq] at h_get'
            rw [← Std.TreeMap.get?_eq_getElem?] at h_get'
            -- co' is consistent in env0 by h_cons0
            have h_cons_env0 := h_cons0 id' co' h_get'
            -- Lift to env1 using composite_consistent_stable
            apply composite_consistent_stable env0 (env0.insert id co) ?_ co' h_cons_env0
            -- Show: env0 extends to env0.insert id co
            intro id'' co'' h_get''
            rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
            by_cases h_eq'' : compare id id'' = Ordering.eq
            · -- id = id'', but we know env0.get? id = none from composite_of_def
              have h_id_eq'' : id = id'' := Std.LawfulEqCmp.compare_eq_iff_eq.mp h_eq''
              have h_none : env0.get? id = none := by
                unfold composite_of_def at h_def
                split at h_def <;> try contradiction
                rename_i h_get_none _
                exact h_get_none
              rw [← h_id_eq''] at h_get''
              rw [h_none] at h_get''
              contradiction
            · rw [if_neg h_eq'']
              rw [← Std.TreeMap.get?_eq_getElem?]
              exact h_get''
        exact ih (env0.insert id co) env h_add h_cons_env1

theorem build_composite_env_consistent (defs : List composite_definition) (env : composite_env) :
    build_composite_env defs = Except.ok env →
    composite_env_consistent env := by
  intro h_build
  unfold build_composite_env at h_build
  apply add_composite_definitions_consistent defs ∅ env h_build
  -- Empty environment is trivially consistent
  intro id co h_empty
  have h_none : (∅ : composite_env).get? id = none := by
    rw [Std.TreeMap.get?_eq_getElem?]
    exact Std.TreeMap.getElem?_emptyc (a := id)
  rw [h_none] at h_empty
  contradiction

/- Moreover, every composite definition is reflected in the composite environment. -/

-- Helper lemma: add_composite_definitions reflects definitions
theorem add_composite_definitions_charact (env0 : composite_env) (id : ident) (su : struct_or_union) (m : members) (a : attr) (defs : List composite_definition) (env : composite_env) :
    add_composite_definitions env0 defs = Except.ok env →
    (composite_definition.Composite id su m a) ∈ defs →
    ∃ co, env.get? id = some co ∧ co.co_members = m ∧ co.co_attr = a ∧ co.co_su = su := by
  intro h_add h_in
  revert env0 env h_add h_in
  induction defs with
  | nil =>
    intro env0 env h_add h_in
    contradiction
  | cons d defs ih =>
    intro env0 env h_add h_in
    cases d with
    | Composite id' su' m' a' =>
      -- Convert membership to Or
      simp only [List.mem_cons] at h_in
      unfold add_composite_definitions at h_add
      split at h_add
      · -- composite_of_def returned error
        contradiction
      · -- composite_of_def returned ok co
        rename_i co h_def
        -- h_def : composite_of_def env0 id' su' m' a' = Except.ok co
        -- h_add : add_composite_definitions (env0.insert id' co) defs = Except.ok env
        cases h_in with
        | inl h_eq =>
          -- composite_definition.Composite id' su' m' a' = composite_definition.Composite id su m a
          injection h_eq with h_id h_su h_m h_a
          subst h_id h_su h_m h_a
          -- Now id' = id, su' = su, m' = m, a' = a (the primed vars are replaced by unprimed)
          -- Extract co's fields from composite_of_def
          have h_fields : co.co_members = m ∧ co.co_attr = a ∧ co.co_su = su := by
            unfold composite_of_def at h_def
            split at h_def <;> try contradiction
            injection h_def with h_co_eq
            subst h_co_eq
            simp
          obtain ⟨h_mem, h_attr, h_su_eq⟩ := h_fields
          -- Now show env.get? id = some co using add_composite_definitions_incr
          have h_get : env.get? id = some co := by
            apply add_composite_definitions_incr id co defs (env0.insert id co) env h_add
            rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]
          exact ⟨co, h_get, h_mem, h_attr, h_su_eq⟩
        | inr h_in_tail =>
          -- Composite id su m a ∈ defs, use IH
          exact ih (env0.insert id' co) env h_add h_in_tail

theorem build_composite_env_charact (id : ident) (su : struct_or_union) (m : members) (a : attr) (defs : List composite_definition) (env : composite_env) :
    build_composite_env defs = Except.ok env →
    (composite_definition.Composite id su m a) ∈ defs →
    ∃ co, env.get? id = some co ∧ co.co_members = m ∧ co.co_attr = a ∧ co.co_su = su := by
  intro h_build h_in
  unfold build_composite_env at h_build
  exact add_composite_definitions_charact ∅ id su m a defs env h_build h_in

theorem add_composite_definitions_domain (env0 : composite_env) (id : ident) (co : composite) (defs : List composite_definition) (env : composite_env) :
    add_composite_definitions env0 defs = Except.ok env →
    env.get? id = some co →
    (composite_definition.Composite id (co.co_su) (co.co_members) (co.co_attr)) ∈ defs ∨ env0.get? id = some co := by
  intro h_add h_get
  revert env0 env h_add h_get
  induction defs with
  | nil =>
    intro env0 env h_add h_get
    unfold add_composite_definitions at h_add
    injection h_add with h_eq
    rw [← h_eq] at h_get
    right
    exact h_get
  | cons head tail ih =>
    intro env0 env h_add h_get
    cases head with
    | Composite def_id def_su def_m def_a =>
      unfold add_composite_definitions at h_add
      split at h_add
      · -- Error case
        contradiction
      · -- Success case: composite_of_def returned Except.ok co_created
        rename_i co_created h_composite_eq
        -- h_add : add_composite_definitions (env0.insert def_id co_created) tail = Except.ok env
        -- h_composite_eq : composite_of_def env0 def_id def_su def_m def_a = Except.ok co_created
        have ih_result := ih (env0.insert def_id co_created) env h_add h_get
        cases ih_result with
        | inl h_in_tail =>
          left
          exact List.Mem.tail (composite_definition.Composite def_id def_su def_m def_a) h_in_tail
        | inr h_in_env0_insert =>
          -- h_in_env0_insert : (env0.insert def_id co_created).get? id = some co
          by_cases h_eq_id : id = def_id
          · -- If id = def_id, then co = co_created
            subst h_eq_id
            -- h_in_env0_insert : (env0.insert id co_created).get? id = some co
            -- Convert get? to [·]? notation
            change (env0.insert id co_created)[id]? = some co at h_in_env0_insert
            rw [Std.TreeMap.getElem?_insert_self] at h_in_env0_insert
            injection h_in_env0_insert with h_co_eq_created
            subst h_co_eq_created
            -- Now we need to show that co_created has the right properties
            -- From composite_of_def, we know the structure of co_created
            unfold composite_of_def at h_composite_eq
            split at h_composite_eq
            · contradiction
            · contradiction
            · injection h_composite_eq with h_struct_eq
              -- Now co_created equals the composite built in composite_of_def
              -- The built composite has co_su := def_su, co_members := def_m, co_attr := def_a
              -- So we need to show that the definition matches
              rw [← h_struct_eq]
              left
              exact List.Mem.head tail
          · -- If id ≠ def_id, then it was already in env0
            have h_ne : def_id ≠ id := Ne.symm h_eq_id
            -- Convert get? to [·]? notation
            change (env0.insert def_id co_created)[id]? = some co at h_in_env0_insert
            rw [Std.TreeMap.getElem?_insert] at h_in_env0_insert
            simp [h_ne] at h_in_env0_insert
            right
            exact h_in_env0_insert

theorem build_composite_env_domain (env : composite_env) (defs : List composite_definition) (id : ident) (co : composite) :
    build_composite_env defs = Except.ok env →
    env.get? id = some co →
    (composite_definition.Composite id (co.co_su) (co.co_members) (co.co_attr)) ∈ defs := by
  intro h_build h_get
  unfold build_composite_env at h_build
  have h_domain := add_composite_definitions_domain ∅ id co defs env h_build h_get
  cases h_domain with
  | inl h_in_defs =>
    exact h_in_defs
  | inr h_in_empty =>
    -- h_in_empty : (∅ : composite_env).get? id = some co
    -- But empty hash map has no entries, so this is a contradiction
    have h_none : (∅ : composite_env).get? id = none := by
      rw [Std.TreeMap.get?_eq_getElem?]
      exact Std.TreeMap.getElem?_emptyc (a := id)
    rw [h_none] at h_in_empty
    exact absurd h_in_empty (by simp)

/- As a corollary, in a consistent environment, the rank of a composite type
   is strictly greater than the ranks of its member types. -/

omit [Archi] in
lemma rank_type_members (ce : composite_env) (m : member) (ms : members) :
  List.contains ms m → rank_type ce (type_member m) ≤ rank_members ce ms := by
  intro h_contains
  induction ms with
  | nil =>
    cases h_contains
  | cons m' ms' ih =>
    unfold List.contains at h_contains
    rw [List.elem_cons] at h_contains
    split at h_contains
    · rename_i h_eq
      have : m = m' := beq_iff_eq.mp h_eq
      rw [this]
      cases m' with
      | Member_plain _ t =>
        unfold rank_members
        apply Nat.le_max_left
      | Member_bitfield _ _ _ _ _ _ =>
        unfold rank_members
        unfold type_member
        apply Nat.zero_le
    · unfold rank_members
      cases m' with
      | Member_plain _ t =>
        have ih_result := ih h_contains
        apply Nat.le_trans ih_result
        apply Nat.le_max_right
      | Member_bitfield _ _ _ _ _ _ =>
        exact ih h_contains

lemma rank_struct_member (ce : composite_env) (id : ident) (a : attr) (co : composite) (m : member) :
    composite_env_consistent ce →
    ce.get? id = some co →
    List.contains co.co_members m →
    rank_type ce (type_member m) < rank_type ce (type.Tstruct id a) := by
  intro h_cons h_get h_contains
  have h_co_cons : composite_consistent ce co := h_cons id co h_get
  have h_rank_eq : co.co_rank = rank_members ce co.co_members := h_co_cons.co_consistent_rank
  have h_le := rank_type_members ce m co.co_members h_contains
  have h_rhs : rank_type ce (type.Tstruct id a) = co.co_rank + 1 := by
    unfold rank_type
    rw [h_get]
  rw [h_rhs, h_rank_eq]
  omega

lemma rank_union_member (ce : composite_env) (id : ident) (a : attr) (co : composite) (m : member) :
    composite_env_consistent ce →
    ce.get? id = some co →
    List.contains co.co_members m →
    rank_type ce (type_member m) < rank_type ce (type.Tunion id a) := by
  intro h_cons h_get h_contains
  have h_co_cons : composite_consistent ce co := h_cons id co h_get
  have h_rank_eq : co.co_rank = rank_members ce co.co_members := h_co_cons.co_consistent_rank
  have h_le := rank_type_members ce m co.co_members h_contains
  have h_rhs : rank_type ce (type.Tunion id a) = co.co_rank + 1 := by
    unfold rank_type
    rw [h_get]
  rw [h_rhs, h_rank_eq]
  omega

-- * Programs and compilation units

/- The definitions in this section are parameterized over a type [F] of
  internal function definitions, so that they apply both to CompCert C and to Clight. -/

section PROGRAMS

variable (F : Type)

/- Functions can either be defined ([Internal]) or declared as
  external functions ([External]).

  WARNING: This redefines fundef from AST.lean to add type signature information
  for External functions (args, return type, calling convention). Cannot shadow the name imported from AST so need a new one. -/

inductive fundef_type : Type where
  | Internal : F → fundef_type
  | External : external_function → List type → type → calling_convention → fundef_type

/- A program, or compilation unit, is composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions.

Note: This extends AST.program with composite type information. -/

structure program_type : Type where
  prog_defs : List (ident × globdef (fundef_type F) type)
  prog_public : List ident
  prog_main : ident
  prog_types : List composite_definition
  prog_comp_env : composite_env
  prog_comp_env_eq : build_composite_env prog_types = Except.ok prog_comp_env

def program_of_program (p : program_type F) : program (fundef_type F) type :=
  { prog_defs := p.prog_defs,
    prog_public := p.prog_public,
    prog_main := p.prog_main }

instance : Coe (program_type F) (program (fundef_type F) type) where
  coe := program_of_program F

def make_program (types : List composite_definition)
                 (defs : List (ident × globdef (fundef_type F) type))
                 (pub : List ident)
                 (main : ident) : Except String (program_type F) :=
  match h : build_composite_env types with
  | Except.ok ce =>
      Except.ok { prog_defs := defs,
                  prog_public := pub,
                  prog_main := main,
                  prog_types := types,
                  prog_comp_env := ce,
                  prog_comp_env_eq := h }
  | Except.error e => Except.error e

/- Total variant of `make_program`, for callers who already know (or can
   cheaply check, via `decide`) that construction succeeds — e.g. ASTs
   produced by a trusted front end such as `clightgen`, mirroring the role
   Coq's `Clightdefs.mkprogram`/`wf_composites` (with its `Logic.I` proof)
   plays for generated `.v` files. Unlike Coq's version, no bespoke
   `wf_composites`-style `Prop` is needed: the default proof obligation
   below is discharged directly by `decide`, since `composite_env` is
   `Std.TreeMap`-backed and `build_composite_env` reduces cleanly under the
   kernel (no `native_decide`, no added trust beyond the kernel every other
   proof in this repo already relies on). `make_program` itself remains
   available unchanged for callers that want the error message on
   failure (e.g. tests asserting that malformed input is rejected). -/
def make_program! (types : List composite_definition)
                  (defs : List (ident × globdef (fundef_type F) type))
                  (pub : List ident)
                  (main : ident)
                  (h : (make_program F types defs pub main).isOk = true := by decide) :
    program_type F :=
  match hm : make_program F types defs pub main, h with
  | Except.ok p, _ => p
  | Except.error _, h => absurd h (by simp [Except.isOk, Except.toBool])

end PROGRAMS

/- Note: The remainder of Ctypes.v (lines 1575-2016) contains definitions and theorems
   for compilation and linking. They are omitted for now. -/
