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

-- Arithmetic and logical operators for the Compcert C and Clight languages

import CLightLean.AST
import CLightLean.CTypes
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats
import CLightLean.Values
import CLightLean.Memory
import CLightLean.CTypes
import CLightLean.Archi

open Memory (mem weak_valid_pointer)

variable [Archi]

-- * Syntax of operators.

/-- Unary operators. -/
inductive unary_operation : Type where
  | Onotbool  -- boolean negation (`!` in C)
  | Onotint   -- integer complement (`~` in C)
  | Oneg      -- opposite (unary `-`)
  | Oabsfloat -- floating-point absolute value
  deriving DecidableEq

/-- Binary operators. -/
inductive binary_operation : Type where
  | Oadd  -- addition (binary `+`)
  | Osub  -- subtraction (binary `-`)
  | Omul  -- multiplication (binary `*`)
  | Odiv  -- division (`/`)
  | Omod  -- remainder (`%`)
  | Oand  -- bitwise and (`&`)
  | Oor   -- bitwise or (`|`)
  | Oxor  -- bitwise xor (`^`)
  | Oshl  -- left shift (`<<`)
  | Oshr  -- right shift (`>>`)
  | Oeq   -- comparison (`==`)
  | One   -- comparison (`!=`)
  | Olt   -- comparison (`<`)
  | Ogt   -- comparison (`>`)
  | Ole   -- comparison (`<=`)
  | Oge   -- comparison (`>=`)
  deriving DecidableEq

/-- Distinguishes `++` from `--`. -/
inductive incr_or_decr : Type where
  | Incr
  | Decr
  deriving DecidableEq

-- * Type classification and semantics of operators.

/-
Most C operators are overloaded (they apply to arguments of various
types) and their semantics depend on the types of their arguments.
The following `classify_*` functions take as arguments the types
of the arguments of an operation. They return enough information
to resolve overloading for this operator application, such as
"both arguments are floats", or "the first is a pointer
and the second is an integer". This classification is used in the
compiler (module `Cshmgen`) to resolve overloading statically.

The `sem_*` functions below compute the result of an operator
application. Since operators are overloaded, the result depends
both on the static types of the arguments and on their run-time values.
The corresponding `classify_*` function is first called on the
types of the arguments to resolve static overloading. It is then
followed by a case analysis on the values of the arguments.
-/

-- ** Casts and truth values

inductive classify_cast_cases : Type where
  | cast_case_pointer                                  -- between pointer types or intptr_t types
  | cast_case_i2i (sz2 : intsize) (si2 : signedness)    -- int -> int
  | cast_case_f2f                                       -- double -> double
  | cast_case_s2s                                       -- single -> single
  | cast_case_f2s                                       -- double -> single
  | cast_case_s2f                                       -- single -> double
  | cast_case_i2f (si1 : signedness)                    -- int -> double
  | cast_case_i2s (si1 : signedness)                    -- int -> single
  | cast_case_f2i (sz2 : intsize) (si2 : signedness)    -- double -> int
  | cast_case_s2i (sz2 : intsize) (si2 : signedness)    -- single -> int
  | cast_case_l2l                                       -- long -> long
  | cast_case_i2l (si1 : signedness)                    -- int -> long
  | cast_case_l2i (sz2 : intsize) (si2 : signedness)    -- long -> int
  | cast_case_l2f (si1 : signedness)                    -- long -> double
  | cast_case_l2s (si1 : signedness)                    -- long -> single
  | cast_case_f2l (si2 : signedness)                    -- double -> long
  | cast_case_s2l (si2 : signedness)                    -- single -> long
  | cast_case_i2bool                                    -- int -> bool
  | cast_case_l2bool                                    -- long -> bool
  | cast_case_f2bool                                    -- double -> bool
  | cast_case_s2bool                                    -- single -> bool
  | cast_case_struct (id1 id2 : ident)                  -- struct -> struct
  | cast_case_union (id1 id2 : ident)                   -- union -> union
  | cast_case_void                                      -- any -> void
  | cast_case_default
  deriving DecidableEq

def classify_cast (tfrom tto : type) : classify_cast_cases :=
  match tto, tfrom with
  -- To `void`
  | .Tvoid, _ => .cast_case_void
  -- To `int`
  | .Tint sz2 si2 _, .Tint _ _ _ =>
      match sz2 with
      | .IBool => .cast_case_i2bool
      | .I32 => if Archi.ptr64 then .cast_case_i2i sz2 si2 else .cast_case_pointer
      | _ => .cast_case_i2i sz2 si2
  | .Tint sz2 si2 _, .Tlong _ _ =>
      if sz2 = .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F64 _ =>
      if sz2 = .IBool then .cast_case_f2bool else .cast_case_f2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F32 _ =>
      if sz2 = .IBool then .cast_case_s2bool else .cast_case_s2i sz2 si2
  | .Tint sz2 si2 _, .Tpointer _ _
  | .Tint sz2 si2 _, .Tarray _ _ _
  | .Tint sz2 si2 _, .Tfunction _ _ _ =>
      if Archi.ptr64 then  -- like long to int
        if sz2 = .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
      else
        match sz2 with  -- like int to int
        | .IBool => .cast_case_i2bool
        | .I32 => .cast_case_pointer
        | _ => .cast_case_i2i sz2 si2
  -- To `long`
  | .Tlong _ _, .Tlong _ _ =>
      if Archi.ptr64 then .cast_case_pointer else .cast_case_l2l
  | .Tlong _ _, .Tint _ si1 _ => .cast_case_i2l si1
  | .Tlong si2 _, .Tfloat .F64 _ => .cast_case_f2l si2
  | .Tlong si2 _, .Tfloat .F32 _ => .cast_case_s2l si2
  | .Tlong si2 _, .Tpointer _ _
  | .Tlong si2 _, .Tarray _ _ _
  | .Tlong si2 _, .Tfunction _ _ _ =>
      if Archi.ptr64 then .cast_case_pointer else .cast_case_i2l si2
  -- To `float`
  | .Tfloat .F64 _, .Tint _ si1 _ => .cast_case_i2f si1
  | .Tfloat .F32 _, .Tint _ si1 _ => .cast_case_i2s si1
  | .Tfloat .F64 _, .Tlong si1 _ => .cast_case_l2f si1
  | .Tfloat .F32 _, .Tlong si1 _ => .cast_case_l2s si1
  | .Tfloat .F64 _, .Tfloat .F64 _ => .cast_case_f2f
  | .Tfloat .F32 _, .Tfloat .F32 _ => .cast_case_s2s
  | .Tfloat .F64 _, .Tfloat .F32 _ => .cast_case_s2f
  | .Tfloat .F32 _, .Tfloat .F64 _ => .cast_case_f2s
  -- To pointer types
  | .Tpointer _ _, .Tint _ si _ =>
      if Archi.ptr64 then .cast_case_i2l si else .cast_case_pointer
  | .Tpointer _ _, .Tlong _ _ =>
      if Archi.ptr64 then .cast_case_pointer else .cast_case_l2i .I32 .Unsigned
  | .Tpointer _ _, .Tpointer _ _
  | .Tpointer _ _, .Tarray _ _ _
  | .Tpointer _ _, .Tfunction _ _ _ => .cast_case_pointer
  -- To struct or union types
  | .Tstruct id2 _, .Tstruct id1 _ => .cast_case_struct id1 id2
  | .Tunion id2 _, .Tunion id1 _ => .cast_case_union id1 id2
  -- Catch-all
  | _, _ => .cast_case_default

/-
Semantics of casts. `sem_cast v1 t1 t2 m = Some v2` if value `v1`,
viewed with static type `t1`, can be converted to type `t2`,
resulting in value `v2`.
-/

def cast_int_int (sz : intsize) (sg : signedness) (i : CompCert.Int) : CompCert.Int :=
  match sz, sg with
  | .I8, .Signed => CompCert.Int.sign_ext 8 i
  | .I8, .Unsigned => CompCert.Int.zero_ext 8 i
  | .I16, .Signed => CompCert.Int.sign_ext 16 i
  | .I16, .Unsigned => CompCert.Int.zero_ext 16 i
  | .I32, _ => i
  | .IBool, _ => if CompCert.Int.eq i CompCert.Int.zero then CompCert.Int.zero else CompCert.Int.one

def cast_int_float (si : signedness) (i : CompCert.Int) : CompCert.Float64 :=
  match si with
  | .Signed => CompCert.Float64.of_int i
  | .Unsigned => CompCert.Float64.of_intu i

def cast_float_int (si : signedness) (f : CompCert.Float64) : Option CompCert.Int :=
  match si with
  | .Signed => CompCert.Float64.to_int f
  | .Unsigned => CompCert.Float64.to_intu f

def cast_int_single (si : signedness) (i : CompCert.Int) : CompCert.Float32 :=
  match si with
  | .Signed => CompCert.Float32.of_int i
  | .Unsigned => CompCert.Float32.of_intu i

def cast_single_int (si : signedness) (f : CompCert.Float32) : Option CompCert.Int :=
  match si with
  | .Signed => CompCert.Float32.to_int f
  | .Unsigned => CompCert.Float32.to_intu f

def cast_int_long (si : signedness) (i : CompCert.Int) : CompCert.Int64 :=
  match si with
  | .Signed => CompCert.Int64.repr i.signed
  | .Unsigned => CompCert.Int64.repr i.unsigned

def cast_long_float (si : signedness) (i : CompCert.Int64) : CompCert.Float64 :=
  match si with
  | .Signed => CompCert.Float64.of_long i
  | .Unsigned => CompCert.Float64.of_longu i

def cast_long_single (si : signedness) (i : CompCert.Int64) : CompCert.Float32 :=
  match si with
  | .Signed => CompCert.Float32.of_long i
  | .Unsigned => CompCert.Float32.of_longu i

def cast_float_long (si : signedness) (f : CompCert.Float64) : Option CompCert.Int64 :=
  match si with
  | .Signed => CompCert.Float64.to_long f
  | .Unsigned => CompCert.Float64.to_longu f

def cast_single_long (si : signedness) (f : CompCert.Float32) : Option CompCert.Int64 :=
  match si with
  | .Signed => CompCert.Float32.to_long f
  | .Unsigned => CompCert.Float32.to_longu f

def sem_cast (v : val) (t1 t2 : type) (m : mem) : Option val :=
  match classify_cast t1 t2 with
  | .cast_case_pointer =>
      match v with
      | .Vptr _ _ => some v
      | .Vint _ => if Archi.ptr64 then none else some v
      | .Vlong _ => if Archi.ptr64 then some v else none
      | _ => none
  | .cast_case_i2i sz2 si2 =>
      match v with
      | .Vint i => some (.Vint (cast_int_int sz2 si2 i))
      | _ => none
  | .cast_case_f2f =>
      match v with
      | .Vfloat f => some (.Vfloat f)
      | _ => none
  | .cast_case_s2s =>
      match v with
      | .Vsingle f => some (.Vsingle f)
      | _ => none
  | .cast_case_s2f =>
      match v with
      | .Vsingle f => some (.Vfloat (CompCert.Float64.of_single f))
      | _ => none
  | .cast_case_f2s =>
      match v with
      | .Vfloat f => some (.Vsingle (CompCert.Float64.to_single f))
      | _ => none
  | .cast_case_i2f si1 =>
      match v with
      | .Vint i => some (.Vfloat (cast_int_float si1 i))
      | _ => none
  | .cast_case_i2s si1 =>
      match v with
      | .Vint i => some (.Vsingle (cast_int_single si1 i))
      | _ => none
  | .cast_case_f2i sz2 si2 =>
      match v with
      | .Vfloat f =>
          match cast_float_int si2 f with
          | some i => some (.Vint (cast_int_int sz2 si2 i))
          | none => none
      | _ => none
  | .cast_case_s2i sz2 si2 =>
      match v with
      | .Vsingle f =>
          match cast_single_int si2 f with
          | some i => some (.Vint (cast_int_int sz2 si2 i))
          | none => none
      | _ => none
  | .cast_case_i2bool =>
      match v with
      | .Vint n =>
          some (.Vint (if CompCert.Int.eq n CompCert.Int.zero then CompCert.Int.zero else CompCert.Int.one))
      | .Vptr b ofs =>
          if Archi.ptr64 then none else
          if weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_l2bool =>
      match v with
      | .Vlong n =>
          some (.Vint (if CompCert.Int64.eq n CompCert.Int64.zero then CompCert.Int.zero else CompCert.Int.one))
      | .Vptr b ofs =>
          if !Archi.ptr64 then none else
          if weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_f2bool =>
      match v with
      | .Vfloat f =>
          some (.Vint (if CompCert.Float64.cmp .Ceq f CompCert.Float64.zero then CompCert.Int.zero else CompCert.Int.one))
      | _ => none
  | .cast_case_s2bool =>
      match v with
      | .Vsingle f =>
          some (.Vint (if CompCert.Float32.cmp .Ceq f CompCert.Float32.zero then CompCert.Int.zero else CompCert.Int.one))
      | _ => none
  | .cast_case_l2l =>
      match v with
      | .Vlong n => some (.Vlong n)
      | _ => none
  | .cast_case_i2l si =>
      match v with
      | .Vint n => some (.Vlong (cast_int_long si n))
      | _ => none
  | .cast_case_l2i sz si =>
      match v with
      | .Vlong n => some (.Vint (cast_int_int sz si (CompCert.Int.repr n.unsigned)))
      | _ => none
  | .cast_case_l2f si1 =>
      match v with
      | .Vlong i => some (.Vfloat (cast_long_float si1 i))
      | _ => none
  | .cast_case_l2s si1 =>
      match v with
      | .Vlong i => some (.Vsingle (cast_long_single si1 i))
      | _ => none
  | .cast_case_f2l si2 =>
      match v with
      | .Vfloat f =>
          match cast_float_long si2 f with
          | some i => some (.Vlong i)
          | none => none
      | _ => none
  | .cast_case_s2l si2 =>
      match v with
      | .Vsingle f =>
          match cast_single_long si2 f with
          | some i => some (.Vlong i)
          | none => none
      | _ => none
  | .cast_case_struct id1 id2 =>
      match v with
      | .Vptr _ _ => if id1 = id2 then some v else none
      | _ => none
  | .cast_case_union id1 id2 =>
      match v with
      | .Vptr _ _ => if id1 = id2 then some v else none
      | _ => none
  | .cast_case_void => some v
  | .cast_case_default => none

/-
The following describes types that can be interpreted as a boolean:
integers, floats, pointers. It is used for the semantics of
the `!` and `?` operators, as well as the `if`, `while`,
and `for` statements.
-/

inductive classify_bool_cases : Type where
  | bool_case_i  -- integer
  | bool_case_l  -- long
  | bool_case_f  -- double float
  | bool_case_s  -- single float
  | bool_default
  deriving DecidableEq

def classify_bool (ty : type) : classify_bool_cases :=
  match typeconv ty with
  | .Tint _ _ _ => .bool_case_i
  | .Tpointer _ _ => if Archi.ptr64 then .bool_case_l else .bool_case_i
  | .Tfloat .F64 _ => .bool_case_f
  | .Tfloat .F32 _ => .bool_case_s
  | .Tlong _ _ => .bool_case_l
  | _ => .bool_default

/-
Interpretation of values as truth values.
Non-zero integers, non-zero floats and non-null pointers are
considered as true. The integer zero (which also represents
the null pointer) and the float 0.0 are false.
-/

def bool_val (v : val) (t : type) (m : mem) : Option Bool :=
  match classify_bool t with
  | .bool_case_i =>
      match v with
      | .Vint n => some (!(CompCert.Int.eq n CompCert.Int.zero))
      | .Vptr b ofs =>
          if Archi.ptr64 then none else
          if weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_l =>
      match v with
      | .Vlong n => some (!(CompCert.Int64.eq n CompCert.Int64.zero))
      | .Vptr b ofs =>
          if !Archi.ptr64 then none else
          if weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_f =>
      match v with
      | .Vfloat f => some (!(CompCert.Float64.cmp .Ceq f CompCert.Float64.zero))
      | _ => none
  | .bool_case_s =>
      match v with
      | .Vsingle f => some (!(CompCert.Float32.cmp .Ceq f CompCert.Float32.zero))
      | _ => none
  | .bool_default => none

-- ** Unary operators

-- *** Boolean negation

def sem_notbool (v : val) (ty : type) (m : mem) : Option val :=
  (bool_val v ty m).map (fun b => Val.of_bool (!b))

-- *** Opposite and absolute value

inductive classify_neg_cases : Type where
  | neg_case_i (s : signedness)  -- int
  | neg_case_f                   -- double float
  | neg_case_s                   -- single float
  | neg_case_l (s : signedness)  -- long
  | neg_default
  deriving DecidableEq

def classify_neg (ty : type) : classify_neg_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .neg_case_i .Unsigned
  | .Tint _ _ _ => .neg_case_i .Signed
  | .Tfloat .F64 _ => .neg_case_f
  | .Tfloat .F32 _ => .neg_case_s
  | .Tlong si _ => .neg_case_l si
  | _ => .neg_default

def sem_neg (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i _ =>
      match v with
      | .Vint n => some (.Vint (CompCert.Int.neg n))
      | _ => none
  | .neg_case_f =>
      match v with
      | .Vfloat f => some (.Vfloat (CompCert.Float64.neg f))
      | _ => none
  | .neg_case_s =>
      match v with
      | .Vsingle f => some (.Vsingle (CompCert.Float32.neg f))
      | _ => none
  | .neg_case_l _ =>
      match v with
      | .Vlong n => some (.Vlong (CompCert.Int64.neg n))
      | _ => none
  | .neg_default => none

def sem_absfloat (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i sg =>
      match v with
      | .Vint n => some (.Vfloat (CompCert.Float64.abs (cast_int_float sg n)))
      | _ => none
  | .neg_case_f =>
      match v with
      | .Vfloat f => some (.Vfloat (CompCert.Float64.abs f))
      | _ => none
  | .neg_case_s =>
      match v with
      | .Vsingle f => some (.Vfloat (CompCert.Float64.abs (CompCert.Float64.of_single f)))
      | _ => none
  | .neg_case_l sg =>
      match v with
      | .Vlong n => some (.Vfloat (CompCert.Float64.abs (cast_long_float sg n)))
      | _ => none
  | .neg_default => none

-- *** Bitwise complement

inductive classify_notint_cases : Type where
  | notint_case_i (s : signedness)  -- int
  | notint_case_l (s : signedness)  -- long
  | notint_default
  deriving DecidableEq

def classify_notint (ty : type) : classify_notint_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .notint_case_i .Unsigned
  | .Tint _ _ _ => .notint_case_i .Signed
  | .Tlong si _ => .notint_case_l si
  | _ => .notint_default

def sem_notint (v : val) (ty : type) : Option val :=
  match classify_notint ty with
  | .notint_case_i _ =>
      match v with
      | .Vint n => some (.Vint (CompCert.Int.not n))
      | _ => none
  | .notint_case_l _ =>
      match v with
      | .Vlong n => some (.Vlong (CompCert.Int64.not n))
      | _ => none
  | .notint_default => none

-- ** Binary operators

/-
For binary operations, the "usual binary conversions" consist in
- determining the type at which the operation is to be performed
  (a form of least upper bound of the types of the two arguments);
- casting the two arguments to this common type;
- performing the operation at that type.
-/

inductive binarith_cases : Type where
  | bin_case_i (s : signedness)  -- at int type
  | bin_case_l (s : signedness)  -- at long int type
  | bin_case_f                   -- at double float type
  | bin_case_s                   -- at single float type
  | bin_default                  -- error
  deriving DecidableEq

def classify_binarith (ty1 ty2 : type) : binarith_cases :=
  match ty1, ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint .I32 .Unsigned _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .bin_case_i .Signed
  | .Tlong .Signed _, .Tlong .Signed _ => .bin_case_l .Signed
  | .Tlong _ _, .Tlong _ _ => .bin_case_l .Unsigned
  | .Tlong sg _, .Tint _ _ _ => .bin_case_l sg
  | .Tint _ _ _, .Tlong sg _ => .bin_case_l sg
  | .Tfloat .F32 _, .Tfloat .F32 _ => .bin_case_s
  | .Tfloat _ _, .Tfloat _ _ => .bin_case_f
  | .Tfloat .F64 _, .Tint _ _ _ => .bin_case_f
  | .Tfloat .F64 _, .Tlong _ _ => .bin_case_f
  | .Tint _ _ _, .Tfloat .F64 _ => .bin_case_f
  | .Tlong _ _, .Tfloat .F64 _ => .bin_case_f
  | .Tfloat .F32 _, .Tint _ _ _ => .bin_case_s
  | .Tfloat .F32 _, .Tlong _ _ => .bin_case_s
  | .Tint _ _ _, .Tfloat .F32 _ => .bin_case_s
  | .Tlong _ _, .Tfloat .F32 _ => .bin_case_s
  | _, _ => .bin_default

-- The static type of the result. Both arguments are converted to this type
-- before the actual computation.

def binarith_type (c : binarith_cases) : type :=
  match c with
  | .bin_case_i sg => .Tint .I32 sg noattr
  | .bin_case_l sg => .Tlong sg noattr
  | .bin_case_f => .Tfloat .F64 noattr
  | .bin_case_s => .Tfloat .F32 noattr
  | .bin_default => .Tvoid

def sem_binarith
    (sem_int : signedness → CompCert.Int → CompCert.Int → Option val)
    (sem_long : signedness → CompCert.Int64 → CompCert.Int64 → Option val)
    (sem_float : CompCert.Float64 → CompCert.Float64 → Option val)
    (sem_single : CompCert.Float32 → CompCert.Float32 → Option val)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  let c := classify_binarith t1 t2
  let t := binarith_type c
  match sem_cast v1 t1 t m with
  | none => none
  | some v1' =>
  match sem_cast v2 t2 t m with
  | none => none
  | some v2' =>
  match c with
  | .bin_case_i sg =>
      match v1', v2' with
      | .Vint n1, .Vint n2 => sem_int sg n1 n2
      | _, _ => none
  | .bin_case_f =>
      match v1', v2' with
      | .Vfloat n1, .Vfloat n2 => sem_float n1 n2
      | _, _ => none
  | .bin_case_s =>
      match v1', v2' with
      | .Vsingle n1, .Vsingle n2 => sem_single n1 n2
      | _, _ => none
  | .bin_case_l sg =>
      match v1', v2' with
      | .Vlong n1, .Vlong n2 => sem_long sg n1 n2
      | _, _ => none
  | .bin_default => none

-- *** Addition

inductive classify_add_cases : Type where
  | add_case_pi (ty : type) (si : signedness)  -- pointer, int
  | add_case_pl (ty : type)                    -- pointer, long
  | add_case_ip (si : signedness) (ty : type)  -- int, pointer
  | add_case_lp (ty : type)                    -- long, pointer
  | add_default                                -- numerical type, numerical type
  deriving DecidableEq

def classify_add (ty1 ty2 : type) : classify_add_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .add_case_pi ty si
  | .Tpointer ty _, .Tlong _ _ => .add_case_pl ty
  | .Tint _ si _, .Tpointer ty _ => .add_case_ip si ty
  | .Tlong _ _, .Tpointer ty _ => .add_case_lp ty
  | _, _ => .add_default

def ptrofs_of_int (si : signedness) (n : CompCert.Int) : ptrofs :=
  match si with
  | .Signed => Ptrofs.of_int n
  | .Unsigned => Ptrofs.of_intu n

def sem_add_ptr_int (cenv : composite_env) (ty : type) (si : signedness) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vint n2 =>
      let n2 := ptrofs_of_int si n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | .Vint n1, .Vint n2 =>
      if Archi.ptr64 then none else
        some (.Vint (CompCert.Int.add n1 (CompCert.Int.mul (CompCert.Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vint n2 =>
      let n2 := cast_int_long si n2
      if Archi.ptr64 then
        some (.Vlong (CompCert.Int64.add n1 (CompCert.Int64.mul (CompCert.Int64.repr (sizeof cenv ty)) n2)))
      else none
  | _, _ => none

def sem_add_ptr_long (cenv : composite_env) (ty : type) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vlong n2 =>
      let n2 := Ptrofs.of_int64 n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | .Vint n1, .Vlong n2 =>
      let n2 := CompCert.Int.repr (CompCert.Int64.unsigned n2)
      if Archi.ptr64 then none else
        some (.Vint (CompCert.Int.add n1 (CompCert.Int.mul (CompCert.Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vlong n2 =>
      if Archi.ptr64 then
        some (.Vlong (CompCert.Int64.add n1 (CompCert.Int64.mul (CompCert.Int64.repr (sizeof cenv ty)) n2)))
      else none
  | _, _ => none

def sem_add (cenv : composite_env) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_add t1 t2 with
  | .add_case_pi ty si =>  -- pointer plus integer
      sem_add_ptr_int cenv ty si v1 v2
  | .add_case_pl ty =>     -- pointer plus long
      sem_add_ptr_long cenv ty v1 v2
  | .add_case_ip si ty =>  -- integer plus pointer
      sem_add_ptr_int cenv ty si v2 v1
  | .add_case_lp ty =>     -- long plus pointer
      sem_add_ptr_long cenv ty v2 v1
  | .add_default =>
      sem_binarith
        (fun _ n1 n2 => some (.Vint (CompCert.Int.add n1 n2)))
        (fun _ n1 n2 => some (.Vlong (CompCert.Int64.add n1 n2)))
        (fun n1 n2 => some (.Vfloat (CompCert.Float64.add n1 n2).value))
        (fun n1 n2 => some (.Vsingle (CompCert.Float32.add n1 n2).value))
        v1 t1 v2 t2 m

-- *** Subtraction

inductive classify_sub_cases : Type where
  | sub_case_pi (ty : type) (si : signedness)  -- pointer, int
  | sub_case_pp (ty : type)                    -- pointer, pointer
  | sub_case_pl (ty : type)                    -- pointer, long
  | sub_default                                -- numerical type, numerical type
  deriving DecidableEq

def classify_sub (ty1 ty2 : type) : classify_sub_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .sub_case_pi ty si
  | .Tpointer ty _, .Tpointer _ _ => .sub_case_pp ty
  | .Tpointer ty _, .Tlong _ _ => .sub_case_pl ty
  | _, _ => .sub_default

def sem_sub (cenv : composite_env) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_sub t1 t2 with
  | .sub_case_pi ty si =>  -- pointer minus integer
      match v1, v2 with
      | .Vptr b1 ofs1, .Vint n2 =>
          let n2 := ptrofs_of_int si n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | .Vint n1, .Vint n2 =>
          if Archi.ptr64 then none else
            some (.Vint (CompCert.Int.sub n1 (CompCert.Int.mul (CompCert.Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vint n2 =>
          let n2 := cast_int_long si n2
          if Archi.ptr64 then
            some (.Vlong (CompCert.Int64.sub n1 (CompCert.Int64.mul (CompCert.Int64.repr (sizeof cenv ty)) n2)))
          else none
      | _, _ => none
  | .sub_case_pl ty =>  -- pointer minus long
      match v1, v2 with
      | .Vptr b1 ofs1, .Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | .Vint n1, .Vlong n2 =>
          let n2 := CompCert.Int.repr (CompCert.Int64.unsigned n2)
          if Archi.ptr64 then none else
            some (.Vint (CompCert.Int.sub n1 (CompCert.Int.mul (CompCert.Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vlong n2 =>
          if Archi.ptr64 then
            some (.Vlong (CompCert.Int64.sub n1 (CompCert.Int64.mul (CompCert.Int64.repr (sizeof cenv ty)) n2)))
          else none
      | _, _ => none
  | .sub_case_pp ty =>  -- pointer minus pointer
      match v1, v2 with
      | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
          if b1 == b2 then
            let sz := sizeof cenv ty
            if 0 < sz && sz ≤ Ptrofs.max_signed
            then some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else none
          else none
      | _, _ => none
  | .sub_default =>
      sem_binarith
        (fun _ n1 n2 => some (.Vint (CompCert.Int.sub n1 n2)))
        (fun _ n1 n2 => some (.Vlong (CompCert.Int64.sub n1 n2)))
        (fun n1 n2 => some (.Vfloat (CompCert.Float64.sub n1 n2).value))
        (fun n1 n2 => some (.Vsingle (CompCert.Float32.sub n1 n2).value))
        v1 t1 v2 t2 m

-- *** Multiplication, division, modulus

def sem_mul (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (CompCert.Int.mul n1 n2)))
    (fun _ n1 n2 => some (.Vlong (CompCert.Int64.mul n1 n2)))
    (fun n1 n2 => some (.Vfloat (CompCert.Float64.mul n1 n2).value))
    (fun n1 n2 => some (.Vsingle (CompCert.Float32.mul n1 n2).value))
    v1 t1 v2 t2 m

def sem_div (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if CompCert.Int.eq n2 CompCert.Int.zero
             || (CompCert.Int.eq n1 (CompCert.Int.repr CompCert.Int.min_signed) && CompCert.Int.eq n2 CompCert.Int.mone)
          then none else some (.Vint (CompCert.Int.divs n1 n2))
      | .Unsigned =>
          if CompCert.Int.eq n2 CompCert.Int.zero
          then none else some (.Vint (CompCert.Int.divu n1 n2)))
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if CompCert.Int64.eq n2 CompCert.Int64.zero
             || (CompCert.Int64.eq n1 (CompCert.Int64.repr CompCert.Int64.min_signed) && CompCert.Int64.eq n2 CompCert.Int64.mone)
          then none else some (.Vlong (CompCert.Int64.divs n1 n2))
      | .Unsigned =>
          if CompCert.Int64.eq n2 CompCert.Int64.zero
          then none else some (.Vlong (CompCert.Int64.divu n1 n2)))
    (fun n1 n2 => some (.Vfloat (CompCert.Float64.div n1 n2).value))
    (fun n1 n2 => some (.Vsingle (CompCert.Float32.div n1 n2).value))
    v1 t1 v2 t2 m

def sem_mod (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if CompCert.Int.eq n2 CompCert.Int.zero
             || (CompCert.Int.eq n1 (CompCert.Int.repr CompCert.Int.min_signed) && CompCert.Int.eq n2 CompCert.Int.mone)
          then none else some (.Vint (CompCert.Int.mods n1 n2))
      | .Unsigned =>
          if CompCert.Int.eq n2 CompCert.Int.zero
          then none else some (.Vint (CompCert.Int.modu n1 n2)))
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if CompCert.Int64.eq n2 CompCert.Int64.zero
             || (CompCert.Int64.eq n1 (CompCert.Int64.repr CompCert.Int64.min_signed) && CompCert.Int64.eq n2 CompCert.Int64.mone)
          then none else some (.Vlong (CompCert.Int64.mods n1 n2))
      | .Unsigned =>
          if CompCert.Int64.eq n2 CompCert.Int64.zero
          then none else some (.Vlong (CompCert.Int64.modu n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

def sem_and (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (CompCert.Int.and n1 n2)))
    (fun _ n1 n2 => some (.Vlong (CompCert.Int64.and n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

def sem_or (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (CompCert.Int.or n1 n2)))
    (fun _ n1 n2 => some (.Vlong (CompCert.Int64.or n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

def sem_xor (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith
    (fun _ n1 n2 => some (.Vint (CompCert.Int.xor n1 n2)))
    (fun _ n1 n2 => some (.Vlong (CompCert.Int64.xor n1 n2)))
    (fun _ _ => none)
    (fun _ _ => none)
    v1 t1 v2 t2 m

-- *** Shifts

/-
Shifts do not perform the usual binary conversions.  Instead,
each argument is converted independently, and the signedness
of the result is always that of the first argument.
-/

inductive classify_shift_cases : Type where
  | shift_case_ii (s : signedness)  -- int, int
  | shift_case_ll (s : signedness)  -- long, long
  | shift_case_il (s : signedness)  -- int, long
  | shift_case_li (s : signedness)  -- long, int
  | shift_default
  deriving DecidableEq

def classify_shift (ty1 ty2 : type) : classify_shift_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .shift_case_ii .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .shift_case_ii .Signed
  | .Tint .I32 .Unsigned _, .Tlong _ _ => .shift_case_il .Unsigned
  | .Tint _ _ _, .Tlong _ _ => .shift_case_il .Signed
  | .Tlong s _, .Tint _ _ _ => .shift_case_li s
  | .Tlong s _, .Tlong _ _ => .shift_case_ll s
  | _, _ => .shift_default

def sem_shift
    (sem_int : signedness → CompCert.Int → CompCert.Int → CompCert.Int)
    (sem_long : signedness → CompCert.Int64 → CompCert.Int64 → CompCert.Int64)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  match classify_shift t1 t2 with
  | .shift_case_ii sg =>
      match v1, v2 with
      | .Vint n1, .Vint n2 =>
          if CompCert.Int.ltu n2 CompCert.Int.iwordsize
          then some (.Vint (sem_int sg n1 n2)) else none
      | _, _ => none
  | .shift_case_il sg =>
      match v1, v2 with
      | .Vint n1, .Vlong n2 =>
          if CompCert.Int64.ltu n2 (CompCert.Int64.repr 32)
          then some (.Vint (sem_int sg n1 (CompCert.Int64.loword n2))) else none
      | _, _ => none
  | .shift_case_li sg =>
      match v1, v2 with
      | .Vlong n1, .Vint n2 =>
          if CompCert.Int.ltu n2 CompCert.Int64.iwordsize'
          then some (.Vlong (sem_long sg n1 (CompCert.Int64.repr (CompCert.Int.unsigned n2)))) else none
      | _, _ => none
  | .shift_case_ll sg =>
      match v1, v2 with
      | .Vlong n1, .Vlong n2 =>
          if CompCert.Int64.ltu n2 CompCert.Int64.iwordsize
          then some (.Vlong (sem_long sg n1 n2)) else none
      | _, _ => none
  | .shift_default => none

def sem_shl (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift
    (fun _ n1 n2 => CompCert.Int.shl n1 n2)
    (fun _ n1 n2 => CompCert.Int64.shl n1 n2)
    v1 t1 v2 t2

def sem_shr (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift
    (fun sg n1 n2 => match sg with | .Signed => CompCert.Int.shr n1 n2 | .Unsigned => CompCert.Int.shru n1 n2)
    (fun sg n1 n2 => match sg with | .Signed => CompCert.Int64.shr n1 n2 | .Unsigned => CompCert.Int64.shru n1 n2)
    v1 t1 v2 t2

-- *** Comparisons

inductive classify_cmp_cases : Type where
  | cmp_case_pp                     -- pointer, pointer
  | cmp_case_pi (si : signedness)   -- pointer, int
  | cmp_case_ip (si : signedness)   -- int, pointer
  | cmp_case_pl                     -- pointer, long
  | cmp_case_lp                     -- long, pointer
  | cmp_default                     -- numerical, numerical
  deriving DecidableEq

def classify_cmp (ty1 ty2 : type) : classify_cmp_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer _ _, .Tpointer _ _ => .cmp_case_pp
  | .Tpointer _ _, .Tint _ si _ => .cmp_case_pi si
  | .Tint _ si _, .Tpointer _ _ => .cmp_case_ip si
  | .Tpointer _ _, .Tlong _ _ => .cmp_case_pl
  | .Tlong _ _, .Tpointer _ _ => .cmp_case_lp
  | _, _ => .cmp_default

def cmp_ptr (m : mem) (c : comparison) (v1 v2 : val) : Option val :=
  (if Archi.ptr64
   then Val.cmplu_bool (Memory.valid_pointer m) c v1 v2
   else Val.cmpu_bool (Memory.valid_pointer m) c v1 v2).map Val.of_bool

def sem_cmp (c : comparison)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type)
    (m : mem) : Option val :=
  match classify_cmp t1 t2 with
  | .cmp_case_pp =>
      cmp_ptr m c v1 v2
  | .cmp_case_pi si =>
      match v2 with
      | .Vint n2 =>
          let v2' := Vptrofs (ptrofs_of_int si n2)
          cmp_ptr m c v1 v2'
      | .Vptr _ _ =>
          if Archi.ptr64 then none else cmp_ptr m c v1 v2
      | _ => none
  | .cmp_case_ip si =>
      match v1 with
      | .Vint n1 =>
          let v1' := Vptrofs (ptrofs_of_int si n1)
          cmp_ptr m c v1' v2
      | .Vptr _ _ =>
          if Archi.ptr64 then none else cmp_ptr m c v1 v2
      | _ => none
  | .cmp_case_pl =>
      match v2 with
      | .Vlong n2 =>
          let v2' := Vptrofs (Ptrofs.of_int64 n2)
          cmp_ptr m c v1 v2'
      | .Vptr _ _ =>
          if Archi.ptr64 then cmp_ptr m c v1 v2 else none
      | _ => none
  | .cmp_case_lp =>
      match v1 with
      | .Vlong n1 =>
          let v1' := Vptrofs (Ptrofs.of_int64 n1)
          cmp_ptr m c v1' v2
      | .Vptr _ _ =>
          if Archi.ptr64 then cmp_ptr m c v1 v2 else none
      | _ => none
  | .cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
            some (Val.of_bool (match sg with | .Signed => CompCert.Int.cmp c n1 n2 | .Unsigned => CompCert.Int.cmpu c n1 n2)))
        (fun sg n1 n2 =>
            some (Val.of_bool (match sg with | .Signed => CompCert.Int64.cmp c n1 n2 | .Unsigned => CompCert.Int64.cmpu c n1 n2)))
        (fun n1 n2 =>
            some (Val.of_bool (CompCert.Float64.cmp c n1 n2)))
        (fun n1 n2 =>
            some (Val.of_bool (CompCert.Float32.cmp c n1 n2)))
        v1 t1 v2 t2 m

-- ** Function applications

inductive classify_fun_cases : Type where
  | fun_case_f (targs : List type) (tres : type) (cc : calling_convention)  -- (pointer to) function
  | fun_default
  deriving DecidableEq

def classify_fun (ty : type) : classify_fun_cases :=
  match ty with
  | .Tfunction args res cc => .fun_case_f args res cc
  | .Tpointer (.Tfunction args res cc) _ => .fun_case_f args res cc
  | _ => .fun_default

-- ** Argument of a [switch] statement

inductive classify_switch_cases : Type where
  | switch_case_i
  | switch_case_l
  | switch_default
  deriving DecidableEq

def classify_switch (ty : type) : classify_switch_cases :=
  match ty with
  | .Tint _ _ _ => .switch_case_i
  | .Tlong _ _ => .switch_case_l
  | _ => .switch_default

def sem_switch_arg (v : val) (ty : type) : Option Nat :=
  match classify_switch ty with
  | .switch_case_i =>
      match v with | .Vint n => some (CompCert.Int.unsigned n) | _ => none
  | .switch_case_l =>
      match v with | .Vlong n => some (CompCert.Int64.unsigned n) | _ => none
  | .switch_default =>
      none

-- * Combined semantics of unary and binary operators

def sem_unary_operation
    (op : unary_operation) (v : val) (ty : type) (m : mem) : Option val :=
  match op with
  | .Onotbool => sem_notbool v ty m
  | .Onotint => sem_notint v ty
  | .Oneg => sem_neg v ty
  | .Oabsfloat => sem_absfloat v ty

def sem_binary_operation
    (cenv : composite_env)
    (op : binary_operation)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type)
    (m : mem) : Option val :=
  match op with
  | .Oadd => sem_add cenv v1 t1 v2 t2 m
  | .Osub => sem_sub cenv v1 t1 v2 t2 m
  | .Omul => sem_mul v1 t1 v2 t2 m
  | .Omod => sem_mod v1 t1 v2 t2 m
  | .Odiv => sem_div v1 t1 v2 t2 m
  | .Oand => sem_and v1 t1 v2 t2 m
  | .Oor => sem_or v1 t1 v2 t2 m
  | .Oxor => sem_xor v1 t1 v2 t2 m
  | .Oshl => sem_shl v1 t1 v2 t2
  | .Oshr => sem_shr v1 t1 v2 t2
  | .Oeq => sem_cmp .Ceq v1 t1 v2 t2 m
  | .One => sem_cmp .Cne v1 t1 v2 t2 m
  | .Olt => sem_cmp .Clt v1 t1 v2 t2 m
  | .Ogt => sem_cmp .Cgt v1 t1 v2 t2 m
  | .Ole => sem_cmp .Cle v1 t1 v2 t2 m
  | .Oge => sem_cmp .Cge v1 t1 v2 t2 m

def sem_incrdecr (cenv : composite_env) (id : incr_or_decr) (v : val) (ty : type) (m : mem) : Option val :=
  match id with
  | .Incr => sem_add cenv v ty (.Vint CompCert.Int.one) type_int32s m
  | .Decr => sem_sub cenv v ty (.Vint CompCert.Int.one) type_int32s m

def incrdecr_type (ty : type) : type :=
  match typeconv ty with
  | .Tpointer ty a => .Tpointer ty a
  | .Tint sz sg _ => .Tint sz sg noattr
  | .Tlong sg _ => .Tlong sg noattr
  | .Tfloat sz _ => .Tfloat sz noattr
  | _ => .Tvoid

-- ** Accessing bit fields

def chunk_for_carrier (sz : intsize) : memory_chunk :=
  match sz with
  | .I8 | .IBool => .Mint8unsigned
  | .I16 => .Mint16unsigned
  | .I32 => .Mint32

/-
For bitfield accesses, bits are numbered differently on
little-endian and on big-endian machines: bit 0 is the least
significant bit in little-endian, and the most significant bit in
big-endian.
-/

def bitsize_carrier (sz : intsize) : Int :=
  match sz with
  | .I8 | .IBool => 8
  | .I16 => 16
  | .I32 => 32

def first_bit (sz : intsize) (pos width : Int) : Int :=
  if Archi.big_endian
  then bitsize_carrier sz - pos - width
  else pos

def bitfield_extract (sz : intsize) (sg : signedness) (pos width : Int) (c : CompCert.Int) : CompCert.Int :=
  if sz = .IBool ∨ sg = .Unsigned
  then CompCert.Int.unsigned_bitfield_extract (first_bit sz pos width) width c
  else CompCert.Int.signed_bitfield_extract (first_bit sz pos width) width c

def bitfield_normalize (sz : intsize) (sg : signedness) (width : Int) (n : CompCert.Int) : CompCert.Int :=
  if sz = .IBool ∨ sg = .Unsigned
  then CompCert.Int.zero_ext width.toNat n
  else CompCert.Int.sign_ext width.toNat n

inductive load_bitfield : type → intsize → signedness → Int → Int → mem → val → val → Prop
  | load_bitfield_intro (sz : intsize) (sg1 : signedness) (attr : attr) (sg : signedness)
      (pos width : Int) (m : mem) (addr : val) (c : CompCert.Int)
      (H0 : 0 ≤ pos) (H1 : 0 < width ∧ width ≤ bitsize_intsize sz) (H2 : pos + width ≤ bitsize_carrier sz)
      (H3 : sg1 = (if width < bitsize_intsize sz then .Signed else sg))
      (H4 : Memory.loadv (chunk_for_carrier sz) m addr = some (.Vint c)) :
      load_bitfield (.Tint sz sg1 attr) sz sg pos width m addr
                    (.Vint (bitfield_extract sz sg pos width c))

inductive store_bitfield : type → intsize → signedness → Int → Int → mem → val → val → mem → val → Prop
  | store_bitfield_intro (sz : intsize) (sg1 : signedness) (attr : attr) (sg : signedness)
      (pos width : Int) (m : mem) (addr : val) (c n : CompCert.Int) (m' : mem)
      (H0 : 0 ≤ pos) (H1 : 0 < width ∧ width ≤ bitsize_intsize sz) (H2 : pos + width ≤ bitsize_carrier sz)
      (H3 : sg1 = (if width < bitsize_intsize sz then .Signed else sg))
      (H4 : Memory.loadv (chunk_for_carrier sz) m addr = some (.Vint c))
      (H5 : Memory.storev (chunk_for_carrier sz) m addr
                 (.Vint (CompCert.Int.bitfield_insert (first_bit sz pos width) width c n)) = some m') :
      store_bitfield (.Tint sz sg1 attr) sz sg pos width m addr (.Vint n)
                     m' (.Vint (bitfield_normalize sz sg width n))

-- * Compatibility with extensions and injections

section GENERIC_INJECTION

variable (f : meminj)
variable (m m' : mem)

variable (valid_pointer_inj : ∀ b1 ofs b2 delta,
  f b1 = some (b2, delta) →
  Memory.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
  Memory.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)

variable (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
  f b1 = some (b2, delta) →
  Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
  Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)

variable (weak_valid_pointer_no_overflow : ∀ b1 ofs b2 delta,
  f b1 = some (b2, delta) →
  Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
  0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
  Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)

variable (valid_different_pointers_inj : ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 ≠ b2 →
  Memory.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
  Memory.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' ≠ b2' ∨
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))

theorem val_inject_vtrue : Val.inject f Vtrue Vtrue := by
  unfold Vtrue
  exact Val.inject.inject_int _

theorem val_inject_vfalse : Val.inject f Vfalse Vfalse := by
  unfold Vfalse
  exact Val.inject.inject_int _

theorem val_inject_of_bool (b : Bool) : Val.inject f (Val.of_bool b) (Val.of_bool b) := by
  unfold Val.of_bool
  cases b
  · exact val_inject_vfalse f
  · exact val_inject_vtrue f

theorem val_inject_vptrofs (n : ptrofs) : Val.inject f (Vptrofs n) (Vptrofs n) := by
  unfold Vptrofs
  cases h : Archi.ptr64 <;> simp
  · exact Val.inject.inject_int _
  · exact Val.inject.inject_long _

set_option maxHeartbeats 1000000 in
theorem sem_cast_inj (v1 : val) (ty1 ty : type) (v tv1 : val)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (H : sem_cast v1 ty1 ty m = some v) (Hinj : Val.inject f v1 tv1) :
    ∃ tv, sem_cast tv1 ty1 ty m' = some tv ∧ Val.inject f v tv := by
  cases hc : classify_cast ty1 ty with
  | cast_case_i2bool =>
      simp only [sem_cast, hc] at H ⊢
      cases Hinj with
      | inject_int i => simp_all; rw [← H]; exact Val.inject.inject_int _
      | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
          subst ho
          simp_all
          obtain ⟨-, hwp, hv⟩ := H
          subst hv
          exact ⟨weak_valid_pointer_inj b1 ofs1 b2 delta hf hwp, Val.inject.inject_int _⟩
      | inject_long i => simp_all
      | inject_float ff => simp_all
      | inject_single ff => simp_all
      | val_inject_undef w => simp_all
  | cast_case_l2bool =>
      simp only [sem_cast, hc] at H ⊢
      cases Hinj with
      | inject_long i => simp_all; rw [← H]; exact Val.inject.inject_int _
      | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
          subst ho
          simp_all
          obtain ⟨-, hwp, hv⟩ := H
          subst hv
          exact ⟨weak_valid_pointer_inj b1 ofs1 b2 delta hf hwp, Val.inject.inject_int _⟩
      | inject_int i => simp_all
      | inject_float ff => simp_all
      | inject_single ff => simp_all
      | val_inject_undef w => simp_all
  | cast_case_pointer =>
      simp only [sem_cast, hc] at H ⊢
      cases Hinj with
      | inject_int i =>
          rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at H ⊢
          obtain rfl : v = .Vint i := by simpa using H.symm
          exact Val.inject.inject_int _
      | inject_long i =>
          rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at H ⊢
          obtain rfl : v = .Vlong i := by simpa using H.symm
          exact Val.inject.inject_long _
      | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
          subst ho
          obtain rfl : v = .Vptr b1 ofs1 := by simpa using H.symm
          exact ⟨.Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta)), rfl,
            Val.inject.inject_ptr _ _ _ _ _ hf rfl⟩
      | inject_float ff => simp_all
      | inject_single ff => simp_all
      | val_inject_undef w => simp_all
  | _ =>
      simp only [sem_cast, hc] at H ⊢;
        cases Hinj <;>
        (repeat (first | (split at H) | (obtain ⟨-, H⟩ := H))) <;>
        simp_all <;>
        (try (rw [← H])) <;>
        first
          | exact Val.inject.inject_int _
          | exact Val.inject.inject_long _
          | exact Val.inject.inject_float _
          | exact Val.inject.inject_single _
          | exact Val.inject.val_inject_undef _
          | (constructor <;> first | assumption | rfl)

theorem bool_val_inj (v : val) (ty : type) (b : Bool) (tv : val)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (H : bool_val v ty m = some b) (Hinj : Val.inject f v tv) :
    bool_val tv ty m' = some b := by
  cases hc : classify_bool ty with
  | bool_case_i =>
      cases Hinj with
      | inject_int i =>
          simp only [bool_val, hc] at H ⊢
          simpa using H
      | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
          subst ho
          simp only [bool_val, hc] at H ⊢
          by_cases hp : Archi.ptr64 = true
          · rw [if_pos hp] at H
            simp at H
          · rw [if_neg hp] at H ⊢
            by_cases hwp : Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true
            · rw [if_pos hwp] at H
              have hbeq : b = true := by simpa using H.symm
              subst hbeq
              have hwp' := weak_valid_pointer_inj b1 ofs1 b2 delta hf hwp
              simp [hwp']
            · rw [if_neg hwp] at H
              simp at H
      | inject_long i => simp_all [bool_val]
      | inject_float ff => simp_all [bool_val]
      | inject_single ff => simp_all [bool_val]
      | val_inject_undef w => simp_all [bool_val]
  | bool_case_l =>
      cases Hinj with
      | inject_long i =>
          simp only [bool_val, hc] at H ⊢
          simpa using H
      | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
          subst ho
          simp only [bool_val, hc] at H ⊢
          by_cases hp : Archi.ptr64 = true
          · simp only [hp, Bool.not_true] at H ⊢
            by_cases hwp : Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true
            · rw [if_pos hwp] at H
              have hbeq : b = true := by simpa using H.symm
              subst hbeq
              have hwp' := weak_valid_pointer_inj b1 ofs1 b2 delta hf hwp
              simp [hwp']
            · rw [if_neg hwp] at H
              simp at H
          · have hp' : Archi.ptr64 = false := by
              rcases h : Archi.ptr64 <;> simp_all
            simp only [hp', Bool.not_false, if_true] at H
            simp at H
      | inject_int i => simp_all [bool_val]
      | inject_float ff => simp_all [bool_val]
      | inject_single ff => simp_all [bool_val]
      | val_inject_undef w => simp_all [bool_val]
  | bool_case_f =>
      cases Hinj <;> simp_all [bool_val]
  | bool_case_s =>
      cases Hinj <;> simp_all [bool_val]
  | bool_default =>
      simp only [bool_val, hc] at H
      exact absurd H (by simp)

theorem sem_unary_operation_inj (op : unary_operation) (v1 : val) (ty : type) (v tv1 : val)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (H : sem_unary_operation op v1 ty m = some v) (Hinj : Val.inject f v1 tv1) :
    ∃ tv, sem_unary_operation op tv1 ty m' = some tv ∧ Val.inject f v tv := by
  cases op with
  | Onotbool =>
      unfold sem_unary_operation sem_notbool at H ⊢
      cases hbv : bool_val v1 ty m with
      | none => simp [hbv] at H
      | some bres =>
          simp only [hbv, Option.map_some] at H
          have hbv' := bool_val_inj f m m' v1 ty bres tv1 weak_valid_pointer_inj hbv Hinj
          refine ⟨Val.of_bool (!bres), ?_, ?_⟩
          · simp [hbv']
          · simp only [Option.some.injEq] at H
            rw [← H]
            exact val_inject_of_bool f (!bres)
  | Onotint =>
      unfold sem_unary_operation sem_notint at H ⊢
      cases hc : classify_notint ty <;> simp only [hc] at H ⊢ <;>
        cases Hinj <;> simp_all <;>
        (try (rw [← H])) <;>
        first
          | exact ⟨_, rfl, Val.inject.inject_int _⟩
          | exact ⟨_, rfl, Val.inject.inject_long _⟩
          | exact Val.inject.inject_int _
          | exact Val.inject.inject_long _
  | Oneg =>
      unfold sem_unary_operation sem_neg at H ⊢
      cases hc : classify_neg ty <;> simp only [hc] at H ⊢ <;>
        cases Hinj <;> simp_all <;>
        (try (rw [← H])) <;>
        first
          | exact ⟨_, rfl, Val.inject.inject_int _⟩
          | exact ⟨_, rfl, Val.inject.inject_long _⟩
          | exact ⟨_, rfl, Val.inject.inject_float _⟩
          | exact ⟨_, rfl, Val.inject.inject_single _⟩
          | exact Val.inject.inject_int _
          | exact Val.inject.inject_long _
          | exact Val.inject.inject_float _
          | exact Val.inject.inject_single _
  | Oabsfloat =>
      unfold sem_unary_operation sem_absfloat at H ⊢
      cases hc : classify_neg ty <;> simp only [hc] at H ⊢ <;>
        cases Hinj <;> simp_all <;>
        (try (rw [← H])) <;>
        first
          | exact ⟨_, rfl, Val.inject.inject_float _⟩
          | exact Val.inject.inject_float _

/-- Under a memory injection, an optional value that is not a pointer
    always injects into itself. -/
def optval_self_injects (ov : Option val) : Prop :=
  match ov with
  | some (.Vptr _ _) => False
  | _ => True

set_option maxHeartbeats 1000000 in
theorem sem_binarith_inject
    (sem_int : signedness → CompCert.Int → CompCert.Int → Option val)
    (sem_long : signedness → CompCert.Int64 → CompCert.Int64 → Option val)
    (sem_float : CompCert.Float64 → CompCert.Float64 → Option val)
    (sem_single : CompCert.Float32 → CompCert.Float32 → Option val)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (v v1' v2' : val)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (H : sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m = some v)
    (Hinj1 : Val.inject f v1 v1') (Hinj2 : Val.inject f v2 v2')
    (Hself_int : ∀ sg n1 n2, optval_self_injects (sem_int sg n1 n2))
    (Hself_long : ∀ sg n1 n2, optval_self_injects (sem_long sg n1 n2))
    (Hself_float : ∀ n1 n2, optval_self_injects (sem_float n1 n2))
    (Hself_single : ∀ n1 n2, optval_self_injects (sem_single n1 n2)) :
    ∃ v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m' = some v' ∧
          Val.inject f v v' := by
  have self_inj : ∀ w : val, optval_self_injects (some w) → Val.inject f w w := by
    intro w hw
    cases w with
    | Vundef => exact Val.inject.val_inject_undef _
    | Vint n => exact Val.inject.inject_int _
    | Vlong n => exact Val.inject.inject_long _
    | Vfloat n => exact Val.inject.inject_float _
    | Vsingle n => exact Val.inject.inject_single _
    | Vptr b o => exact absurd hw (by simp [optval_self_injects])
  unfold sem_binarith at H ⊢
  cases hcast1 : sem_cast v1 t1 (binarith_type (classify_binarith t1 t2)) m with
  | none => simp [hcast1] at H
  | some w1 =>
    cases hcast2 : sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m with
    | none => simp [hcast1, hcast2] at H
    | some w2 =>
      simp only [hcast1, hcast2] at H
      obtain ⟨w1', hw1', Hinjw1⟩ :=
        sem_cast_inj f m m' v1 t1 (binarith_type (classify_binarith t1 t2)) w1 v1'
          weak_valid_pointer_inj hcast1 Hinj1
      obtain ⟨w2', hw2', Hinjw2⟩ :=
        sem_cast_inj f m m' v2 t2 (binarith_type (classify_binarith t1 t2)) w2 v2'
          weak_valid_pointer_inj hcast2 Hinj2
      simp only [hw1', hw2']
      -- Package each per-type self-injection as a closed term *before* any
      -- `simp_all`, then hide them from it. `simp_all` would otherwise rewrite the
      -- float quantifiers through FloatLib's subtype representation, after which
      -- they no longer match `sem_float`/`sem_single` applications.
      have hf : ∀ (a b : CompCert.Float64) (w : val), sem_float a b = some w → Val.inject f w w :=
        fun a b w h => self_inj _ (h ▸ Hself_float a b)
      have hs : ∀ (a b : CompCert.Float32) (w : val), sem_single a b = some w → Val.inject f w w :=
        fun a b w h => self_inj _ (h ▸ Hself_single a b)
      have hi : ∀ sg a b (w : val), sem_int sg a b = some w → Val.inject f w w :=
        fun sg a b w h => self_inj _ (h ▸ Hself_int sg a b)
      have hl : ∀ sg a b (w : val), sem_long sg a b = some w → Val.inject f w w :=
        fun sg a b w h => self_inj _ (h ▸ Hself_long sg a b)
      clear Hself_int Hself_long Hself_float Hself_single self_inj
      revert hf hs hi hl
      cases hbc : classify_binarith t1 t2 <;> simp only [hbc] at H ⊢ <;>
        cases Hinjw1 <;> cases Hinjw2 <;> try simp only [] at H ⊢
      all_goals intro hf hs hi hl
      all_goals first
        | exact ⟨v, H, hf _ _ v H⟩
        | exact ⟨v, H, hs _ _ v H⟩
        | exact ⟨v, H, hi _ _ _ v H⟩
        | exact ⟨v, H, hl _ _ _ v H⟩
        | (clear hf hs hi hl; simp_all)

theorem sem_shift_inject
    (sem_int : signedness → CompCert.Int → CompCert.Int → CompCert.Int)
    (sem_long : signedness → CompCert.Int64 → CompCert.Int64 → CompCert.Int64)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (v v1' v2' : val)
    (H : sem_shift sem_int sem_long v1 t1 v2 t2 = some v)
    (Hinj1 : Val.inject f v1 v1') (Hinj2 : Val.inject f v2 v2') :
    ∃ v', sem_shift sem_int sem_long v1' t1 v2' t2 = some v' ∧ Val.inject f v v' := by
  unfold sem_shift at H ⊢
  cases hc : classify_shift t1 t2 <;> simp only [hc] at H ⊢ <;>
    cases Hinj1 <;> cases Hinj2 <;>
    (repeat (first | (split at H) | (obtain ⟨-, H⟩ := H))) <;>
    simp_all <;>
    first
      | exact ⟨_, rfl, Val.inject.inject_int _⟩
      | exact ⟨_, rfl, Val.inject.inject_long _⟩
      | exact Val.inject.inject_int _
      | exact Val.inject.inject_long _

/-- If a pointer is valid via the shift-by-one characterization used internally by
    `Val.weak_valid_ptr` (`valid_ptr b ofs || valid_ptr b (ofs - 1)`, matching real
    CompCert's `Values.v`/`Memory.v` `weak_valid_ptr`/`Mem.weak_valid_pointer`), then it
    is weakly valid in `Memory.weak_valid_pointer`'s (independent, `lo ≤ ofs ≤ hi`) sense.
    This direction holds unconditionally (no well-formedness needed). -/
theorem valid_pointer_or_imp_weak_valid_pointer (m0 : mem) (b : block) (ofs : Int) :
    (Memory.valid_pointer m0 b ofs || Memory.valid_pointer m0 b (ofs - 1)) = true →
    weak_valid_pointer m0 b ofs = true := by
  unfold Memory.valid_pointer weak_valid_pointer
  cases hb : m0.blocks.get? b with
  | none => simp
  | some info => simp only []; intro h; simp_all; omega

/-- Converse of `valid_pointer_or_imp_weak_valid_pointer`, valid only for well-formed
    memories (`Memory.mem_wf`, which guarantees every allocated block is non-empty,
    `lo < hi`). Without well-formedness the converse fails at the one-past-end offset
    of an (illegal) zero-size block. -/
theorem weak_valid_pointer_imp_valid_pointer_or (m0 : mem) (hwf : Memory.mem_wf m0)
    (b : block) (ofs : Int) :
    weak_valid_pointer m0 b ofs = true →
    (Memory.valid_pointer m0 b ofs || Memory.valid_pointer m0 b (ofs - 1)) = true := by
  unfold weak_valid_pointer Memory.valid_pointer
  cases hb : m0.blocks.get? b with
  | none => simp
  | some info =>
    obtain ⟨_, h_bounds, _⟩ := hwf
    have hlt : info.lo < info.hi := h_bounds b info hb
    simp only []; intro h; simp_all; omega

theorem sem_cmp_ptr_inj (c : comparison) (v1 v2 v tv1 tv2 : val)
    (valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (weak_valid_pointer_no_overflow : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)
    (valid_different_pointers_inj : ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
      b1 ≠ b2 →
      Memory.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Memory.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
      Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))
    (hwf' : Memory.mem_wf m')
    (H : cmp_ptr m c v1 v2 = some v)
    (Hinj1 : Val.inject f v1 tv1) (Hinj2 : Val.inject f v2 tv2) :
    ∃ tv, cmp_ptr m' c tv1 tv2 = some tv ∧ Val.inject f v tv := by
  have weak_valid_pointer_inj' : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      (Memory.valid_pointer m b1 ofs.unsigned || Memory.valid_pointer m b1 (ofs.unsigned - 1)) = true →
      (Memory.valid_pointer m' b2 (Ptrofs.add ofs (Ptrofs.repr delta)).unsigned ||
       Memory.valid_pointer m' b2 ((Ptrofs.add ofs (Ptrofs.repr delta)).unsigned - 1)) = true := by
    intro b1 ofs b2 delta hf hor
    exact weak_valid_pointer_imp_valid_pointer_or m' hwf' b2 _
      (weak_valid_pointer_inj b1 ofs b2 delta hf (valid_pointer_or_imp_weak_valid_pointer m b1 ofs.unsigned hor))
  have weak_valid_pointer_no_overflow' : ∀ b1 (ofs : Ptrofs) b2 delta,
      f b1 = some (b2, delta) →
      (Memory.valid_pointer m b1 ofs.unsigned || Memory.valid_pointer m b1 (ofs.unsigned - 1)) = true →
      0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned := by
    intro b1 ofs b2 delta hf hor
    exact weak_valid_pointer_no_overflow b1 ofs b2 delta hf
      (valid_pointer_or_imp_weak_valid_pointer m b1 ofs.unsigned hor)
  unfold cmp_ptr at H ⊢
  by_cases hp : Archi.ptr64
  · simp only [hp, if_true] at H ⊢
    cases hcl : Val.cmplu_bool (Memory.valid_pointer m) c v1 v2 with
    | none => simp [hcl] at H
    | some bres =>
      have hcl' : Val.cmplu_bool (Memory.valid_pointer m') c tv1 tv2 = some bres :=
        Val.cmplu_bool_inject f (Memory.valid_pointer m) (Memory.valid_pointer m')
          valid_pointer_inj weak_valid_pointer_inj' weak_valid_pointer_no_overflow'
          valid_different_pointers_inj c v1 v2 tv1 tv2 bres Hinj1 Hinj2 hcl
      refine ⟨Val.of_bool bres, ?_, ?_⟩
      · simp [hcl']
      · simp only [hcl, Option.map_some] at H
        have hv := Option.some.inj H
        rw [← hv]; exact val_inject_of_bool f bres
  · simp only [hp] at H ⊢
    cases hcl : Val.cmpu_bool (Memory.valid_pointer m) c v1 v2 with
    | none => simp [hcl] at H
    | some bres =>
      have hcl' : Val.cmpu_bool (Memory.valid_pointer m') c tv1 tv2 = some bres :=
        Val.cmpu_bool_inject f (Memory.valid_pointer m) (Memory.valid_pointer m')
          valid_pointer_inj weak_valid_pointer_inj' weak_valid_pointer_no_overflow'
          valid_different_pointers_inj c v1 v2 tv1 tv2 bres Hinj1 Hinj2 hcl
      refine ⟨Val.of_bool bres, ?_, ?_⟩
      · simp [hcl']
      · simp only [hcl] at H
        have hv := Option.some.inj H
        rw [← hv]; exact val_inject_of_bool f bres

theorem sem_cmp_inj (cmp : comparison) (v1 tv1 : val) (ty1 : type) (v2 tv2 : val) (ty2 : type) (v : val)
    (valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (weak_valid_pointer_no_overflow : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)
    (valid_different_pointers_inj : ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
      b1 ≠ b2 →
      Memory.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Memory.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
      Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))
    (hwf' : Memory.mem_wf m')
    (H : sem_cmp cmp v1 ty1 v2 ty2 m = some v)
    (Hinj1 : Val.inject f v1 tv1) (Hinj2 : Val.inject f v2 tv2) :
    ∃ tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv := by
  unfold sem_cmp at H ⊢
  cases hc : classify_cmp ty1 ty2 with
  | cmp_case_pp =>
      rw [hc] at H
      exact sem_cmp_ptr_inj f m m' cmp v1 v2 v tv1 tv2 valid_pointer_inj weak_valid_pointer_inj
        weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2
  | cmp_case_pi si =>
      rw [hc] at H
      cases Hinj2 with
      | inject_int n2 =>
          simp only at H ⊢
          exact sem_cmp_ptr_inj f m m' cmp v1 (Vptrofs (ptrofs_of_int si n2)) v tv1
            (Vptrofs (ptrofs_of_int si n2)) valid_pointer_inj weak_valid_pointer_inj
            weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 (val_inject_vptrofs f _)
      | inject_ptr b2 ofs2 b2' ofs2' delta hf ho =>
          simp only at H ⊢
          by_cases hp : Archi.ptr64
          · simp [hp] at H
          · simp only [hp, Bool.false_eq_true, if_false] at H ⊢
            exact sem_cmp_ptr_inj f m m' cmp v1 (.Vptr b2 ofs2) v tv1 (.Vptr b2' ofs2')
              valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow
              valid_different_pointers_inj hwf' H Hinj1 (Val.inject.inject_ptr _ _ _ _ _ hf ho)
      | val_inject_undef => simp at H
      | _ => simp at H
  | cmp_case_ip si =>
      rw [hc] at H
      cases Hinj1 with
      | inject_int n1 =>
          simp only at H ⊢
          exact sem_cmp_ptr_inj f m m' cmp (Vptrofs (ptrofs_of_int si n1)) v2 v
            (Vptrofs (ptrofs_of_int si n1)) tv2 valid_pointer_inj weak_valid_pointer_inj
            weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H (val_inject_vptrofs f _) Hinj2
      | inject_ptr b1 ofs1 b1' ofs1' delta hf ho =>
          simp only at H ⊢
          by_cases hp : Archi.ptr64
          · simp [hp] at H
          · simp only [hp, Bool.false_eq_true, if_false] at H ⊢
            exact sem_cmp_ptr_inj f m m' cmp (.Vptr b1 ofs1) v2 v (.Vptr b1' ofs1') tv2
              valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow
              valid_different_pointers_inj hwf' H (Val.inject.inject_ptr _ _ _ _ _ hf ho) Hinj2
      | val_inject_undef => simp at H
      | _ => simp at H
  | cmp_case_pl =>
      rw [hc] at H
      cases Hinj2 with
      | inject_long n2 =>
          simp only at H ⊢
          exact sem_cmp_ptr_inj f m m' cmp v1 (Vptrofs (Ptrofs.of_int64 n2)) v tv1
            (Vptrofs (Ptrofs.of_int64 n2)) valid_pointer_inj weak_valid_pointer_inj
            weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 (val_inject_vptrofs f _)
      | inject_ptr b2 ofs2 b2' ofs2' delta hf ho =>
          simp only at H ⊢
          by_cases hp : Archi.ptr64
          · simp only [hp, if_true] at H ⊢
            exact sem_cmp_ptr_inj f m m' cmp v1 (.Vptr b2 ofs2) v tv1 (.Vptr b2' ofs2')
              valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow
              valid_different_pointers_inj hwf' H Hinj1 (Val.inject.inject_ptr _ _ _ _ _ hf ho)
          · simp [hp] at H
      | val_inject_undef => simp at H
      | _ => simp at H
  | cmp_case_lp =>
      rw [hc] at H
      cases Hinj1 with
      | inject_long n1 =>
          simp only at H ⊢
          exact sem_cmp_ptr_inj f m m' cmp (Vptrofs (Ptrofs.of_int64 n1)) v2 v
            (Vptrofs (Ptrofs.of_int64 n1)) tv2 valid_pointer_inj weak_valid_pointer_inj
            weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H (val_inject_vptrofs f _) Hinj2
      | inject_ptr b1 ofs1 b1' ofs1' delta hf ho =>
          simp only at H ⊢
          by_cases hp : Archi.ptr64
          · simp only [hp, if_true] at H ⊢
            exact sem_cmp_ptr_inj f m m' cmp (.Vptr b1 ofs1) v2 v (.Vptr b1' ofs1') tv2
              valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow
              valid_different_pointers_inj hwf' H (Val.inject.inject_ptr _ _ _ _ _ hf ho) Hinj2
          · simp [hp] at H
      | val_inject_undef => simp at H
      | _ => simp at H
  | cmp_default =>
      rw [hc] at H
      refine sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        ?_ ?_ ?_ ?_
      · intro sg n1 n2; cases sg <;> simp only [Val.of_bool] <;> split <;> trivial
      · intro sg n1 n2; cases sg <;> simp only [Val.of_bool] <;> split <;> trivial
      · intro n1 n2; simp only [Val.of_bool]; split <;> trivial
      · intro n1 n2; simp only [Val.of_bool]; split <;> trivial

theorem sem_binary_operation_inj (cenv : composite_env) (op : binary_operation)
    (v1 : val) (ty1 : type) (v2 : val) (ty2 : type) (v tv1 tv2 : val)
    (valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (weak_valid_pointer_inj : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Memory.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true)
    (weak_valid_pointer_no_overflow : ∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Memory.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned)
    (valid_different_pointers_inj : ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
      b1 ≠ b2 →
      Memory.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Memory.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
      Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)))
    (hwf' : Memory.mem_wf m')
    (H : sem_binary_operation cenv op v1 ty1 v2 ty2 m = some v)
    (Hinj1 : Val.inject f v1 tv1) (Hinj2 : Val.inject f v2 tv2) :
    ∃ tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv := by
  have addA : ∀ (ty : type) (si : signedness) (va ta vb tb : val),
      Val.inject f va ta → Val.inject f vb tb →
      sem_add_ptr_int cenv ty si va vb = some v →
      ∃ tv, sem_add_ptr_int cenv ty si ta tb = some tv ∧ Val.inject f v tv := by
    intro ty si va ta vb tb Ha Hb Hadd
    cases Hb with
    | inject_int n2 =>
        cases Ha with
        | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
            subst ho
            simp only [sem_add_ptr_int] at Hadd ⊢
            have hv := Option.some.inj Hadd; subst hv
            refine ⟨.Vptr b2 (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr delta))
              (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) (ptrofs_of_int si n2))), rfl, ?_⟩
            refine Val.inject.inject_ptr _ _ _ _ _ hf ?_
            rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta)]
        | inject_int i =>
            simp only [sem_add_ptr_int] at Hadd ⊢
            rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at Hadd ⊢;
              (subst Hadd; exact Val.inject.inject_int _)
        | inject_long i =>
            simp only [sem_add_ptr_int] at Hadd ⊢
            rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at Hadd ⊢;
              (subst Hadd; exact Val.inject.inject_long _)
        | inject_float _ => simp [sem_add_ptr_int] at Hadd
        | inject_single _ => simp [sem_add_ptr_int] at Hadd
        | val_inject_undef w => simp [sem_add_ptr_int] at Hadd
    | inject_long _ => simp [sem_add_ptr_int] at Hadd
    | inject_float _ => simp [sem_add_ptr_int] at Hadd
    | inject_single _ => simp [sem_add_ptr_int] at Hadd
    | inject_ptr _ _ _ _ _ _ _ => simp [sem_add_ptr_int] at Hadd
    | val_inject_undef w => simp [sem_add_ptr_int] at Hadd
  have addB : ∀ (ty : type) (va ta vb tb : val),
      Val.inject f va ta → Val.inject f vb tb →
      sem_add_ptr_long cenv ty va vb = some v →
      ∃ tv, sem_add_ptr_long cenv ty ta tb = some tv ∧ Val.inject f v tv := by
    intro ty va ta vb tb Ha Hb Hadd
    cases Hb with
    | inject_long n2 =>
        cases Ha with
        | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
            subst ho
            simp only [sem_add_ptr_long] at Hadd ⊢
            have hv := Option.some.inj Hadd; subst hv
            refine ⟨.Vptr b2 (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr delta))
              (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) (Ptrofs.of_int64 n2))), rfl, ?_⟩
            refine Val.inject.inject_ptr _ _ _ _ _ hf ?_
            rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr delta)]
        | inject_int i =>
            simp only [sem_add_ptr_long] at Hadd ⊢
            rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at Hadd ⊢;
                    (subst Hadd; exact Val.inject.inject_int _)
        | inject_long i =>
            simp only [sem_add_ptr_long] at Hadd ⊢
            rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at Hadd ⊢;
                    (subst Hadd; exact Val.inject.inject_long _)
        | inject_float _ => simp [sem_add_ptr_long] at Hadd
        | inject_single _ => simp [sem_add_ptr_long] at Hadd
        | val_inject_undef w => simp [sem_add_ptr_long] at Hadd
    | inject_int _ => simp [sem_add_ptr_long] at Hadd
    | inject_float _ => simp [sem_add_ptr_long] at Hadd
    | inject_single _ => simp [sem_add_ptr_long] at Hadd
    | inject_ptr _ _ _ _ _ _ _ => simp [sem_add_ptr_long] at Hadd
    | val_inject_undef w => simp [sem_add_ptr_long] at Hadd
  cases op with
  | Oadd =>
      simp only [sem_binary_operation, sem_add] at H ⊢
      cases hc : classify_add ty1 ty2 with
      | add_case_pi ty si =>
          rw [hc] at H; exact addA ty si v1 tv1 v2 tv2 Hinj1 Hinj2 H
      | add_case_pl ty =>
          rw [hc] at H; exact addB ty v1 tv1 v2 tv2 Hinj1 Hinj2 H
      | add_case_ip si ty =>
          rw [hc] at H; exact addA ty si v2 tv2 v1 tv1 Hinj2 Hinj1 H
      | add_case_lp ty =>
          rw [hc] at H; exact addB ty v2 tv2 v1 tv1 Hinj2 Hinj1 H
      | add_default =>
          rw [hc] at H
          exact sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
            (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  | Osub =>
      simp only [sem_binary_operation, sem_sub] at H ⊢
      cases hc : classify_sub ty1 ty2 with
      | sub_case_pi ty si =>
          rw [hc] at H
          cases Hinj1 with
          | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
              subst ho
              cases Hinj2 with
              | inject_int n2 =>
                  simp only at H ⊢
                  have hv := Option.some.inj H; subst hv
                  refine ⟨.Vptr b2 (Ptrofs.sub (Ptrofs.add ofs1 (Ptrofs.repr delta))
                    (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) (ptrofs_of_int si n2))), rfl, ?_⟩
                  refine Val.inject.inject_ptr _ _ _ _ _ hf ?_
                  rw [Ptrofs.sub_add_l]
               | inject_long _ => simp at H
               | inject_float _ => simp at H
               | inject_single _ => simp at H
               | inject_ptr _ _ _ _ _ _ _ => simp at H
               | val_inject_undef w => simp at H
           | inject_int i =>
               cases Hinj2 with
               | inject_int n2 =>
                   simp only at H ⊢
                   rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at H ⊢;
                     (subst H; exact Val.inject.inject_int _)
               | _ => simp at H
           | inject_long i =>
               cases Hinj2 with
               | inject_int n2 =>
                   simp only at H ⊢
                   rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at H ⊢;
                     (subst H; exact Val.inject.inject_long _)
               | _ => simp at H
           | inject_float _ => simp at H
           | inject_single _ => simp at H
          | val_inject_undef w => simp at H
      | sub_case_pl ty =>
          rw [hc] at H
          cases Hinj1 with
          | inject_ptr b1 ofs1 b2 ofs2 delta hf ho =>
              subst ho
              cases Hinj2 with
              | inject_long n2 =>
                  simp only at H ⊢
                  have hv := Option.some.inj H; subst hv
                  refine ⟨.Vptr b2 (Ptrofs.sub (Ptrofs.add ofs1 (Ptrofs.repr delta))
                    (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) (Ptrofs.of_int64 n2))), rfl, ?_⟩
                  refine Val.inject.inject_ptr _ _ _ _ _ hf ?_
                  rw [Ptrofs.sub_add_l]
              | inject_int _ => simp at H
              | inject_float _ => simp at H
              | inject_single _ => simp at H
              | inject_ptr _ _ _ _ _ _ _ => simp at H
              | val_inject_undef w => simp at H
          | inject_int i =>
              cases Hinj2 with
              | inject_long n2 =>
                  simp only at H ⊢
                  rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at H ⊢;
                    (subst H; exact Val.inject.inject_int _)
              | _ => simp at H
          | inject_long i =>
              cases Hinj2 with
              | inject_long n2 =>
                  simp only at H ⊢
                  rcases hp : Archi.ptr64 with _ | _ <;> simp [hp] at H ⊢;
                    (subst H; exact Val.inject.inject_long _)
              | _ => simp at H
          | inject_float _ => simp at H
          | inject_single _ => simp at H
          | val_inject_undef w => simp at H
      | sub_case_pp ty =>
          rw [hc] at H
          cases Hinj1 with
          | inject_ptr b1 ofs1 b2 ofs2 delta1 hf1 ho1 =>
              subst ho1
              cases Hinj2 with
              | inject_ptr b1' ofs1' b2' ofs2' delta2 hf2 ho2 =>
                  subst ho2
                  simp only at H ⊢
                  by_cases hbeq : b1 == b1'
                  · have hbeq' : b1 = b1' := by simpa using hbeq
                    subst hbeq'
                    rw [hf1] at hf2
                    have hpair : (b2, delta1) = (b2', delta2) := Option.some.inj hf2
                    have hb' : b2 = b2' := congrArg Prod.fst hpair
                    have hd' : delta1 = delta2 := congrArg Prod.snd hpair
                    subst hb'; subst hd'
                    simp only [hbeq, beq_self_eq_true, if_true] at H ⊢
                    rw [Ptrofs.sub_add_cancel]
                    by_cases hcond : (0 < sizeof cenv ty && sizeof cenv ty ≤ Ptrofs.max_signed)
                    · rw [if_pos hcond] at H
                      rw [if_pos hcond]
                      have hv := Option.some.inj H
                      subst hv
                      exact ⟨_, rfl, val_inject_vptrofs f _⟩
                    · rw [if_neg hcond] at H
                      exact absurd H (by simp)
                  · have hbeq_false : (b1 == b1') = false := by
                      cases h : (b1 == b1') <;> simp_all
                    simp only [hbeq_false] at H
                    exact absurd H (by simp)
              | inject_int _ => simp at H
              | inject_long _ => simp at H
              | inject_float _ => simp at H
              | inject_single _ => simp at H
              | val_inject_undef w => simp at H
          | inject_int _ => cases Hinj2 <;> simp at H
          | inject_long _ => cases Hinj2 <;> simp at H
          | inject_float _ => cases Hinj2 <;> simp at H
          | inject_single _ => cases Hinj2 <;> simp at H
          | val_inject_undef w => cases Hinj2 <;> simp at H
      | sub_default =>
          rw [hc] at H
          exact sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
            (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  | Omul =>
      exact sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  | Odiv =>
      refine sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        ?_ ?_ (fun _ _ => trivial) (fun _ _ => trivial)
      · intro sg n1 n2; cases sg <;> (dsimp only [optval_self_injects]; split <;> first | trivial | (next heq => split at heq <;> simp at heq))
      · intro sg n1 n2; cases sg <;> (dsimp only [optval_self_injects]; split <;> first | trivial | (next heq => split at heq <;> simp at heq))
  | Omod =>
      refine sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        ?_ ?_ (fun _ _ => trivial) (fun _ _ => trivial)
      · intro sg n1 n2; cases sg <;> (dsimp only [optval_self_injects]; split <;> first | trivial | (next heq => split at heq <;> simp at heq))
      · intro sg n1 n2; cases sg <;> (dsimp only [optval_self_injects]; split <;> first | trivial | (next heq => split at heq <;> simp at heq))
  | Oand =>
      exact sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  | Oor =>
      exact sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  | Oxor =>
      exact sem_binarith_inject f m m' _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 weak_valid_pointer_inj H Hinj1 Hinj2
        (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  | Oshl =>
      simp only [sem_binary_operation, sem_shl] at H ⊢
      exact sem_shift_inject f _ _ v1 ty1 v2 ty2 v tv1 tv2 H Hinj1 Hinj2
  | Oshr =>
      simp only [sem_binary_operation, sem_shr] at H ⊢
      exact sem_shift_inject f _ _ v1 ty1 v2 ty2 v tv1 tv2 H Hinj1 Hinj2
  | Oeq =>
      simp only [sem_binary_operation] at H ⊢
      exact sem_cmp_inj f m m' _ v1 tv1 ty1 v2 tv2 ty2 v
        valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2
  | One =>
      simp only [sem_binary_operation] at H ⊢
      exact sem_cmp_inj f m m' _ v1 tv1 ty1 v2 tv2 ty2 v
        valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2
  | Olt =>
      simp only [sem_binary_operation] at H ⊢
      exact sem_cmp_inj f m m' _ v1 tv1 ty1 v2 tv2 ty2 v
        valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2
  | Ogt =>
      simp only [sem_binary_operation] at H ⊢
      exact sem_cmp_inj f m m' _ v1 tv1 ty1 v2 tv2 ty2 v
        valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2
  | Ole =>
      simp only [sem_binary_operation] at H ⊢
      exact sem_cmp_inj f m m' _ v1 tv1 ty1 v2 tv2 ty2 v
        valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2
  | Oge =>
      simp only [sem_binary_operation] at H ⊢
      exact sem_cmp_inj f m m' _ v1 tv1 ty1 v2 tv2 ty2 v
        valid_pointer_inj weak_valid_pointer_inj weak_valid_pointer_no_overflow valid_different_pointers_inj hwf' H Hinj1 Hinj2


end GENERIC_INJECTION

/-
NOTE: The four Coq lemmas that close this section by deriving the above
hypotheses from a full `Mem.inject f m tm` relation (`sem_cast_inject`,
`sem_unary_operation_inject`, `sem_binary_operation_inject`, `bool_val_inject`)
are NOT ported: this codebase's `Memory.lean` does not yet define `Mem.inject`
(the full CompCert memory-injection relation, with its permission/content
conditions). Porting them is blocked on porting that relation first, and is
tracked as separate follow-up work rather than faked with a placeholder
definition.
-/

/-
* Some properties of operator semantics

This section collects some common-sense properties about the type
classification and semantic functions above.  Some properties are used
in the CompCert semantics preservation proofs.  Others are not, but increase
confidence in the specification and its relation with the ISO C99 standard.
-/

-- Relation between Boolean value and casting to [_Bool] type.

theorem cast_bool_bool_val (v : val) (t : type) (m : mem) :
    sem_cast v t (.Tint .IBool .Signed noattr) m =
    (match bool_val v t m with | none => none | some b => some (Val.of_bool b)) := by
  unfold sem_cast bool_val classify_bool
  cases t with
  | Tvoid => simp [classify_cast, typeconv, remove_attributes, change_attributes]
  | Tstruct id a => simp [classify_cast, typeconv, remove_attributes, change_attributes]
  | Tunion id a => simp [classify_cast, typeconv, remove_attributes, change_attributes]
  | Tint sz si a =>
      cases sz <;> cases si <;>
        simp only [classify_cast, typeconv, remove_attributes, change_attributes] <;>
        (cases v with
          | Vundef => rfl
          | Vint n =>
              cases h : CompCert.Int.eq n CompCert.Int.zero <;>
                simp [h, Val.of_bool, Vtrue, Vfalse]
          | Vlong n => rfl
          | Vfloat f => rfl
          | Vsingle f => rfl
          | Vptr b ofs =>
              cases h : Archi.ptr64 <;> simp; split <;>
                simp [Val.of_bool, Vtrue, Vone])
  | Tlong si a =>
      simp only [classify_cast, typeconv, remove_attributes, change_attributes]
      cases v with
      | Vundef => rfl
      | Vint n => rfl
      | Vlong n =>
          cases h : CompCert.Int64.eq n CompCert.Int64.zero <;>
            simp [h, Val.of_bool, Vtrue, Vfalse]
      | Vfloat f => rfl
      | Vsingle f => rfl
      | Vptr b ofs =>
          cases h : Archi.ptr64 <;> simp; split <;>
            simp [Val.of_bool, Vtrue, Vone]
  | Tfloat f a =>
      cases f <;>
        simp only [classify_cast, typeconv, remove_attributes, change_attributes] <;>
        (cases v with
          | Vundef => rfl
          | Vint n => rfl
          | Vlong n => rfl
          | Vfloat g =>
              first
                | rfl
                | (cases h : CompCert.Float64.cmp .Ceq g CompCert.Float64.zero <;>
                    simp [h, Val.of_bool, Vtrue, Vfalse])
          | Vsingle g =>
              first
                | rfl
                | (cases h : CompCert.Float32.cmp .Ceq g CompCert.Float32.zero <;>
                    simp [h, Val.of_bool, Vtrue, Vfalse])
          | Vptr b ofs => rfl)
  | Tpointer t' a =>
      cases h : Archi.ptr64 <;>
        simp [h, classify_cast, typeconv, remove_attributes, change_attributes] <;>
        (cases v with
          | Vundef => rfl
          | Vint n =>
              first
                | rfl
                | (cases h2 : CompCert.Int.eq n CompCert.Int.zero <;>
                    simp [h2, Val.of_bool, Vtrue, Vfalse])
          | Vlong n =>
              first
                | rfl
                | (cases h2 : CompCert.Int64.eq n CompCert.Int64.zero <;>
                    simp [h2, Val.of_bool, Vtrue, Vfalse])
          | Vfloat g => rfl
          | Vsingle g => rfl
          | Vptr b ofs => simp only []; split <;> simp [Val.of_bool, Vtrue, Vone])
  | Tarray t' sz a =>
      cases h : Archi.ptr64 <;>
        simp [h, classify_cast, typeconv] <;>
        (cases v with
          | Vundef => rfl
          | Vint n =>
              first
                | rfl
                | (cases h2 : CompCert.Int.eq n CompCert.Int.zero <;>
                    simp [h2, Val.of_bool, Vtrue, Vfalse])
          | Vlong n =>
              first
                | rfl
                | (cases h2 : CompCert.Int64.eq n CompCert.Int64.zero <;>
                    simp [h2, Val.of_bool, Vtrue, Vfalse])
          | Vfloat g => rfl
          | Vsingle g => rfl
          | Vptr b ofs => simp only []; split <;> simp [Val.of_bool, Vtrue, Vone])
  | Tfunction ps tr cc =>
      cases h : Archi.ptr64 <;>
        simp [h, classify_cast, typeconv] <;>
        (cases v with
          | Vundef => rfl
          | Vint n =>
              first
                | rfl
                | (cases h2 : CompCert.Int.eq n CompCert.Int.zero <;>
                    simp [h2, Val.of_bool, Vtrue, Vfalse])
          | Vlong n =>
              first
                | rfl
                | (cases h2 : CompCert.Int64.eq n CompCert.Int64.zero <;>
                    simp [h2, Val.of_bool, Vtrue, Vfalse])
          | Vfloat g => rfl
          | Vsingle g => rfl
          | Vptr b ofs => simp only []; split <;> simp [Val.of_bool, Vtrue, Vone])

-- Relation between Boolean value and Boolean negation.

theorem notbool_bool_val (v : val) (t : type) (m : mem) :
    sem_notbool v t m =
    (match bool_val v t m with | none => none | some b => some (Val.of_bool (!b))) := by
  unfold sem_notbool
  cases bool_val v t m <;> rfl

-- Properties of values obtained by casting to a given type.

inductive val_casted : val → type → Prop
  | val_casted_int (sz : intsize) (si : signedness) (attr : attr) (n : CompCert.Int)
      (H : cast_int_int sz si n = n) :
      val_casted (.Vint n) (.Tint sz si attr)
  | val_casted_float (attr : attr) (n : CompCert.Float64) :
      val_casted (.Vfloat n) (.Tfloat .F64 attr)
  | val_casted_single (attr : attr) (n : CompCert.Float32) :
      val_casted (.Vsingle n) (.Tfloat .F32 attr)
  | val_casted_long (si : signedness) (attr : attr) (n : CompCert.Int64) :
      val_casted (.Vlong n) (.Tlong si attr)
  | val_casted_ptr_ptr (b : block) (ofs : ptrofs) (ty : type) (attr : attr) :
      val_casted (.Vptr b ofs) (.Tpointer ty attr)
  | val_casted_int_ptr (n : CompCert.Int) (ty : type) (attr : attr)
      (H : Archi.ptr64 = false) :
      val_casted (.Vint n) (.Tpointer ty attr)
  | val_casted_ptr_int (b : block) (ofs : ptrofs) (si : signedness) (attr : attr)
      (H : Archi.ptr64 = false) :
      val_casted (.Vptr b ofs) (.Tint .I32 si attr)
  | val_casted_long_ptr (n : CompCert.Int64) (ty : type) (attr : attr)
      (H : Archi.ptr64 = true) :
      val_casted (.Vlong n) (.Tpointer ty attr)
  | val_casted_ptr_long (b : block) (ofs : ptrofs) (si : signedness) (attr : attr)
      (H : Archi.ptr64 = true) :
      val_casted (.Vptr b ofs) (.Tlong si attr)
  | val_casted_struct (id : ident) (attr : attr) (b : block) (ofs : ptrofs) :
      val_casted (.Vptr b ofs) (.Tstruct id attr)
  | val_casted_union (id : ident) (attr : attr) (b : block) (ofs : ptrofs) :
      val_casted (.Vptr b ofs) (.Tunion id attr)
  | val_casted_void (v : val) :
      val_casted v .Tvoid

omit [Archi] in
theorem cast_int_int_idem (sz : intsize) (sg : signedness) (i : CompCert.Int) :
    cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i := by
  cases sz with
  | I8 =>
      cases sg with
      | Signed => unfold cast_int_int; exact CompCert.Int.sign_ext_idem 8 i
      | Unsigned => unfold cast_int_int; exact CompCert.Int.zero_ext_idem 8 i
  | I16 =>
      cases sg with
      | Signed => unfold cast_int_int; exact CompCert.Int.sign_ext_idem 16 i
      | Unsigned => unfold cast_int_int; exact CompCert.Int.zero_ext_idem 16 i
  | I32 => cases sg <;> rfl
  | IBool =>
      cases sg <;>
        (unfold cast_int_int
         cases h : CompCert.Int.eq i CompCert.Int.zero <;> simp <;> decide)

set_option maxHeartbeats 800000 in
theorem cast_val_is_casted (v : val) (ty ty' : type) (v' : val) (m : mem)
    (H : sem_cast v ty ty' m = some v') : val_casted v' ty' := by
  cases ty' with
  | Tvoid =>
      simp only [sem_cast, classify_cast, Option.some.injEq] at H
      subst H
      exact val_casted.val_casted_void _
  | Tarray _ _ _ =>
      cases ty <;> simp [sem_cast, classify_cast] at H
  | Tfunction _ _ _ =>
      cases ty <;> simp [sem_cast, classify_cast] at H
  | Tstruct id2 attr =>
      cases ty <;> cases v <;>
        simp only [sem_cast, classify_cast, reduceCtorEq] at H
      case Tstruct.Vptr id1 _ b ofs =>
        split at H
        · rename_i heq; subst heq
          simp only [Option.some.injEq] at H; subst H
          exact val_casted.val_casted_struct _ _ _ _
        · simp only [reduceCtorEq] at H
  | Tunion id2 attr =>
      cases ty <;> cases v <;>
        simp only [sem_cast, classify_cast, reduceCtorEq] at H
      case Tunion.Vptr id1 _ b ofs =>
        split at H
        · rename_i heq; subst heq
          simp only [Option.some.injEq] at H; subst H
          exact val_casted.val_casted_union _ _ _ _
        · simp only [reduceCtorEq] at H
  | Tfloat fsz attr =>
      cases fsz <;> cases ty <;>
        (try (rename_i fsz1 _; cases fsz1)) <;>
        cases v <;>
        simp only [sem_cast, classify_cast, Option.some.injEq, reduceCtorEq] at H <;>
        subst H <;>
        first
          | exact val_casted.val_casted_float _ _
          | exact val_casted.val_casted_single _ _
  | Tlong si2 attr =>
      rcases hp : Archi.ptr64 with _ | _ <;>
      cases ty <;>
        (try (rename_i fsz1 _; cases fsz1)) <;>
        cases v <;>
        simp only [sem_cast, classify_cast, hp, Option.some.injEq, reduceCtorEq,
          Bool.false_eq_true, if_true, if_false] at H <;>
        (try (split at H <;>
          simp only [Option.some.injEq, reduceCtorEq] at H)) <;>
        (try subst H) <;>
        first
          | exact val_casted.val_casted_long _ _ _
          | exact val_casted.val_casted_ptr_long _ _ _ _ hp
  | Tpointer t2 attr =>
      rcases hp : Archi.ptr64 with _ | _ <;>
      cases ty <;>
        cases v <;>
        simp only [sem_cast, classify_cast, hp, Option.some.injEq, reduceCtorEq,
          Bool.false_eq_true, if_true, if_false] at H <;>
        (try subst H) <;>
        first
          | exact val_casted.val_casted_ptr_ptr _ _ _ _
          | exact val_casted.val_casted_int_ptr _ _ _ hp
          | exact val_casted.val_casted_long_ptr _ _ _ hp
  | Tint sz2 si2 attr =>
      rcases hp : Archi.ptr64 with _ | _ <;>
      cases ty <;>
        (try (rename_i fsz1 _; cases fsz1)) <;>
        cases sz2 <;>
        cases v <;>
        simp only [sem_cast, classify_cast, hp, Vone, Bool.not_false, Bool.not_true,
          Option.some.injEq, reduceCtorEq,
          Bool.false_eq_true, if_true, if_false] at H <;>
        (try (split at H)) <;>
        (try (simp only [Option.some.injEq, reduceCtorEq] at H)) <;>
        (try subst_vars) <;>
        first
          | exact val_casted.val_casted_ptr_int _ _ _ _ hp
          | refine val_casted.val_casted_int _ _ _ _ ?_
      all_goals
        first
          | exact cast_int_int_idem _ _ _
          | rfl

-- As a consequence, casting twice is equivalent to casting once.

theorem cast_val_casted (v : val) (ty : type) (m : mem) (H : val_casted v ty) :
    sem_cast v ty ty m = some v := by
  cases H with
  | val_casted_int sz si attr n H =>
      unfold sem_cast classify_cast
      cases sz with
      | I8 => simpa [cast_int_int] using H
      | I16 => simpa [cast_int_int] using H
      | IBool => simpa [cast_int_int] using H
      | I32 =>
          rcases hp : Archi.ptr64 with _ | _ <;> simp [cast_int_int]
  | val_casted_float attr n => rfl
  | val_casted_single attr n => rfl
  | val_casted_long si attr n =>
      unfold sem_cast classify_cast
      rcases hp : Archi.ptr64 with _ | _ <;> simp
  | val_casted_ptr_ptr b ofs ty attr => rfl
  | val_casted_int_ptr n ty attr hp =>
      unfold sem_cast classify_cast
      simp [hp]
  | val_casted_ptr_int b ofs si attr hp =>
      unfold sem_cast classify_cast
      simp [hp]
  | val_casted_long_ptr n ty attr hp =>
      unfold sem_cast classify_cast
      simp [hp]
  | val_casted_ptr_long b ofs si attr hp =>
      unfold sem_cast classify_cast
      simp [hp]
  | val_casted_struct id attr b ofs =>
      unfold sem_cast classify_cast
      simp
  | val_casted_union id attr b ofs =>
      unfold sem_cast classify_cast
      simp
  | val_casted_void v =>
      unfold sem_cast classify_cast
      rfl

theorem cast_idempotent (v : val) (ty ty' : type) (v' : val) (m : mem)
    (H : sem_cast v ty ty' m = some v') : sem_cast v' ty' ty' m = some v' :=
  cast_val_casted v' ty' m (cast_val_is_casted v ty ty' v' m H)

-- Moreover, casted values belong to the machine argument type corresponding
-- to the C type.

theorem val_casted_has_argtype (v : val) (ty : type) (H : val_casted v ty) :
    Val.has_argtype v (argtype_of_type ty) := by
  cases H with
  | val_casted_int sz si attr n H =>
      cases sz with
      | I32 => trivial
      | I8 =>
          cases si with
          | Signed => simpa [argtype_of_type, Val.has_argtype, cast_int_int] using H.symm
          | Unsigned => simpa [argtype_of_type, Val.has_argtype, cast_int_int] using H.symm
      | I16 =>
          cases si with
          | Signed => simpa [argtype_of_type, Val.has_argtype, cast_int_int] using H.symm
          | Unsigned => simpa [argtype_of_type, Val.has_argtype, cast_int_int] using H.symm
      | IBool =>
          simp only [argtype_of_type, Val.has_argtype]
          unfold cast_int_int at H
          split_ifs at H with hz
          · exact Or.inl H.symm
          · exact Or.inr H.symm
  | val_casted_float attr n => trivial
  | val_casted_single attr n => trivial
  | val_casted_long si attr n => trivial
  | val_casted_ptr_ptr b ofs ty attr => trivial
  | val_casted_int_ptr n ty attr hp => exact hp
  | val_casted_ptr_int b ofs si attr hp => exact hp
  | val_casted_long_ptr n ty attr hp => exact hp
  | val_casted_ptr_long b ofs si attr hp => exact hp
  | val_casted_struct id attr b ofs => trivial
  | val_casted_union id attr b ofs => trivial
  | val_casted_void v => trivial

-- Likewise, casted values belong to the machine type corresponding to the
-- C type.

theorem val_casted_has_type (v : val) (ty : type) (H : val_casted v ty) (Hty : ty ≠ .Tvoid) :
    Val.has_type v (typ_of_type ty) := by
  cases H with
  | val_casted_int sz si attr n H => trivial
  | val_casted_float attr n => trivial
  | val_casted_single attr n => trivial
  | val_casted_long si attr n => trivial
  | val_casted_ptr_ptr b ofs ty attr => exact Val.Vptr_has_type b ofs
  | val_casted_int_ptr n ty attr hp =>
      simp [typ_of_type, Tptr, hp, Val.has_type]
  | val_casted_ptr_int b ofs si attr hp => exact hp
  | val_casted_long_ptr n ty attr hp =>
      simp [typ_of_type, Tptr, hp, Val.has_type]
  | val_casted_ptr_long b ofs si attr hp => exact hp
  | val_casted_struct id attr b ofs => exact Val.Vptr_has_type b ofs
  | val_casted_union id attr b ofs => exact Val.Vptr_has_type b ofs
  | val_casted_void v => exact absurd rfl Hty

/-
Relation with the arithmetic conversions of ISO C99, section 6.3.1.

This is the ISO C algebra of arithmetic types, without qualifiers.
-/

inductive int_type : Type where
  | _Bool
  | Char | SChar | UChar
  | Short | UShort
  | Int | UInt
  | Long | ULong
  | Longlong | ULonglong
  deriving DecidableEq

inductive arith_type : Type where
  | I (it : int_type)
  | Float
  | Double
  | Longdouble
  deriving DecidableEq

def is_unsigned (t : int_type) : Bool :=
  match t with
  | ._Bool => true
  | .Char => false  -- as in most of CompCert's target ABIs
  | .SChar => false
  | .UChar => true
  | .Short => false
  | .UShort => true
  | .Int => false
  | .UInt => true
  | .Long => false
  | .ULong => true
  | .Longlong => false
  | .ULonglong => true

def unsigned_type (t : int_type) : int_type :=
  match t with
  | .Char => .UChar
  | .SChar => .UChar
  | .Short => .UShort
  | .Int => .UInt
  | .Long => .ULong
  | .Longlong => .ULonglong
  | _ => t

def int_sizeof (t : int_type) : Int :=
  match t with
  | ._Bool | .Char | .SChar | .UChar => 1
  | .Short | .UShort => 2
  | .Int | .UInt | .Long | .ULong => 4
  | .Longlong | .ULonglong => 8

-- 6.3.1.1 para 1: integer conversion rank

def rank (t : int_type) : Int :=
  match t with
  | ._Bool => 1
  | .Char | .SChar | .UChar => 2
  | .Short | .UShort => 3
  | .Int | .UInt => 4
  | .Long | .ULong => 5
  | .Longlong | .ULonglong => 6

-- 6.3.1.1 para 2: integer promotions, a.k.a. usual unary conversions

def integer_promotion (t : int_type) : int_type :=
  if rank t < rank .Int then .Int else t

/-
6.3.1.8: Usual arithmetic conversions, a.k.a. binary conversions.
This function returns the type to which the two operands must be
converted.
-/

def usual_arithmetic_conversion (t1 t2 : arith_type) : arith_type :=
  match t1, t2 with
  -- First, if the corresponding real type of either operand is long
  -- double, the other operand is converted, without change of type domain,
  -- to a type whose corresponding real type is long double.
  | .Longdouble, _ => .Longdouble
  | _, .Longdouble => .Longdouble
  -- Otherwise, if the corresponding real type of either operand is
  -- double, the other operand is converted, without change of type domain,
  -- to a type whose corresponding real type is double.
  | .Double, _ => .Double
  | _, .Double => .Double
  -- Otherwise, if the corresponding real type of either operand is
  -- float, the other operand is converted, without change of type domain,
  -- to a type whose corresponding real type is float.
  | .Float, _ => .Float
  | _, .Float => .Float
  -- Otherwise, the integer promotions are performed on both operands.
  | .I i1, .I i2 =>
      let j1 := integer_promotion i1
      let j2 := integer_promotion i2
      -- Then the following rules are applied to the promoted operands:
      -- If both operands have the same type, then no further conversion
      -- is needed.
      if j1 = j2 then .I j1 else
      match is_unsigned j1, is_unsigned j2 with
      -- Otherwise, if both operands have signed integer types or both
      -- have unsigned integer types, the operand with the type of lesser
      -- integer conversion rank is converted to the type of the operand with
      -- greater rank.
      | true, true =>
          if rank j1 < rank j2 then .I j2 else .I j1
      | false, false =>
          if rank j1 < rank j2 then .I j2 else .I j1
      | true, false =>
          -- Otherwise, if the operand that has unsigned integer type has
          -- rank greater or equal to the rank of the type of the other operand,
          -- then the operand with signed integer type is converted to the type of
          -- the operand with unsigned integer type.
          if rank j2 ≤ rank j1 then .I j1 else
          -- Otherwise, if the type of the operand with signed integer type
          -- can represent all of the values of the type of the operand with
          -- unsigned integer type, then the operand with unsigned integer type is
          -- converted to the type of the operand with signed integer type.
          if int_sizeof j1 < int_sizeof j2 then .I j2 else
          -- Otherwise, both operands are converted to the unsigned integer type
          -- corresponding to the type of the operand with signed integer type.
          .I (unsigned_type j2)
      | false, true =>
          -- Same logic as above, swapping the roles of j1 and j2
          if rank j1 ≤ rank j2 then .I j2 else
          if int_sizeof j2 < int_sizeof j1 then .I j1 else
          .I (unsigned_type j1)

-- Mapping ISO arithmetic types to CompCert types

def proj_type (t : arith_type) : type :=
  match t with
  | .I ._Bool => .Tint .IBool .Unsigned noattr
  | .I .Char => .Tint .I8 .Unsigned noattr
  | .I .SChar => .Tint .I8 .Signed noattr
  | .I .UChar => .Tint .I8 .Unsigned noattr
  | .I .Short => .Tint .I16 .Signed noattr
  | .I .UShort => .Tint .I16 .Unsigned noattr
  | .I .Int => .Tint .I32 .Signed noattr
  | .I .UInt => .Tint .I32 .Unsigned noattr
  | .I .Long => .Tint .I32 .Signed noattr
  | .I .ULong => .Tint .I32 .Unsigned noattr
  | .I .Longlong => .Tlong .Signed noattr
  | .I .ULonglong => .Tlong .Unsigned noattr
  | .Float => .Tfloat .F32 noattr
  | .Double => .Tfloat .F64 noattr
  | .Longdouble => .Tfloat .F64 noattr

-- Relation between [typeconv] and integer promotion.

omit [Archi] in
theorem typeconv_integer_promotion (i : int_type) :
    typeconv (proj_type (.I i)) = proj_type (.I (integer_promotion i)) := by
  cases i <;> rfl

-- Relation between [classify_binarith] and arithmetic conversion.

omit [Archi] in
theorem classify_binarith_arithmetic_conversion (t1 t2 : arith_type) :
    binarith_type (classify_binarith (proj_type t1) (proj_type t2)) =
    proj_type (usual_arithmetic_conversion t1 t2) := by
  cases t1 with
  | I i1 =>
      cases t2 with
      | I i2 => cases i1 <;> cases i2 <;> rfl
      | Float => cases i1 <;> rfl
      | Double => cases i1 <;> rfl
      | Longdouble => cases i1 <;> rfl
  | Float =>
      cases t2 with
      | I i2 => cases i2 <;> rfl
      | Float => rfl
      | Double => rfl
      | Longdouble => rfl
  | Double =>
      cases t2 with
      | I i2 => cases i2 <;> rfl
      | Float => rfl
      | Double => rfl
      | Longdouble => rfl
  | Longdouble =>
      cases t2 with
      | I i2 => cases i2 <;> rfl
      | Float => rfl
      | Double => rfl
      | Longdouble => rfl

