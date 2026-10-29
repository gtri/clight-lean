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

/- This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. -/

import CLightLean.Archi
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats

variable [Archi]

-- Syntactic elements

/- Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by Nat. WARNING: divergence from CompCert/VST, where they are represented by the type of positive integers. -/

def ident := Nat deriving DecidableEq, Hashable, ToString, Ord

/- The intermediate languages are weakly typed, using the following types: -/
inductive typ : Type where
  | Tint                -- 32-bit integers or pointers
  | Tfloat              -- 64-bit double-precision floats
  | Tlong               -- 64-bit integers
  | Tsingle             -- 32-bit single-precision floats
  | Tany32              -- any 32-bit value
  | Tany64              -- any 64-bit value, i.e. any value
  deriving DecidableEq

def Tptr : typ := if Archi.ptr64 then typ.Tlong else typ.Tint

def typesize (ty : typ) : Int :=
  match ty with
  | typ.Tint => 4
  | typ.Tfloat => 8
  | typ.Tlong => 8
  | typ.Tsingle => 4
  | typ.Tany32 => 4
  | typ.Tany64 => 8

omit [Archi] in
theorem typesize_pos : ∀ ty, typesize ty > 0 := by
  intro ty; cases ty <;> simp [typesize]

theorem typesize_Tptr: typesize Tptr = if Archi.ptr64 then 8 else 4 := by
  unfold Tptr; cases Archi.ptr64 <;> rfl

/- All values of size 32 bits are also of type [Tany32].  All values
  are of type [Tany64].  This corresponds to the following subtyping
  relation over types. -/

def subtype (ty1 ty2 : typ) : Bool :=
  match ty1, ty2 with
  | typ.Tint, typ.Tint => true
  | typ.Tlong, typ.Tlong => true
  | typ.Tfloat, typ.Tfloat => true
  | typ.Tsingle, typ.Tsingle => true
  | typ.Tint, typ.Tany32 => true
  | typ.Tsingle, typ.Tany32 => true
  | typ.Tany32, typ.Tany32 => true
  | _, typ.Tany64 => true
  | _, _ => false

def subtype_list (tyl1 tyl2 : List typ) : Bool :=
  match tyl1, tyl2 with
  | [], [] => true
  | ty1::tys1, ty2::tys2 => subtype ty1 ty2 && subtype_list tys1 tys2
  | _, _ => false

/- To describe function arguments and function return values,
    we use the more precise types below. -/

inductive xtype : Type where
  | Xbool               -- Boolean value (0 or 1)
  | Xint8signed         -- 8-bit signed integer
  | Xint8unsigned       -- 8-bit unsigned integer
  | Xint16signed        -- 16-bit signed integer
  | Xint16unsigned      -- 16-bit unsigned integer
  | Xint                -- 32-bit integers or pointers
  | Xfloat              -- 64-bit double-precision floats
  | Xlong               -- 64-bit integers
  | Xsingle             -- 32-bit single-precision floats
  | Xptr                -- pointers and pointer-sized integers
  | Xany32              -- any 32-bit value
  | Xany64              -- any 64-bit value, i.e. any value
  | Xvoid               -- no meaningful value
  deriving DecidableEq

def Xsize_t : xtype := if Archi.ptr64 then xtype.Xlong else xtype.Xint

def inj_type (t : typ) : xtype :=
  match t with
  | typ.Tint => xtype.Xint
  | typ.Tfloat => xtype.Xfloat
  | typ.Tlong => xtype.Xlong
  | typ.Tsingle => xtype.Xsingle
  | typ.Tany32 => xtype.Xany32
  | typ.Tany64 => xtype.Xany64

def proj_xtype (x : xtype) : typ :=
  match x with
  | xtype.Xbool => typ.Tint
  | xtype.Xint8signed => typ.Tint
  | xtype.Xint8unsigned => typ.Tint
  | xtype.Xint16signed => typ.Tint
  | xtype.Xint16unsigned => typ.Tint
  | xtype.Xint => typ.Tint
  | xtype.Xfloat => typ.Tfloat
  | xtype.Xlong => typ.Tlong
  | xtype.Xsingle => typ.Tsingle
  | xtype.Xptr => Tptr
  | xtype.Xany32 => typ.Tany32
  | xtype.Xany64 => typ.Tany64
  | xtype.Xvoid => typ.Tint

theorem proj_inj_type : ∀ t, proj_xtype (inj_type t) = t := by
  intro t; cases t <;> rfl



/- Additionally, function definitions and function calls are annotated
  by function signatures indicating:
- the number and types of arguments;
- the type of the returned value;
- additional information on which calling convention to use.

These signatures are used in particular to determine appropriate
calling conventions for the function. -/

structure calling_convention : Type where
  mkcallconv ::
  cc_vararg : Option Nat      -- variable-arity function (+ number of fixed args). WARNING: divergence from CompCert/VST, where this is option Z
  cc_unproto : Bool           -- old-style unprototyped function
  cc_structret : Bool         -- function returning a struct
  deriving DecidableEq

def cc_default : calling_convention := { cc_vararg := none, cc_unproto := false, cc_structret := false }

structure signature : Type where
  mksignature ::
  sig_args : List xtype
  sig_res : xtype
  sig_cc : calling_convention
  deriving DecidableEq

def proj_sig_args (s : signature) : List typ := List.map proj_xtype s.sig_args

def proj_sig_res (s : signature) : typ := proj_xtype s.sig_res

def signature_main : signature := { sig_args := [], sig_res := xtype.Xint, sig_cc := cc_default }

/- Memory accesses (load and store instructions) are annotated by
  a "memory chunk" indicating the type, size and signedness of the
  chunk of memory being accessed. -/

inductive memory_chunk : Type where
  | Mbool           -- 8-bit integer containing 0 or 1
  | Mint8signed     -- 8-bit signed integer
  | Mint8unsigned   -- 8-bit unsigned integer
  | Mint16signed    -- 16-bit signed integer
  | Mint16unsigned  -- 16-bit unsigned integer
  | Mint32          -- 32-bit integer, or pointer
  | Mint64          -- 64-bit integer
  | Mfloat32        -- 32-bit single-precision float
  | Mfloat64        -- 64-bit double-precision float
  | Many32          -- any value that fits in 32 bits
  | Many64          -- any value
  deriving DecidableEq

def Mptr : memory_chunk := if Archi.ptr64 then memory_chunk.Mint64 else memory_chunk.Mint32

/- The type (integer/pointer or float) of a chunk. -/

def type_of_chunk (c : memory_chunk) : typ :=
  match c with
  | memory_chunk.Mbool => typ.Tint
  | memory_chunk.Mint8signed => typ.Tint
  | memory_chunk.Mint8unsigned => typ.Tint
  | memory_chunk.Mint16signed => typ.Tint
  | memory_chunk.Mint16unsigned => typ.Tint
  | memory_chunk.Mint32 => typ.Tint
  | memory_chunk.Mint64 => typ.Tlong
  | memory_chunk.Mfloat32 => typ.Tsingle
  | memory_chunk.Mfloat64 => typ.Tfloat
  | memory_chunk.Many32 => typ.Tany32
  | memory_chunk.Many64 => typ.Tany64

theorem type_of_Mptr : type_of_chunk Mptr = Tptr := by
  unfold Mptr Tptr; cases Archi.ptr64 <;> rfl

/- Same, as an extended type. -/

def xtype_of_chunk (c : memory_chunk) : xtype :=
  match c with
  | memory_chunk.Mbool => xtype.Xbool
  | memory_chunk.Mint8signed => xtype.Xint8signed
  | memory_chunk.Mint8unsigned => xtype.Xint8unsigned
  | memory_chunk.Mint16signed => xtype.Xint16signed
  | memory_chunk.Mint16unsigned => xtype.Xint16unsigned
  | memory_chunk.Mint32 => xtype.Xint
  | memory_chunk.Mint64 => xtype.Xlong
  | memory_chunk.Mfloat32 => xtype.Xsingle
  | memory_chunk.Mfloat64 => xtype.Xfloat
  | memory_chunk.Many32 => xtype.Xany32
  | memory_chunk.Many64 => xtype.Xany64

theorem proj_xtype_of_chunk :
  ∀ chunk, proj_xtype (xtype_of_chunk chunk) = type_of_chunk chunk := by
  intro chunk; cases chunk <;> rfl

/- The chunk that is appropriate to store and reload a value of
  the given type, without losing information. -/

def chunk_of_type (ty : typ) : memory_chunk :=
  match ty with
  | typ.Tint => memory_chunk.Mint32
  | typ.Tfloat => memory_chunk.Mfloat64
  | typ.Tlong => memory_chunk.Mint64
  | typ.Tsingle => memory_chunk.Mfloat32
  | typ.Tany32 => memory_chunk.Many32
  | typ.Tany64 => memory_chunk.Many64

theorem chunk_of_Tptr : chunk_of_type Tptr = Mptr := by
  unfold Mptr Tptr; cases Archi.ptr64 <;> rfl

/- Initialization data for global variables. -/

inductive init_data : Type where
  | Init_int8 : CompCert.Int → init_data
  | Init_int16 : CompCert.Int → init_data
  | Init_int32 : CompCert.Int → init_data
  | Init_int64 : CompCert.Int64 → init_data
  | Init_float32 : CompCert.Float32 → init_data
  | Init_float64 : CompCert.Float64 → init_data
  | Init_space : Int → init_data
  | Init_addrof : ident → Int → init_data  -- address of symbol + offset. WARNING: CompCert uses ptrofs for offset, we use Int

def init_data_size (i : init_data) : Int :=
  match i with
  | init_data.Init_int8 _ => 1
  | init_data.Init_int16 _ => 2
  | init_data.Init_int32 _ => 4
  | init_data.Init_int64 _ => 8
  | init_data.Init_float32 _ => 4
  | init_data.Init_float64 _ => 8
  | init_data.Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | init_data.Init_space n => max n 0

def init_data_list_size (il : List init_data) : Int :=
  match il with
  | [] => 0
  | i :: il' => init_data_size i + init_data_list_size il'

theorem init_data_size_pos : ∀ i, init_data_size i ≥ 0 := by
  intro i; cases i <;> simp [init_data_size]; split <;> omega

theorem init_data_list_size_pos : ∀ il, init_data_list_size il ≥ 0 := by
  intro il; induction il with
  | nil => simp [init_data_list_size]
  | cons a il' ih =>
      simp [init_data_list_size]
      have : init_data_size a ≥ 0 := init_data_size_pos a
      omega

/- Information attached to global variables. -/

structure globvar (V : Type) : Type where
  mkglobvar ::
  gvar_info : V                    -- language-dependent info, e.g. a type
  gvar_init : List init_data       -- initialization data
  gvar_readonly : Bool             -- read-only variable? (const)
  gvar_volatile : Bool             -- volatile variable?

/- Whole programs consist of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside
  this compilation unit);
- the name of the "main" function that serves as entry point in the program.

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. -/

inductive globdef (F V : Type) : Type where
  | Gfun (f : F)
  | Gvar (v : globvar V)

structure program (F V : Type) : Type where
  mkprogram ::
  prog_defs : List (ident × globdef F V)
  prog_public : List ident
  prog_main : ident

def prog_defs_names (F V : Type) (p : program F V) : List ident :=
  List.map Prod.fst p.prog_defs

/- The "definition map" of a program maps names of globals to their definitions.
  If several definitions have the same name, the one appearing last in [p.(prog_defs)] wins. -/

def prog_defmap (F V : Type) [BEq ident] [Hashable ident] (p : program F V) : Std.HashMap ident (globdef F V) :=
  Std.HashMap.ofList p.prog_defs

/- Generic transformations over programs -/

/- Omitted: transform_program_globdef, transform_program, transform_partial_program2,
  transform_partial_program, and related error monad definitions. These are used for
  compiler passes in CompCert but not immediately needed for VST verification. -/

-- External functions

/- For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. -/

inductive external_function : Type where
  | EF_external (name : String) (sg : signature)
     -- A system call or library function.  Produces an event in the trace.
  | EF_builtin (name : String) (sg : signature)
     -- A compiler built-in function.  Behaves like an external, but can be inlined by the compiler.
  | EF_runtime (name : String) (sg : signature)
     -- A function from the run-time library.  Behaves like an external, but must not be redefined.
  | EF_vload (chunk : memory_chunk)
     /- A volatile read operation.  If the address given as first argument
        points within a volatile global variable, generate an
        event and return the value found in this event.  Otherwise,
        produce no event and behave like a regular memory load. -/
  | EF_vstore (chunk : memory_chunk)
     /- A volatile store operation.   If the address given as first argument
        points within a volatile global variable, generate an event.
        Otherwise, produce no event and behave like a regular memory store. -/
  | EF_malloc
     /- Dynamic memory allocation.  Takes the requested size in bytes
        as argument; returns a pointer to a fresh block of the given size.
        Produces no observable event. -/
  | EF_free
     /- Dynamic memory deallocation.  Takes a pointer to a block
        allocated by an [EF_malloc] external call and frees the
        corresponding block.
        Produces no observable event. -/
  | EF_memcpy (sz : Int) (al : Int)
     -- Block copy, of [sz] bytes, between addresses that are [al]-aligned.
  | EF_annot (kind : ident) (text : String) (targs : List typ)
     /- A programmer-supplied annotation.  Takes zero, one or several arguments,
        produces an event carrying the text and the values of these arguments,
        and returns no value. -/
  | EF_annot_val (kind : ident) (text : String) (targ : typ)
     /- Another form of annotation that takes one argument, produces
        an event carrying the text and the value of this argument,
        and returns the value of the argument. -/
  | EF_inline_asm (text : String) (sg : signature) (clobbers : List String)
     /- Inline [asm] statements.  Semantically, treated like an
        annotation with no parameters ([EF_annot text nil]).  To be
        used with caution, as it can invalidate the semantic
        preservation theorem.  Generated only if [-finline-asm] is
        given. -/
  | EF_debug (kind : ident) (text : ident) (targs : List typ)
     /- Transport debugging information from the front-end to the generated
        assembly.  Takes zero, one or several arguments like [EF_annot].
        Unlike [EF_annot], produces no observable event. -/
  deriving DecidableEq

-- The type signature of an external function.

def ef_sig (ef : external_function) : signature :=
  match ef with
  | external_function.EF_external _name sg => sg
  | external_function.EF_builtin _name sg => sg
  | external_function.EF_runtime _name sg => sg
  | external_function.EF_vload chunk =>
      signature.mksignature [xtype.Xptr] (xtype_of_chunk chunk) cc_default
  | external_function.EF_vstore chunk =>
      signature.mksignature [xtype.Xptr, xtype_of_chunk chunk] xtype.Xvoid cc_default
  | external_function.EF_malloc =>
      signature.mksignature [Xsize_t] xtype.Xptr cc_default
  | external_function.EF_free =>
      signature.mksignature [xtype.Xptr] xtype.Xvoid cc_default
  | external_function.EF_memcpy _sz _al =>
      signature.mksignature [xtype.Xptr, xtype.Xptr] xtype.Xvoid cc_default
  | external_function.EF_annot _kind _text targs =>
      signature.mksignature (List.map inj_type targs) xtype.Xvoid cc_default
  | external_function.EF_annot_val _kind _text targ =>
      signature.mksignature [inj_type targ] (inj_type targ) cc_default
  | external_function.EF_inline_asm _text sg _clob => sg
  | external_function.EF_debug _kind _text targs =>
      signature.mksignature (List.map inj_type targs) xtype.Xvoid cc_default

-- Whether an external function should be inlined by the compiler.

def ef_inline (ef : external_function) : Bool :=
  match ef with
  | external_function.EF_external _name _sg => false
  | external_function.EF_builtin _name _sg => true
  | external_function.EF_runtime _name _sg => false
  | external_function.EF_vload _chunk => true
  | external_function.EF_vstore _chunk => true
  | external_function.EF_malloc => false
  | external_function.EF_free => false
  | external_function.EF_memcpy _sz _al => true
  | external_function.EF_annot _kind _text _targs => true
  | external_function.EF_annot_val _kind _text _rg => true
  | external_function.EF_inline_asm _text _sg _clob => true
  | external_function.EF_debug _kind _text _targs => true

-- Whether an external function must reload its arguments.

def ef_reloads (ef : external_function) : Bool :=
  match ef with
  | external_function.EF_annot _kind _text _targs => false
  | external_function.EF_debug _kind _text _targs => false
  | _ => true

-- Function definitions are the union of internal and external functions.

inductive fundef (F : Type) : Type where
  | Internal (f : F)
  | External (ef : external_function)

-- Omitted: transf_fundef and transf_partial_fundef (compiler pass transformations).

-- Omitted: Remaining rpair operations (regs_of_rpairs, forall_rpair, etc.) and builtin argument/result types (builtin_arg, builtin_res, and related operations) - used in lower-level compiler passes, not needed for Clight/VST.
