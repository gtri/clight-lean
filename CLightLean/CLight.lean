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

/- The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. -/

import CLightLean.AST
import CLightLean.CTypes
import CLightLean.Cop
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats
import CLightLean.Lib.Ptrofs
import CLightLean.Values
import CLightLean.Memory
import CLightLean.Events
import CLightLean.Globalenvs
import CLightLean.Smallstep
import CLightLean.Archi

open Memory (mem)
open Events (trace E0)

variable [Archi]

-- * Abstract syntax

-- ** Expressions

/- Clight expressions correspond to the "pure" subset of C expressions.
  The main omissions are string literals and assignment operators
  (`=`, `+=`, `++`, etc).  In Clight, assignment is a statement,
  not an expression.  Additionally, an expression can also refer to
  temporary variables, which are a separate class of local variables
  that do not reside in memory and whose address cannot be taken.

  As in Compcert C, all expressions are annotated with their types,
  as needed to resolve operator overloading and type-dependent behaviors. -/

inductive expr : Type where
  | Econst_int (i : CompCert.Int) (ty : type)      -- integer literal
  | Econst_float (f : CompCert.Float64) (ty : type)  -- double float literal
  | Econst_single (f : CompCert.Float32) (ty : type) -- single float literal
  | Econst_long (i : CompCert.Int64) (ty : type)   -- long integer literal
  | Evar (id : ident) (ty : type)                  -- variable
  | Etempvar (id : ident) (ty : type)               -- temporary variable
  | Ederef (a : expr) (ty : type)                   -- pointer dereference (unary `*`)
  | Eaddrof (a : expr) (ty : type)                  -- address-of operator (`&`)
  | Eunop (op : unary_operation) (a : expr) (ty : type)              -- unary operation
  | Ebinop (op : binary_operation) (a1 a2 : expr) (ty : type)        -- binary operation
  | Ecast (a : expr) (ty : type)                    -- type cast (`(ty) e`)
  | Efield (a : expr) (i : ident) (ty : type)        -- access to a member of a struct or union
  | Esizeof (ty1 : type) (ty : type)                 -- size of a type
  | Ealignof (ty1 : type) (ty : type)                -- alignment of a type

/-- Extract the type part of a type-annotated Clight expression. -/
def typeof (e : expr) : type :=
  match e with
  | .Econst_int _ ty => ty
  | .Econst_float _ ty => ty
  | .Econst_single _ ty => ty
  | .Econst_long _ ty => ty
  | .Evar _ ty => ty
  | .Etempvar _ ty => ty
  | .Ederef _ ty => ty
  | .Eaddrof _ ty => ty
  | .Eunop _ _ ty => ty
  | .Ebinop _ _ _ ty => ty
  | .Ecast _ ty => ty
  | .Efield _ _ ty => ty
  | .Esizeof _ ty => ty
  | .Ealignof _ ty => ty

-- ** Statements

/- Clight statements are similar to those of Compcert C, with the addition
  of assignment (of a rvalue to a lvalue), assignment to a temporary,
  and function call (with assignment of the result to a temporary).
  The three C loops are replaced by a single infinite loop `Sloop s1
  s2` that executes `s1` then `s2` repeatedly.  A `continue` in `s1`
  branches to `s2`. -/

-- NOTE: `abbrev` (not `def`), so instance search for `DecidableEq` unfolds `label` to
-- `ident`'s existing instance (see `find_label`'s use of `lbl = lbl'` below).
abbrev label : Type := ident

mutual
  inductive statement : Type where
    | Sskip                                                       -- do nothing
    | Sassign (a1 a2 : expr)                                      -- assignment `lvalue = rvalue`
    | Sset (id : ident) (a : expr)                                -- assignment `tempvar = rvalue`
    | Scall (optid : Option ident) (a : expr) (al : List expr)    -- function call
    | Sbuiltin (optid : Option ident) (ef : external_function) (tyargs : List type) (al : List expr)
        -- builtin invocation
    | Ssequence (s1 s2 : statement)                                -- sequence
    | Sifthenelse (a : expr) (s1 s2 : statement)                   -- conditional
    | Sloop (s1 s2 : statement)                                    -- infinite loop
    | Sbreak                                                       -- `break` statement
    | Scontinue                                                    -- `continue` statement
    | Sreturn (a : Option expr)                                    -- `return` statement
    | Sswitch (a : expr) (sl : labeled_statements)                 -- `switch` statement
    | Slabel (lbl : label) (s : statement)
    | Sgoto (lbl : label)

  /-- Cases of a `switch`. -/
  inductive labeled_statements : Type where
    | LSnil
    | LScons (c : Option Int) (s : statement) (sl' : labeled_statements)
        -- `none` is `default`, `some x` is `case x`
end

-- The C loops are derived forms.

def Swhile (e : expr) (s : statement) : statement :=
  .Sloop (.Ssequence (.Sifthenelse e .Sskip .Sbreak) s) .Sskip

def Sdowhile (s : statement) (e : expr) : statement :=
  .Sloop s (.Sifthenelse e .Sskip .Sbreak)

def Sfor (s1 : statement) (e2 : expr) (s3 s4 : statement) : statement :=
  .Ssequence s1 (.Sloop (.Ssequence (.Sifthenelse e2 .Sskip .Sbreak) s3) s4)

-- ** Functions

/- A function definition is composed of its return type (`fn_return`),
  the names and types of its parameters (`fn_params`), the names
  and types of its local variables (`fn_vars`), and the body of the
  function (a statement, `fn_body`). -/

structure function : Type where
  fn_return : type
  fn_callconv : calling_convention
  fn_params : List (ident × type)
  fn_vars : List (ident × type)
  fn_temps : List (ident × type)
  fn_body : statement

def var_names (vars : List (ident × type)) : List ident :=
  vars.map Prod.fst

/- Functions can either be defined (`Internal`) or declared as
  external functions (`External`).

  NOTE: Coq writes `Definition fundef := Ctypes.fundef function.` here, giving a bare
  local name `fundef` that shadows `AST.fundef`/`Ctypes.fundef` within the rest of the
  Coq module. Lean has no such per-file shadowing for top-level names, and `fundef` is
  already bound (unprefixed) by `AST.lean`'s generic `fundef (F : Type)` — so, exactly
  like `CTypes.lean`'s `fundef_type` (added for the very same reason), we spell this out
  as `fundef_type function` at each use site instead of introducing a clashing alias. -/

/-- The type of a function definition. -/
def type_of_function (f : function) : type :=
  .Tfunction (type_of_params f.fn_params) f.fn_return f.fn_callconv

def type_of_fundef (f : fundef_type function) : type :=
  match f with
  | .Internal fd => type_of_function fd
  | .External _id args res cc => .Tfunction args res cc

-- ** Programs

/- As defined in module `CTypes`, a program, or compilation unit, is
  composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions.

  NOTE: Coq writes `Definition program := Ctypes.program function.` here; as with
  `fundef` above, we spell this out as `program_type function` at each use site
  instead of introducing an alias that would clash with `AST.lean`'s generic
  `program (F V : Type)`. -/

-- * Operational semantics

/- The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module `Globalenvs`.)
  It also contains a composite environment, used by type-dependent operations. -/

structure genv where
  genv_genv : Genv.t (fundef_type function) type
  genv_cenv : composite_env

def globalenv (p : program_type function) : genv :=
  { genv_genv := Genv.globalenv p, genv_cenv := p.prog_comp_env }

/- The local environment maps local variables to block references and
  types.  The current value of the variable is stored in the
  associated memory block. -/

abbrev env : Type := Std.HashMap ident (block × type)

def empty_env : env := ∅  -- map variable -> location & type

/- The temporary environment maps local temporaries to values. -/

abbrev temp_env : Type := Std.HashMap ident val

/- `deref_loc ty m b ofs bf v` computes the value of a datum
  of type `ty` residing in memory `m` at block `b`, offset `ofs`,
  and bitfield designation `bf`.
  If the type `ty` indicates an access by value, the corresponding
  memory load is performed.  If the type `ty` indicates an access by
  reference or by copy, the pointer `Vptr b ofs` is returned. -/

inductive deref_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs) : bitfield → val → Prop where
  | deref_loc_value (chunk : memory_chunk) (v : val) :
      access_mode ty = .By_value chunk →
      Memory.loadv chunk m (.Vptr b ofs) = some v →
      deref_loc ty m b ofs .Full v
  | deref_loc_reference :
      access_mode ty = .By_reference →
      deref_loc ty m b ofs .Full (.Vptr b ofs)
  | deref_loc_copy :
      access_mode ty = .By_copy →
      deref_loc ty m b ofs .Full (.Vptr b ofs)
  | deref_loc_bitfield (sz : intsize) (sg : signedness) (pos width : Int) (v : val) :
      load_bitfield ty sz sg pos width m (.Vptr b ofs) v →
      deref_loc ty m b ofs (.Bits sz sg pos width) v

/- Symmetrically, `assign_loc ty m b ofs bf v m'` returns the
  memory state after storing the value `v` in the datum
  of type `ty` residing in memory `m` at block `b`, offset `ofs`,
  bitfield designation `bf`.
  This is allowed only if `ty` indicates an access by value or by copy.
  `m'` is the updated memory state. -/

inductive assign_loc (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs) :
    bitfield → val → mem → Prop where
  | assign_loc_value (v : val) (chunk : memory_chunk) (m' : mem) :
      access_mode ty = .By_value chunk →
      Memory.storev chunk m (.Vptr b ofs) v = some m' →
      assign_loc ce ty m b ofs .Full v m'
  | assign_loc_copy (b' : block) (ofs' : ptrofs) (bytes : List Memory.memval) (m' : mem) :
      access_mode ty = .By_copy →
      (sizeof ce ty > 0 → alignof_blockcopy ce ty ∣ Ptrofs.unsigned ofs') →
      (sizeof ce ty > 0 → alignof_blockcopy ce ty ∣ Ptrofs.unsigned ofs) →
      (b' ≠ b ∨ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
        ∨ Ptrofs.unsigned ofs' + sizeof ce ty ≤ Ptrofs.unsigned ofs
        ∨ Ptrofs.unsigned ofs + sizeof ce ty ≤ Ptrofs.unsigned ofs') →
      Memory.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = some bytes →
      Memory.storebytes m b (Ptrofs.unsigned ofs) bytes = some m' →
      assign_loc ce ty m b ofs .Full (.Vptr b' ofs') m'
  | assign_loc_bitfield (sz : intsize) (sg : signedness) (pos width : Int) (v : val) (m' : mem) (v' : val) :
      store_bitfield ty sz sg pos width m (.Vptr b ofs) v m' v' →
      assign_loc ce ty m b ofs (.Bits sz sg pos width) v m'

section SEMANTICS

variable (ge : genv)

/- Allocation of function-local variables.
  `alloc_variables e1 m1 vars e2 m2` allocates one memory block
  for each variable declared in `vars`, and associates the variable
  name with this block.  `e1` and `m1` are the initial local environment
  and memory state.  `e2` and `m2` are the final local environment
  and memory state. -/

inductive alloc_variables : env → mem → List (ident × type) → env → mem → Prop where
  | alloc_variables_nil (e : env) (m : mem) :
      alloc_variables e m [] e m
  | alloc_variables_cons (e : env) (m : mem) (id : ident) (ty : type)
      (vars : List (ident × type)) (m1 : mem) (b1 : block) (m2 : mem) (e2 : env) :
      Memory.alloc m 0 (sizeof ge.genv_cenv ty) = (b1, m1) →
      alloc_variables (e.insert id (b1, ty)) m1 vars e2 m2 →
      alloc_variables e m ((id, ty) :: vars) e2 m2

/- Initialization of local variables that are parameters to a function.
  `bind_parameters e m1 params args m2` stores the values `args`
  in the memory blocks corresponding to the variables `params`.
  `m1` is the initial memory state and `m2` the final memory state. -/

inductive bind_parameters (e : env) : mem → List (ident × type) → List val → mem → Prop where
  | bind_parameters_nil (m : mem) :
      bind_parameters e m [] [] m
  | bind_parameters_cons (m : mem) (id : ident) (ty : type) (params : List (ident × type))
      (v1 : val) (vl : List val) (b : block) (m1 m2 : mem) :
      e.get? id = some (b, ty) →
      assign_loc ge.genv_cenv ty m b Ptrofs.zero .Full v1 m1 →
      bind_parameters e m1 params vl m2 →
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2

/- Initialization of temporary variables. -/

def create_undef_temps (temps : List (ident × type)) : temp_env :=
  match temps with
  | [] => ∅
  | (id, _t) :: temps' => (create_undef_temps temps').insert id .Vundef

/- Initialization of temporary variables that are parameters to a function. -/

def bind_parameter_temps (formals : List (ident × type)) (args : List val)
    (le : temp_env) : Option temp_env :=
  match formals, args with
  | [], [] => some le
  | (id, _t) :: xl, v :: vl => bind_parameter_temps xl vl (le.insert id v)
  | _, _ => none

/- Return the list of blocks in the codomain of `e`, with low and high bounds. -/

def block_of_binding (id_b_ty : ident × (block × type)) : block × Int × Int :=
  match id_b_ty with
  | (_id, (b, ty)) => (b, 0, sizeof ge.genv_cenv ty)

def blocks_of_env (e : env) : List (block × Int × Int) :=
  e.toList.map (block_of_binding ge)

/- Optional assignment to a temporary -/

def set_opttemp (optid : Option ident) (v : val) (le : temp_env) : temp_env :=
  match optid with
  | none => le
  | some id => le.insert id v

/- Selection of the appropriate case of a `switch`, given the value `n`
  of the selector expression. -/

def select_switch_default (sl : labeled_statements) : labeled_statements :=
  match sl with
  | .LSnil => sl
  | .LScons none _s _sl' => sl
  | .LScons (some _i) _s sl' => select_switch_default sl'

def select_switch_case (n : Int) (sl : labeled_statements) : Option labeled_statements :=
  match sl with
  | .LSnil => none
  | .LScons none _s sl' => select_switch_case n sl'
  | .LScons (some c) _s sl' => if c = n then some sl else select_switch_case n sl'

def select_switch (n : Int) (sl : labeled_statements) : labeled_statements :=
  match select_switch_case n sl with
  | some sl' => sl'
  | none => select_switch_default sl

/- Turn a labeled statement into a sequence -/

def seq_of_labeled_statement (sl : labeled_statements) : statement :=
  match sl with
  | .LSnil => .Sskip
  | .LScons _ s sl' => .Ssequence s (seq_of_labeled_statement sl')

-- ** Evaluation of expressions

/- `eval_expr ge e le m a v` defines the evaluation of expression `a`
  in r-value position.  `v` is the value of the expression.
  `e` is the current environment and `m` is the current memory state.

  `eval_lvalue ge e m a b ofs` defines the evaluation of expression `a`
  in l-value position.  The result is the memory location `b, ofs`
  that contains the value of the expression `a`, and the bitfield `bf`
  designation. -/

section EXPR

variable (e : env) (le : temp_env) (m : mem)

/- `eval_expr ge e le m a v` defines the evaluation of expression `a`
  in r-value position.  `v` is the value of the expression.
  `e` is the current environment and `m` is the current memory state.

  `eval_lvalue ge e m a b ofs` defines the evaluation of expression `a`
  in l-value position.  The result is the memory location `b, ofs`
  that contains the value of the expression `a`, and the bitfield `bf`
  designation.

  NOTE: unlike every other relation/def in this file, `ge`/`e`/`le`/`m` must be
  spelled out as EXPLICIT parameters on `eval_expr`/`eval_lvalue`'s own headers
  below, rather than relying on section-`variable` auto-inclusion. Lean's
  auto-inclusion mechanism (which works fine for ordinary single `inductive`s
  elsewhere in this file, e.g. `alloc_variables`) does not propagate section
  variables into `inductive`s declared inside a `mutual ... end` block, so
  each cross-reference between the two mutual relations below must pass them
  explicitly too. -/

mutual
  inductive eval_expr (ge : genv) (e : env) (le : temp_env) (m : mem) : expr → val → Prop where
    | eval_Econst_int (i : CompCert.Int) (ty : type) :
        eval_expr ge e le m (.Econst_int i ty) (.Vint i)
    | eval_Econst_float (f : CompCert.Float64) (ty : type) :
        eval_expr ge e le m (.Econst_float f ty) (.Vfloat f)
    | eval_Econst_single (f : CompCert.Float32) (ty : type) :
        eval_expr ge e le m (.Econst_single f ty) (.Vsingle f)
    | eval_Econst_long (i : CompCert.Int64) (ty : type) :
        eval_expr ge e le m (.Econst_long i ty) (.Vlong i)
    | eval_Etempvar (id : ident) (ty : type) (v : val) :
        le.get? id = some v →
        eval_expr ge e le m (.Etempvar id ty) v
    | eval_Eaddrof (a : expr) (ty : type) (loc : block) (ofs : ptrofs) :
        eval_lvalue ge e le m a loc ofs .Full →
        eval_expr ge e le m (.Eaddrof a ty) (.Vptr loc ofs)
    | eval_Eunop (op : unary_operation) (a : expr) (ty : type) (v1 v : val) :
        eval_expr ge e le m a v1 →
        sem_unary_operation op v1 (typeof a) m = some v →
        eval_expr ge e le m (.Eunop op a ty) v
    | eval_Ebinop (op : binary_operation) (a1 a2 : expr) (ty : type) (v1 v2 v : val) :
        eval_expr ge e le m a1 v1 →
        eval_expr ge e le m a2 v2 →
        sem_binary_operation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m = some v →
        eval_expr ge e le m (.Ebinop op a1 a2 ty) v
    | eval_Ecast (a : expr) (ty : type) (v1 v : val) :
        eval_expr ge e le m a v1 →
        sem_cast v1 (typeof a) ty m = some v →
        eval_expr ge e le m (.Ecast a ty) v
    | eval_Esizeof (ty1 ty : type) :
        eval_expr ge e le m (.Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge.genv_cenv ty1)))
    | eval_Ealignof (ty1 ty : type) :
        eval_expr ge e le m (.Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge.genv_cenv ty1)))
    | eval_Elvalue (a : expr) (loc : block) (ofs : ptrofs) (bf : bitfield) (v : val) :
        eval_lvalue ge e le m a loc ofs bf →
        deref_loc (typeof a) m loc ofs bf v →
        eval_expr ge e le m a v

  inductive eval_lvalue (ge : genv) (e : env) (le : temp_env) (m : mem) :
      expr → block → ptrofs → bitfield → Prop where
    | eval_Evar_local (id : ident) (l : block) (ty : type) :
        e.get? id = some (l, ty) →
        eval_lvalue ge e le m (.Evar id ty) l Ptrofs.zero .Full
    | eval_Evar_global (id : ident) (l : block) (ty : type) :
        e.get? id = none →
        Genv.find_symbol ge.genv_genv id = some l →
        eval_lvalue ge e le m (.Evar id ty) l Ptrofs.zero .Full
    | eval_Ederef (a : expr) (ty : type) (l : block) (ofs : ptrofs) :
        eval_expr ge e le m a (.Vptr l ofs) →
        eval_lvalue ge e le m (.Ederef a ty) l ofs .Full
    | eval_Efield_struct (a : expr) (i : ident) (ty : type) (l : block) (ofs : ptrofs)
        (id : ident) (co : composite) (att : attr) (delta : Int) (bf : bitfield) :
        eval_expr ge e le m a (.Vptr l ofs) →
        typeof a = .Tstruct id att →
        ge.genv_cenv.get? id = some co →
        field_offset ge.genv_cenv i co.co_members = Except.ok (delta, bf) →
        eval_lvalue ge e le m (.Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
    | eval_Efield_union (a : expr) (i : ident) (ty : type) (l : block) (ofs : ptrofs)
        (id : ident) (co : composite) (att : attr) (delta : Int) (bf : bitfield) :
        eval_expr ge e le m a (.Vptr l ofs) →
        typeof a = .Tunion id att →
        ge.genv_cenv.get? id = some co →
        union_field_offset ge.genv_cenv i co.co_members = Except.ok (delta, bf) →
        eval_lvalue ge e le m (.Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
end

/- `eval_exprlist ge e le m al tyl vl` evaluates a list of r-value
  expressions `al`, cast their values to the types given in `tyl`,
  and produces the list of cast values `vl`.  It is used to
  evaluate the arguments of function calls. -/

inductive eval_exprlist : List expr → List type → List val → Prop where
  | eval_Enil :
      eval_exprlist [] [] []
  | eval_Econs (a : expr) (bl : List expr) (ty : type) (tyl : List type)
      (v1 v2 : val) (vl : List val) :
      eval_expr ge e le m a v1 →
      sem_cast v1 (typeof a) ty m = some v2 →
      eval_exprlist bl tyl vl →
      eval_exprlist (a :: bl) (ty :: tyl) (v2 :: vl)

end EXPR

-- ** Transition semantics for statements and functions

/- Continuations -/

inductive cont : Type where
  | Kstop
  | Kseq (s2 : statement) (k : cont)               -- `Kseq s2 k` = after `s1` in `s1;s2`
  | Kloop1 (s1 s2 : statement) (k : cont)           -- `Kloop1 s1 s2 k` = after `s1` in `Sloop s1 s2`
  | Kloop2 (s1 s2 : statement) (k : cont)           -- `Kloop2 s1 s2 k` = after `s2` in `Sloop s1 s2`
  | Kswitch (k : cont)                              -- catches `break` statements arising out of `switch`
  | Kcall (optid : Option ident)                    -- where to store result
          (f : function)                            -- calling function
          (e : env)                                 -- local env of calling function
          (le : temp_env)                           -- temporary env of calling function
          (k : cont)

/- Pop continuation until a call or stop -/

def call_cont (k : cont) : cont :=
  match k with
  | .Kseq _s k => call_cont k
  | .Kloop1 _s1 _s2 k => call_cont k
  | .Kloop2 _s1 _s2 k => call_cont k
  | .Kswitch k => call_cont k
  | _ => k

def is_call_cont (k : cont) : Prop :=
  match k with
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

-- ** States

inductive state : Type where
  | State
      (f : function)
      (s : statement)
      (k : cont)
      (e : env)
      (le : temp_env)
      (m : mem)
  | Callstate
      (fd : fundef_type function)
      (args : List val)
      (k : cont)
      (m : mem)
  | Returnstate
      (res : val)
      (k : cont)
      (m : mem)

/- Find the statement and manufacture the continuation
  corresponding to a label -/

mutual
  def find_label (lbl : label) (s : statement) (k : cont) : Option (statement × cont) :=
    match s with
    | .Ssequence s1 s2 =>
        match find_label lbl s1 (.Kseq s2 k) with
        | some sk => some sk
        | none => find_label lbl s2 k
    | .Sifthenelse _a s1 s2 =>
        match find_label lbl s1 k with
        | some sk => some sk
        | none => find_label lbl s2 k
    | .Sloop s1 s2 =>
        match find_label lbl s1 (.Kloop1 s1 s2 k) with
        | some sk => some sk
        | none => find_label lbl s2 (.Kloop2 s1 s2 k)
    | .Sswitch _e sl =>
        find_label_ls lbl sl (.Kswitch k)
    | .Slabel lbl' s' =>
        if lbl = lbl' then some (s', k) else find_label lbl s' k
    | _ => none

  def find_label_ls (lbl : label) (sl : labeled_statements) (k : cont) : Option (statement × cont) :=
    match sl with
    | .LSnil => none
    | .LScons _ s sl' =>
        match find_label lbl s (.Kseq (seq_of_labeled_statement sl') k) with
        | some sk => some sk
        | none => find_label_ls lbl sl' k
end

/- Semantics for allocation of variables and binding of parameters at
  function entry.  Two semantics are supported: one where
  parameters are local variables, reside in memory, and can have their address
  taken; the other where parameters are temporary variables and do not reside
  in memory.  We parameterize the `step` transition relation over the
  parameter binding semantics, then instantiate it later to give the two
  semantics described above. -/

variable (function_entry : function → List val → mem → env → temp_env → mem → Prop)

/- Transition relation -/

inductive step : state → trace → state → Prop where
  | step_assign (f : function) (a1 a2 : expr) (k : cont) (e : env) (le : temp_env) (m : mem)
      (loc : block) (ofs : ptrofs) (bf : bitfield) (v2 v : val) (m' : mem) :
      eval_lvalue ge e le m a1 loc ofs bf →
      eval_expr ge e le m a2 v2 →
      sem_cast v2 (typeof a2) (typeof a1) m = some v →
      assign_loc ge.genv_cenv (typeof a1) m loc ofs bf v m' →
      step (.State f (.Sassign a1 a2) k e le m)
        E0 (.State f .Sskip k e le m')

  | step_set (f : function) (id : ident) (a : expr) (k : cont) (e : env) (le : temp_env)
      (m : mem) (v : val) :
      eval_expr ge e le m a v →
      step (.State f (.Sset id a) k e le m)
        E0 (.State f .Sskip k e (le.insert id v) m)

  | step_call (f : function) (optid : Option ident) (a : expr) (al : List expr) (k : cont)
      (e : env) (le : temp_env) (m : mem) (tyargs : List type) (tyres : type)
      (cconv : calling_convention) (vf : val) (vargs : List val) (fd : fundef_type function) :
      classify_fun (typeof a) = .fun_case_f tyargs tyres cconv →
      eval_expr ge e le m a vf →
      eval_exprlist ge e le m al tyargs vargs →
      Genv.find_funct ge.genv_genv vf = some fd →
      type_of_fundef fd = .Tfunction tyargs tyres cconv →
      step (.State f (.Scall optid a al) k e le m)
        E0 (.Callstate fd vargs (.Kcall optid f e le k) m)

  | step_builtin (f : function) (optid : Option ident) (ef : external_function)
      (tyargs : List type) (al : List expr) (k : cont) (e : env) (le : temp_env) (m : mem)
      (vargs : List val) (t : trace) (vres : val) (m' : mem) :
      eval_exprlist ge e le m al tyargs vargs →
      Events.external_call ef ge.genv_genv vargs m t vres m' →
      step (.State f (.Sbuiltin optid ef tyargs al) k e le m)
        t (.State f .Sskip k e (set_opttemp optid vres le) m')

  | step_seq (f : function) (s1 s2 : statement) (k : cont) (e : env) (le : temp_env) (m : mem) :
      step (.State f (.Ssequence s1 s2) k e le m)
        E0 (.State f s1 (.Kseq s2 k) e le m)
  | step_skip_seq (f : function) (s : statement) (k : cont) (e : env) (le : temp_env) (m : mem) :
      step (.State f .Sskip (.Kseq s k) e le m)
        E0 (.State f s k e le m)
  | step_continue_seq (f : function) (s : statement) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step (.State f .Scontinue (.Kseq s k) e le m)
        E0 (.State f .Scontinue k e le m)
  | step_break_seq (f : function) (s : statement) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step (.State f .Sbreak (.Kseq s k) e le m)
        E0 (.State f .Sbreak k e le m)

  | step_ifthenelse (f : function) (a : expr) (s1 s2 : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) (v1 : val) (b : Bool) :
      eval_expr ge e le m a v1 →
      bool_val v1 (typeof a) m = some b →
      step (.State f (.Sifthenelse a s1 s2) k e le m)
        E0 (.State f (if b then s1 else s2) k e le m)

  | step_loop (f : function) (s1 s2 : statement) (k : cont) (e : env) (le : temp_env) (m : mem) :
      step (.State f (.Sloop s1 s2) k e le m)
        E0 (.State f s1 (.Kloop1 s1 s2 k) e le m)
  | step_skip_or_continue_loop1 (f : function) (s1 s2 : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) (x : statement) :
      x = .Sskip ∨ x = .Scontinue →
      step (.State f x (.Kloop1 s1 s2 k) e le m)
        E0 (.State f s2 (.Kloop2 s1 s2 k) e le m)
  | step_break_loop1 (f : function) (s1 s2 : statement) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step (.State f .Sbreak (.Kloop1 s1 s2 k) e le m)
        E0 (.State f .Sskip k e le m)
  | step_skip_loop2 (f : function) (s1 s2 : statement) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step (.State f .Sskip (.Kloop2 s1 s2 k) e le m)
        E0 (.State f (.Sloop s1 s2) k e le m)
  | step_break_loop2 (f : function) (s1 s2 : statement) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step (.State f .Sbreak (.Kloop2 s1 s2 k) e le m)
        E0 (.State f .Sskip k e le m)

  | step_return_0 (f : function) (k : cont) (e : env) (le : temp_env) (m m' : mem) :
      Memory.free_list m (blocks_of_env ge e) = some m' →
      step (.State f (.Sreturn none) k e le m)
        E0 (.Returnstate .Vundef (call_cont k) m')
  | step_return_1 (f : function) (a : expr) (k : cont) (e : env) (le : temp_env) (m : mem)
      (v v' : val) (m' : mem) :
      eval_expr ge e le m a v →
      sem_cast v (typeof a) f.fn_return m = some v' →
      Memory.free_list m (blocks_of_env ge e) = some m' →
      step (.State f (.Sreturn (some a)) k e le m)
        E0 (.Returnstate v' (call_cont k) m')
  | step_skip_call (f : function) (k : cont) (e : env) (le : temp_env) (m m' : mem) :
      is_call_cont k →
      Memory.free_list m (blocks_of_env ge e) = some m' →
      step (.State f .Sskip k e le m)
        E0 (.Returnstate .Vundef k m')

  | step_switch (f : function) (a : expr) (sl : labeled_statements) (k : cont) (e : env)
      (le : temp_env) (m : mem) (v : val) (n : Nat) :
      eval_expr ge e le m a v →
      sem_switch_arg v (typeof a) = some n →
      step (.State f (.Sswitch a sl) k e le m)
        E0 (.State f (seq_of_labeled_statement (select_switch (n : Int) sl)) (.Kswitch k) e le m)
  | step_skip_break_switch (f : function) (x : statement) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      x = .Sskip ∨ x = .Sbreak →
      step (.State f x (.Kswitch k) e le m)
        E0 (.State f .Sskip k e le m)
  | step_continue_switch (f : function) (k : cont) (e : env) (le : temp_env) (m : mem) :
      step (.State f .Scontinue (.Kswitch k) e le m)
        E0 (.State f .Scontinue k e le m)

  | step_label (f : function) (lbl : label) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step (.State f (.Slabel lbl s) k e le m)
        E0 (.State f s k e le m)

  | step_goto (f : function) (lbl : label) (k : cont) (e : env) (le : temp_env) (m : mem)
      (s' : statement) (k' : cont) :
      find_label lbl f.fn_body (call_cont k) = some (s', k') →
      step (.State f (.Sgoto lbl) k e le m)
        E0 (.State f s' k' e le m)

  | step_internal_function (f : function) (vargs : List val) (k : cont) (m : mem) (e : env)
      (le : temp_env) (m1 : mem) :
      function_entry f vargs m e le m1 →
      step (.Callstate (.Internal f) vargs k m)
        E0 (.State f f.fn_body k e le m1)

  | step_external_function (ef : external_function) (targs : List type) (tres : type)
      (cconv : calling_convention) (vargs : List val) (k : cont) (m : mem) (vres : val)
      (t : trace) (m' : mem) :
      Events.external_call ef ge.genv_genv vargs m t vres m' →
      step (.Callstate (.External ef targs tres cconv) vargs k m)
        t (.Returnstate vres k m')

  | step_returnstate (v : val) (optid : Option ident) (f : function) (e : env) (le : temp_env)
      (k : cont) (m : mem) :
      step (.Returnstate v (.Kcall optid f e le k) m)
        E0 (.State f .Sskip k e (set_opttemp optid v le) m)

end SEMANTICS

-- ** Whole-program semantics

/- Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a `Callstate`
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. -/

inductive initial_state (p : program_type function) : state → Prop where
  | initial_state_intro (b : block) (f : fundef_type function) (m0 : mem) :
      Genv.init_mem (program_of_program function p) = some m0 →
      Genv.find_symbol (Genv.globalenv (program_of_program function p)) p.prog_main = some b →
      Genv.find_funct_ptr (Genv.globalenv (program_of_program function p)) b = some f →
      type_of_fundef f = .Tfunction [] type_int32s cc_default →
      initial_state p (.Callstate f [] .Kstop m0)

/- A final state is a `Returnstate` with an empty continuation. -/

inductive final_state : state → CompCert.Int → Prop where
  | final_state_intro (r : CompCert.Int) (m : mem) :
      final_state (.Returnstate (.Vint r) .Kstop m) r

/- The two semantics for function parameters.  First, parameters as local variables. -/

inductive function_entry1 (ge : genv) (f : function) (vargs : List val) (m : mem)
    (e : env) (le : temp_env) (m' : mem) : Prop where
  | function_entry1_intro (m1 : mem) :
      (var_names f.fn_params ++ var_names f.fn_vars).Nodup →
      alloc_variables ge empty_env m (f.fn_params ++ f.fn_vars) e m1 →
      bind_parameters ge e m1 f.fn_params vargs m' →
      le = create_undef_temps f.fn_temps →
      function_entry1 ge f vargs m e le m'

def step1 (ge : genv) : state → trace → state → Prop :=
  step ge (function_entry1 ge)

/- Second, parameters as temporaries. -/

inductive function_entry2 (ge : genv) (f : function) (vargs : List val) (m : mem)
    (e : env) (le : temp_env) (m' : mem) : Prop where
  | function_entry2_intro :
      (var_names f.fn_vars).Nodup →
      (var_names f.fn_params).Nodup →
      (∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y) →
      alloc_variables ge empty_env m f.fn_vars e m' →
      bind_parameter_temps f.fn_params vargs (create_undef_temps f.fn_temps) = some le →
      function_entry2 ge f vargs m e le m'

def step2 (ge : genv) : state → trace → state → Prop :=
  step ge (function_entry2 ge)

/- Wrapping up these definitions in two small-step semantics. -/

def semantics1 (p : program_type function) : Smallstep.semantics (fundef_type function) type :=
  let ge := globalenv p
  { state := state
    genvtype := genv
    step := step1
    initial_state := initial_state p
    final_state := final_state
    globalenv := ge
    to_genv := genv.genv_genv }

def semantics2 (p : program_type function) : Smallstep.semantics (fundef_type function) type :=
  let ge := globalenv p
  { state := state
    genvtype := genv
    step := step2
    initial_state := initial_state p
    final_state := final_state
    globalenv := ge
    to_genv := genv.genv_genv }

/- This semantics is receptive to changes in events. -/

theorem semantics_receptive (p : program_type function) :
    Smallstep.receptive (semantics1 p) where
  sr_receptive := by
    intro s t1 s1 t2 hstep hmt
    have hassert : t1 = E0 → ∃ s2, Smallstep.Step (semantics1 p) s t2 s2 := by
      intro heq
      subst heq
      cases hmt with
      | match_traces_E0 => exact ⟨s1, hstep⟩
    cases hstep with
    | step_builtin f optid ef tyargs al k e le m vargs t vres m' heval hext =>
        obtain ⟨vres2, m2, hext2⟩ := (Events.external_call_spec ef).ec_receptive hext hmt
        exact ⟨_, .step_builtin f optid ef tyargs al k e le m vargs t2 vres2 m2 heval hext2⟩
    | step_external_function ef targs tres cconv vargs k m vres t m' hext =>
        obtain ⟨vres2, m2, hext2⟩ := (Events.external_call_spec ef).ec_receptive hext hmt
        exact ⟨_, .step_external_function ef targs tres cconv vargs k m vres2 t2 m2 hext2⟩
    | _ => exact hassert rfl
  sr_traces := by
    intro s t s' hstep
    cases hstep with
    | step_builtin f optid ef tyargs al k e le m vargs t vres m' heval hext =>
        exact (Events.external_call_spec ef).ec_trace_length hext
    | step_external_function ef targs tres cconv vargs k m vres t m' hext =>
        exact (Events.external_call_spec ef).ec_trace_length hext
    | _ => simp [E0]
