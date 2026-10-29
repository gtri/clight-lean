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

import CLightLean.Exec.Types

/-!
Functional expression, lvalue, and location-dereference evaluation for the
additive executor.

These functions structurally mirror `CLight.eval_expr`, `CLight.eval_lvalue`,
and `CLight.deref_loc`, while delegating value operations, memory access, and
layout calculations to the existing executable semantic primitives.  The
authoritative relations remain unchanged in `CLight.lean`.

Correspondence proofs are intentionally deferred.  In particular, a useful
mutual soundness proof should cover the recursive evaluators and the bitfield
side conditions together; it is kept out of this narrowly functional unit
rather than introducing incomplete proof scaffolding.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A resolved Clight lvalue location, including its possible bitfield view. -/
structure Lvalue where
  block : block
  offset : ptrofs
  bitfield : bitfield

/-- Resolve a variable expression using the same local-before-global order as
`eval_lvalue`.  A present local binding must have the expression's annotated
type; only an absent local binding falls through to `Genv`. -/
def evalVarLvalue (ge : genv) (e : env) (id : ident) (ty : type) : Except ExecError Lvalue :=
  match e.get? id with
  | some (b, storedTy) =>
      if storedTy = ty then
        .ok { block := b, offset := Ptrofs.zero, bitfield := .Full }
      else
        .error .invalidLvalue
  | none =>
      match Genv.find_symbol ge.genv_genv id with
      | some b => .ok { block := b, offset := Ptrofs.zero, bitfield := .Full }
      | none => .error .invalidLvalue

/-- Resolve a struct or union member after its base expression has evaluated to
a pointer.  `field_offset` and `union_field_offset` remain the sole source of
composite-layout behavior. -/
def evalFieldLvalue (ge : genv) (baseTy : type) (base : val) (field : ident) :
    Except ExecError Lvalue :=
  match base with
  | .Vptr b ofs =>
      match baseTy with
      | .Tstruct id _ =>
          match ge.genv_cenv.get? id with
          | none => .error .invalidLvalue
          | some co =>
              match field_offset ge.genv_cenv field co.co_members with
              | .ok (delta, bf) =>
                  .ok { block := b, offset := Ptrofs.add ofs (Ptrofs.repr delta), bitfield := bf }
              | .error _ => .error .invalidLvalue
      | .Tunion id _ =>
          match ge.genv_cenv.get? id with
          | none => .error .invalidLvalue
          | some co =>
              match union_field_offset ge.genv_cenv field co.co_members with
              | .ok (delta, bf) =>
                  .ok { block := b, offset := Ptrofs.add ofs (Ptrofs.repr delta), bitfield := bf }
              | .error _ => .error .invalidLvalue
      | _ => .error .invalidLvalue
  | _ => .error .invalidLvalue

/-- Execute the computational content of the relational bitfield load rule.
Malformed bitfield designators or a mismatched carrier type are invalid
expressions; a failed carrier-memory load is a memory failure. -/
def derefBitfield (ty : type) (sz : intsize) (sg : signedness) (pos width : Int)
    (m : Memory.mem) (addr : val) : Except ExecError val :=
  match ty with
  | .Tint carrierSz carrierSigned _ =>
      if carrierSz = sz then
        if _ : 0 ≤ pos then
          if _ : 0 < width ∧ width ≤ bitsize_intsize sz then
            if _ : pos + width ≤ bitsize_carrier sz then
              if _ : carrierSigned = (if width < bitsize_intsize sz then .Signed else sg) then
                match Memory.loadv (chunk_for_carrier sz) m addr with
                | some (.Vint carrier) => .ok (.Vint (bitfield_extract sz sg pos width carrier))
                | some _ => .error .invalidExpression
                | none => .error .memoryFailure
              else
                .error .invalidExpression
            else
              .error .invalidExpression
          else
            .error .invalidExpression
        else
          .error .invalidExpression
      else
        .error .invalidExpression
  | _ => .error .invalidExpression

/-- Functional mirror of `deref_loc`. -/
def derefLoc (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs) (bf : bitfield) :
    Except ExecError val :=
  match bf with
  | .Full =>
      match access_mode ty with
      | .By_value chunk =>
          match Memory.loadv chunk m (.Vptr b ofs) with
          | some v => .ok v
          | none => .error .memoryFailure
      | .By_reference | .By_copy => .ok (.Vptr b ofs)
      | .By_nothing => .error .invalidExpression
  | .Bits sz sg pos width => derefBitfield ty sz sg pos width m (.Vptr b ofs)

mutual
  /-- Functional mirror of `eval_expr` for every Clight expression constructor. -/
  def evalExpr (ge : genv) (e : env) (le : temp_env) (m : Memory.mem) : expr → Except ExecError val
    | .Econst_int i _ => .ok (.Vint i)
    | .Econst_float f _ => .ok (.Vfloat f)
    | .Econst_single f _ => .ok (.Vsingle f)
    | .Econst_long i _ => .ok (.Vlong i)
    | .Evar id ty =>
        match evalVarLvalue ge e id ty with
        | .error err => .error err
        | .ok loc => derefLoc ty m loc.block loc.offset loc.bitfield
    | .Etempvar id _ =>
        match le.get? id with
        | some v => .ok v
        | none => .error .invalidExpression
    | .Ederef a ty =>
        match evalExpr ge e le m a with
        | .error err => .error err
        | .ok (.Vptr b ofs) => derefLoc ty m b ofs .Full
        | .ok _ => .error .invalidLvalue
    | .Eaddrof a _ =>
        match evalLvalue ge e le m a with
        | .error err => .error err
        | .ok { bitfield := .Full, block, offset } => .ok (.Vptr block offset)
        | .ok _ => .error .invalidExpression
    | .Eunop op a _ =>
        match evalExpr ge e le m a with
        | .error err => .error err
        | .ok v =>
            match sem_unary_operation op v (typeof a) m with
            | some result => .ok result
            | none => .error .invalidExpression
    | .Ebinop op a1 a2 _ =>
        match evalExpr ge e le m a1 with
        | .error err => .error err
        | .ok v1 =>
            match evalExpr ge e le m a2 with
            | .error err => .error err
            | .ok v2 =>
                match sem_binary_operation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m with
                | some result => .ok result
                | none => .error .invalidExpression
    | .Ecast a ty =>
        match evalExpr ge e le m a with
        | .error err => .error err
        | .ok v =>
            match sem_cast v (typeof a) ty m with
            | some result => .ok result
            | none => .error .invalidExpression
    | .Efield a field ty =>
        match evalExpr ge e le m a with
        | .error err => .error err
        | .ok base =>
            match evalFieldLvalue ge (typeof a) base field with
            | .error err => .error err
            | .ok loc => derefLoc ty m loc.block loc.offset loc.bitfield
    | .Esizeof ty _ => .ok (Vptrofs (Ptrofs.repr (sizeof ge.genv_cenv ty)))
    | .Ealignof ty _ => .ok (Vptrofs (Ptrofs.repr (alignof ge.genv_cenv ty)))

  /-- Functional mirror of `eval_lvalue`.  The other expression constructors
  have no relational lvalue rule and therefore fail explicitly. -/
  def evalLvalue (ge : genv) (e : env) (le : temp_env) (m : Memory.mem) :
      expr → Except ExecError Lvalue
    | .Evar id ty => evalVarLvalue ge e id ty
    | .Ederef a _ =>
        match evalExpr ge e le m a with
        | .error err => .error err
        | .ok (.Vptr b ofs) => .ok { block := b, offset := ofs, bitfield := .Full }
        | .ok _ => .error .invalidLvalue
    | .Efield a field _ =>
        match evalExpr ge e le m a with
        | .error err => .error err
        | .ok base => evalFieldLvalue ge (typeof a) base field
    | _ => .error .invalidLvalue
end

/-- Functional mirror of `eval_exprlist`.  Arguments are evaluated in source
order, each resulting value is cast to its corresponding formal type, and the
cast values are returned in that same order.  Unequal expression/type lists
violate the call's structural arity requirement; an expression or cast failure
is reported without inventing an argument value. -/
def evalExprList (ge : genv) (e : env) (le : temp_env) (m : Memory.mem) :
    List expr → List type → Except ExecError (List val)
  | [], [] => .ok []
  | a :: al, ty :: tyl =>
      match evalExpr ge e le m a with
      | .error err => .error err
      | .ok v1 =>
          match sem_cast v1 (typeof a) ty m with
          | none => .error .invalidExpression
          | some v2 =>
              match evalExprList ge e le m al tyl with
              | .error err => .error err
              | .ok vl => .ok (v2 :: vl)
  | _, _ => .error .malformedCall

end CLightLean.Exec
