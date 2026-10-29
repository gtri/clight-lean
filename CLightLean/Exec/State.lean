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

import CLightLean.Exec.Expr

/-!
Functional location assignment and function-entry setup for the additive
executor.

The definitions in this file are executable mirrors of the corresponding
relations in `CLight.lean`.  They reuse the established `Memory` operations
and retain the existing provenance-preserving memory representation.  The
relational semantics remains authoritative.
-/

namespace CLightLean.Exec

variable [Archi]

/-- The pieces of local state produced by local-variable allocation. -/
structure LocalState where
  env : env
  memory : Memory.mem

/-- The pieces of local state needed to enter an internal `step2` function. -/
structure FunctionEntryState where
  env : env
  temps : temp_env
  memory : Memory.mem

/-- Decidable computation of the `assign_loc_copy` source/destination
alignment premise.  `alignof_blockcopy` is always one of 1, 2, 4, or 8, so
remainder zero is equivalent to the relation's divisibility condition. -/
def blockCopyAligned (cenv : composite_env) (ty : type) (ofs : ptrofs) : Bool :=
  if sizeof cenv ty > 0 then
    Ptrofs.unsigned ofs % alignof_blockcopy cenv ty == 0
  else
    true

/-- Decidable computation of the `assign_loc_copy` non-overlap premise. -/
def blockCopySeparated (cenv : composite_env) (srcBlock : block) (srcOfs : ptrofs)
    (dstBlock : block) (dstOfs : ptrofs) (ty : type) : Bool :=
  srcBlock != dstBlock || Ptrofs.unsigned srcOfs == Ptrofs.unsigned dstOfs
    || decide (Ptrofs.unsigned srcOfs + sizeof cenv ty ≤ Ptrofs.unsigned dstOfs)
    || decide (Ptrofs.unsigned dstOfs + sizeof cenv ty ≤ Ptrofs.unsigned srcOfs)

/-- Execute the bitfield branch of `assign_loc`.  The carrier load and store
are deliberately delegated to `Memory`, so pointer provenance is untouched. -/
def assignBitfield (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (sz : intsize) (sg : signedness) (pos width : Int) (v : val) :
    Except ExecError Memory.mem :=
  match ty, v with
  | .Tint carrierSz carrierSg _, .Vint n =>
      if _ : carrierSz = sz then
        if _ : 0 ≤ pos then
          if _ : 0 < width ∧ width ≤ bitsize_intsize sz then
            if _ : pos + width ≤ bitsize_carrier sz then
              if _ : carrierSg = (if width < bitsize_intsize sz then .Signed else sg) then
                match Memory.loadv (chunk_for_carrier sz) m (.Vptr b ofs) with
                | some (.Vint carrier) =>
                    match Memory.storev (chunk_for_carrier sz) m (.Vptr b ofs)
                        (.Vint (CompCert.Int.bitfield_insert (first_bit sz pos width) width carrier n)) with
                    | some m' => .ok m'
                    | none => .error .memoryFailure
                | some _ => .error .invalidLvalue
                | none => .error .memoryFailure
              else
                .error .invalidLvalue
            else
              .error .invalidLvalue
          else
            .error .invalidLvalue
        else
          .error .invalidLvalue
      else
        .error .invalidLvalue
  | .Tint _ _ _, _ => .error .invalidExpression
  | _, _ => .error .invalidLvalue

/-- Functional mirror of `assign_loc`.

All three relational branches are computed directly:
* scalar stores use `Memory.storev`;
* aggregate copies use `Memory.loadbytes` and `Memory.storebytes` after
  checking the relation's alignment and non-overlap premises; and
* bitfield stores perform the relation's carrier read-modify-write.
-/
def assignLoc (cenv : composite_env) (ty : type) (m : Memory.mem) (b : block)
    (ofs : ptrofs) (bf : bitfield) (v : val) : Except ExecError Memory.mem :=
  match bf with
  | .Full =>
      match access_mode ty with
      | .By_value chunk =>
          match Memory.storev chunk m (.Vptr b ofs) v with
          | some m' => .ok m'
          | none => .error .memoryFailure
      | .By_copy =>
          match v with
          | .Vptr srcBlock srcOfs =>
              if blockCopyAligned cenv ty srcOfs then
                if blockCopyAligned cenv ty ofs then
                  if blockCopySeparated cenv srcBlock srcOfs b ofs ty then
                    match Memory.loadbytes m srcBlock (Ptrofs.unsigned srcOfs) (sizeof cenv ty) with
                    | some bytes =>
                        match Memory.storebytes m b (Ptrofs.unsigned ofs) bytes with
                        | some m' => .ok m'
                        | none => .error .memoryFailure
                    | none => .error .memoryFailure
                  else
                    .error .invalidAssignment
                else
                  .error .invalidAssignment
              else
                .error .invalidAssignment
          | _ => .error .invalidExpression
      | .By_reference | .By_nothing => .error .invalidLvalue
  | .Bits sz sg pos width => assignBitfield ty m b ofs sz sg pos width v

/-- Functional mirror of `alloc_variables`.  Allocation itself cannot fail in
the current `Memory` API, but the `Except` result keeps this operation aligned
with the other setup functions and leaves room for a future finite-memory API.
Duplicate identifiers intentionally retain the relational behavior: the later
binding overwrites the earlier environment binding while both blocks remain
allocated. -/
def allocVariables (ge : genv) : env → Memory.mem → List (ident × type) →
    Except ExecError LocalState
  | e, m, [] => .ok { env := e, memory := m }
  | e, m, (id, ty) :: vars =>
      let (b, m1) := Memory.alloc m 0 (sizeof ge.genv_cenv ty)
      allocVariables ge (e.insert id (b, ty)) m1 vars

/-- Functional mirror of `bind_parameters`.  A missing or type-mismatched
environment binding and a length mismatch violate the relation's structural
premises, so they are reported as `malformedCall`; a location-store failure is
reported by `assignLoc` without manufacturing a successor memory. -/
def bindParameters (ge : genv) (e : env) : Memory.mem → List (ident × type) →
    List val → Except ExecError Memory.mem
  | m, [], [] => .ok m
  | m, (id, ty) :: params, v :: args =>
      match e.get? id with
      | some (b, storedTy) =>
          if _ : storedTy = ty then
            match assignLoc ge.genv_cenv ty m b Ptrofs.zero .Full v with
            | .ok m1 => bindParameters ge e m1 params args
            | .error err => .error err
          else
            .error .malformedCall
      | none => .error .malformedCall
  | _, _, _ => .error .malformedCall

/-- Executor spelling of the existing, authoritative computational temporary
initialization helper. -/
def createUndefTemps (temps : List (ident × type)) : temp_env :=
  create_undef_temps temps

/-- Checked executor view of `bind_parameter_temps`.  The existing helper is
already exactly executable; this wrapper merely gives arity failure the
executor's structured error shape. -/
def bindParameterTemps (formals : List (ident × type)) (args : List val)
    (temps : temp_env) : Except ExecError temp_env :=
  match bind_parameter_temps formals args temps with
  | some boundTemps => .ok boundTemps
  | none => .error .malformedCall

/-- Functional mirror of the parameter-as-temporaries `function_entry2`
discipline used by `step2`.  The three structural side conditions are checked
before allocation.  Argument binding is then delegated to the existing
`bind_parameter_temps` computation through `bindParameterTemps`. -/
def functionEntry2 (ge : genv) (f : function) (args : List val) (m : Memory.mem) :
    Except ExecError FunctionEntryState :=
  if _ : (var_names f.fn_vars).Nodup then
    if _ : (var_names f.fn_params).Nodup then
      if _ : ∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y then
        match allocVariables ge empty_env m f.fn_vars with
        | .error err => .error err
        | .ok locals =>
            match bindParameterTemps f.fn_params args (createUndefTemps f.fn_temps) with
            | .ok temps => .ok { env := locals.env, temps := temps, memory := locals.memory }
            | .error err => .error err
      else
        .error .malformedCall
    else
      .error .malformedCall
  else
    .error .malformedCall

end CLightLean.Exec
