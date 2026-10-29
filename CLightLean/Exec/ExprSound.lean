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
Initial correspondence results for the pure executor layer.

The relational definitions in `CLight.lean` remain authoritative.  This file
proves soundness for the cases whose functional computation is a direct mirror
of one relational constructor.  In particular, the variable evaluator accepts
a local binding only when its stored type agrees with the `Evar` annotation,
making its successful local case directly match `eval_Evar_local`.

The direct bitfield and field-location lemmas below retain all information in a
successful functional result, including the exact bitfield designation.  They
are the local building blocks for the mutually recursive evaluator theorem at
the end of this file.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Successful full, by-value dereference is a relational `deref_loc_value`. -/
theorem derefLoc_full_value_sound
    (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (chunk : memory_chunk) (v : val)
    (hmode : access_mode ty = .By_value chunk)
    (h : derefLoc ty m b ofs .Full = .ok v) :
    deref_loc ty m b ofs .Full v := by
  cases hload : Memory.loadv chunk m (.Vptr b ofs) with
  | none =>
      simp [derefLoc, hmode, hload] at h
  | some loaded =>
      simp [derefLoc, hmode, hload] at h
      subst v
      exact .deref_loc_value chunk loaded hmode hload

/-- Successful full, by-reference dereference is a relational pointer result. -/
theorem derefLoc_full_reference_sound
    (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (v : val)
    (hmode : access_mode ty = .By_reference)
    (h : derefLoc ty m b ofs .Full = .ok v) :
    deref_loc ty m b ofs .Full v := by
  simp [derefLoc, hmode] at h
  subst v
  exact .deref_loc_reference hmode

/-- Successful full, by-copy dereference is a relational pointer result. -/
theorem derefLoc_full_copy_sound
    (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (v : val)
    (hmode : access_mode ty = .By_copy)
    (h : derefLoc ty m b ofs .Full = .ok v) :
    deref_loc ty m b ofs .Full v := by
  simp [derefLoc, hmode] at h
  subst v
  exact .deref_loc_copy hmode

/-- A successful bitfield load supplies exactly the premises of the
    authoritative `load_bitfield` constructor. -/
theorem derefBitfield_sound
    (ty : type) (sz : intsize) (sg : signedness) (pos width : Int)
    (m : Memory.mem) (addr : val) (v : val)
    (h : derefBitfield ty sz sg pos width m addr = .ok v) :
    load_bitfield ty sz sg pos width m addr v := by
  cases ty with
  | Tvoid =>
      simp [derefBitfield] at h
  | Tint carrierSz carrierSg attr =>
      by_cases hsz : carrierSz = sz
      · by_cases h0 : 0 ≤ pos
        · by_cases h1 : 0 < width ∧ width ≤ bitsize_intsize sz
          · by_cases h2 : pos + width ≤ bitsize_carrier sz
            · by_cases h3 : carrierSg = (if width < bitsize_intsize sz then .Signed else sg)
              · cases hload : Memory.loadv (chunk_for_carrier sz) m addr with
                | none =>
                    simp [derefBitfield, hsz, h0, h1, h2, h3, hload] at h
                | some loaded =>
                    cases loaded with
                    | Vint c =>
                        have hv : v = .Vint (bitfield_extract sz sg pos width c) := by
                          simpa [derefBitfield, hsz, h0, h1, h2, h3, hload] using h.symm
                        subst v
                        simpa [hsz] using
                          (.load_bitfield_intro sz carrierSg attr sg pos width m addr c
                            h0 h1 h2 h3 hload)
                    | Vundef =>
                        simp [derefBitfield, hsz, h0, h1, h2, h3, hload] at h
                    | Vlong c =>
                        simp [derefBitfield, hsz, h0, h1, h2, h3, hload] at h
                    | Vfloat f =>
                        simp [derefBitfield, hsz, h0, h1, h2, h3, hload] at h
                    | Vsingle f =>
                        simp [derefBitfield, hsz, h0, h1, h2, h3, hload] at h
                    | Vptr b ofs =>
                        simp [derefBitfield, hsz, h0, h1, h2, h3, hload] at h
              · simp [derefBitfield, hsz, h0, h1, h2, h3] at h
            · simp [derefBitfield, hsz, h0, h1, h2] at h
          · simp [derefBitfield, hsz, h0, h1] at h
        · simp [derefBitfield, hsz, h0] at h
      · simp [derefBitfield, hsz] at h
  | Tlong s attr =>
      simp [derefBitfield] at h
  | Tfloat f attr =>
      simp [derefBitfield] at h
  | Tpointer t attr =>
      simp [derefBitfield] at h
  | Tarray t n attr =>
      simp [derefBitfield] at h
  | Tfunction params result cc =>
      simp [derefBitfield] at h
  | Tstruct id attr =>
      simp [derefBitfield] at h
  | Tunion id attr =>
      simp [derefBitfield] at h

/-- A successful functional bitfield dereference is the corresponding
    authoritative `deref_loc` derivation. -/
theorem derefLoc_bitfield_sound
    (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (sz : intsize) (sg : signedness) (pos width : Int) (v : val)
    (h : derefLoc ty m b ofs (.Bits sz sg pos width) = .ok v) :
    deref_loc ty m b ofs (.Bits sz sg pos width) v := by
  exact .deref_loc_bitfield sz sg pos width v
    (derefBitfield_sound ty sz sg pos width m (.Vptr b ofs) v h)

/-- Unified soundness for successful full and bitfield dereferences. -/
theorem derefLoc_sound
    (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (bf : bitfield) (v : val)
    (h : derefLoc ty m b ofs bf = .ok v) :
    deref_loc ty m b ofs bf v := by
  cases bf with
  | Full =>
      cases hmode : access_mode ty with
      | By_value chunk =>
          exact derefLoc_full_value_sound ty m b ofs chunk v hmode h
      | By_reference =>
          exact derefLoc_full_reference_sound ty m b ofs v hmode h
      | By_copy =>
          exact derefLoc_full_copy_sound ty m b ofs v hmode h
      | By_nothing =>
          simp [derefLoc, hmode] at h
  | Bits sz sg pos width =>
      exact derefLoc_bitfield_sound ty m b ofs sz sg pos width v h

/-- A successful local/global variable lookup is an authoritative lvalue. -/
theorem evalVarLvalue_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (id : ident) (ty : type) (loc : Lvalue)
    (h : evalVarLvalue ge e id ty = .ok loc) :
    eval_lvalue ge e le m (.Evar id ty) loc.block loc.offset loc.bitfield := by
  unfold evalVarLvalue at h
  cases hlookup : e.get? id with
  | none =>
      cases hglobal : Genv.find_symbol ge.genv_genv id with
      | none =>
          rw [hlookup, hglobal] at h
          simp at h
      | some globalBlock =>
          rw [hlookup, hglobal] at h
          cases h
          exact .eval_Evar_global id globalBlock ty hlookup hglobal
  | some binding =>
      cases binding with
      | mk localBlock storedTy =>
          rw [hlookup] at h
          by_cases hty : storedTy = ty
          · simp [hty] at h
            subst storedTy
            cases h
            exact .eval_Evar_local id localBlock ty hlookup
          · simp [hty] at h

/-- The evaluator's `Evar` lvalue case is sound without a separate type premise. -/
theorem evalLvalue_var_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (id : ident) (ty : type) (loc : Lvalue)
    (h : evalLvalue ge e le m (.Evar id ty) = .ok loc) :
    eval_lvalue ge e le m (.Evar id ty) loc.block loc.offset loc.bitfield := by
  exact evalVarLvalue_sound ge e le m id ty loc h

/-- Constants are successful only at their relationally prescribed value. -/
theorem evalExpr_const_int_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (i : CompCert.Int) (ty : type) (v : val)
    (h : evalExpr ge e le m (.Econst_int i ty) = .ok v) :
    eval_expr ge e le m (.Econst_int i ty) v := by
  simp [evalExpr] at h
  subst v
  exact .eval_Econst_int i ty

theorem evalExpr_const_float_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (f : CompCert.Float64) (ty : type) (v : val)
    (h : evalExpr ge e le m (.Econst_float f ty) = .ok v) :
    eval_expr ge e le m (.Econst_float f ty) v := by
  simp [evalExpr] at h
  subst v
  exact .eval_Econst_float f ty

theorem evalExpr_const_single_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (f : CompCert.Float32) (ty : type) (v : val)
    (h : evalExpr ge e le m (.Econst_single f ty) = .ok v) :
    eval_expr ge e le m (.Econst_single f ty) v := by
  simp [evalExpr] at h
  subst v
  exact .eval_Econst_single f ty

theorem evalExpr_const_long_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (i : CompCert.Int64) (ty : type) (v : val)
    (h : evalExpr ge e le m (.Econst_long i ty) = .ok v) :
    eval_expr ge e le m (.Econst_long i ty) v := by
  simp [evalExpr] at h
  subst v
  exact .eval_Econst_long i ty

theorem evalExpr_sizeof_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (ty1 ty : type) (v : val)
    (h : evalExpr ge e le m (.Esizeof ty1 ty) = .ok v) :
    eval_expr ge e le m (.Esizeof ty1 ty) v := by
  simp [evalExpr] at h
  subst v
  exact .eval_Esizeof ty1 ty

theorem evalExpr_alignof_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (ty1 ty : type) (v : val)
    (h : evalExpr ge e le m (.Ealignof ty1 ty) = .ok v) :
    eval_expr ge e le m (.Ealignof ty1 ty) v := by
  simp [evalExpr] at h
  subst v
  exact .eval_Ealignof ty1 ty

/-- A successful temporary lookup is the relational temporary-variable rule. -/
theorem evalExpr_tempvar_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (id : ident) (ty : type) (v : val)
    (h : evalExpr ge e le m (.Etempvar id ty) = .ok v) :
    eval_expr ge e le m (.Etempvar id ty) v := by
  unfold evalExpr at h
  cases hlookup : le.get? id with
  | none =>
      simp only [hlookup] at h
      simp at h
  | some stored =>
      simp only [hlookup] at h
      have hv : v = stored := by simpa using h.symm
      cases hv
      exact .eval_Etempvar id ty v hlookup

/-- The unary evaluator branch is sound once its operand has been related and
its functional result is fixed.  The operand result premise is intentionally
separate from the branch result: this is the shape needed by a later mutual
induction, without claiming that induction here. -/
theorem evalExpr_unop_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (op : unary_operation) (a : expr) (ty : type) (v1 v : val)
    (harg : eval_expr ge e le m a v1)
    (harg_eval : evalExpr ge e le m a = .ok v1)
    (h : evalExpr ge e le m (.Eunop op a ty) = .ok v) :
    eval_expr ge e le m (.Eunop op a ty) v := by
  simp only [evalExpr] at h
  rw [harg_eval] at h
  cases hop : sem_unary_operation op v1 (typeof a) m with
  | none =>
      simp only [hop] at h
      simp at h
  | some result =>
      simp only [hop] at h
      have hv : result = v := by simpa using h
      rw [← hv]
      exact .eval_Eunop op a ty v1 result harg hop

/-- The binary evaluator branch is sound from related, successfully evaluated
operands and the successful functional branch result. -/
theorem evalExpr_binop_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (op : binary_operation) (a1 a2 : expr) (ty : type) (v1 v2 v : val)
    (harg1 : eval_expr ge e le m a1 v1)
    (harg2 : eval_expr ge e le m a2 v2)
    (harg1_eval : evalExpr ge e le m a1 = .ok v1)
    (harg2_eval : evalExpr ge e le m a2 = .ok v2)
    (h : evalExpr ge e le m (.Ebinop op a1 a2 ty) = .ok v) :
    eval_expr ge e le m (.Ebinop op a1 a2 ty) v := by
  simp only [evalExpr] at h
  rw [harg1_eval, harg2_eval] at h
  cases hop : sem_binary_operation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m with
  | none =>
      simp only [hop] at h
      simp at h
  | some result =>
      simp only [hop] at h
      have hv : result = v := by simpa using h
      rw [← hv]
      exact .eval_Ebinop op a1 a2 ty v1 v2 result harg1 harg2 hop

/-- The cast evaluator branch is sound from a related, successfully evaluated
operand and the successful functional branch result. -/
theorem evalExpr_cast_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (a : expr) (ty : type) (v1 v : val)
    (harg : eval_expr ge e le m a v1)
    (harg_eval : evalExpr ge e le m a = .ok v1)
    (h : evalExpr ge e le m (.Ecast a ty) = .ok v) :
    eval_expr ge e le m (.Ecast a ty) v := by
  simp only [evalExpr] at h
  rw [harg_eval] at h
  cases hop : sem_cast v1 (typeof a) ty m with
  | none =>
      simp only [hop] at h
      simp at h
  | some result =>
      simp only [hop] at h
      have hv : result = v := by simpa using h
      rw [← hv]
      exact .eval_Ecast a ty v1 result harg hop

 /-- A successful dereference is sound from a related pointer operand and the
 functional result of the full dereference. -/
 theorem evalExpr_deref_sound
     (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
     (a : expr) (ty : type) (b : block) (ofs : ptrofs) (v : val)
     (harg : eval_expr ge e le m a (.Vptr b ofs))
     (harg_eval : evalExpr ge e le m a = .ok (.Vptr b ofs))
     (h : evalExpr ge e le m (.Ederef a ty) = .ok v) :
     eval_expr ge e le m (.Ederef a ty) v := by
   simp only [evalExpr] at h
   rw [harg_eval] at h
   cases hmode : access_mode ty with
   | By_value chunk =>
       exact .eval_Elvalue (.Ederef a ty) b ofs .Full v
         (eval_lvalue.eval_Ederef a ty b ofs harg)
         (derefLoc_full_value_sound ty m b ofs chunk v hmode h)
   | By_reference =>
       exact .eval_Elvalue (.Ederef a ty) b ofs .Full v
         (eval_lvalue.eval_Ederef a ty b ofs harg)
         (derefLoc_full_reference_sound ty m b ofs v hmode h)
   | By_copy =>
       exact .eval_Elvalue (.Ederef a ty) b ofs .Full v
         (eval_lvalue.eval_Ederef a ty b ofs harg)
         (derefLoc_full_copy_sound ty m b ofs v hmode h)
   | By_nothing =>
       simp [derefLoc, hmode] at h

 /-- A successful dereference lvalue is sound from a related pointer operand. -/
theorem evalLvalue_deref_sound
     (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
     (a : expr) (ty : type) (b : block) (ofs : ptrofs)
     (harg : eval_expr ge e le m a (.Vptr b ofs))
     (harg_eval : evalExpr ge e le m a = .ok (.Vptr b ofs))
      (h : evalLvalue ge e le m (.Ederef a ty) =
        .ok { block := b, offset := ofs, bitfield := .Full }) :
      eval_lvalue ge e le m (.Ederef a ty) b ofs .Full := by
    simp only [evalLvalue] at h
    rw [harg_eval] at h
    cases h
    exact eval_lvalue.eval_Ederef a ty b ofs harg

 /-- A successful address-of evaluation is sound from its authoritative
  lvalue result and the matching functional lvalue result. -/
 theorem evalExpr_addrof_sound
     (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
     (a : expr) (ty : type) (b : block) (ofs : ptrofs)
     (harg : eval_lvalue ge e le m a b ofs .Full)
     (harg_eval : evalLvalue ge e le m a =
       .ok { block := b, offset := ofs, bitfield := .Full })
     (h : evalExpr ge e le m (.Eaddrof a ty) = .ok (.Vptr b ofs)) :
     eval_expr ge e le m (.Eaddrof a ty) (.Vptr b ofs) := by
    simp only [evalExpr] at h
    rw [harg_eval] at h
    cases h
    exact .eval_Eaddrof a ty b ofs harg

   /-- A successful field lvalue evaluation is sound from the related base
       expression and its matching functional result.  Its conclusion retains
       the exact resolved bitfield designation. -/
   theorem evalLvalue_field_sound
       (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
       (a : expr) (field : ident) (ty : type) (base : val) (loc : Lvalue)
       (harg : eval_expr ge e le m a base)
       (harg_eval : evalExpr ge e le m a = .ok base)
       (h : evalLvalue ge e le m (.Efield a field ty) = .ok loc) :
       eval_lvalue ge e le m (.Efield a field ty) loc.block loc.offset loc.bitfield := by
    simp only [evalLvalue] at h
    rw [harg_eval] at h
    cases base with
    | Vundef =>
        simp [evalFieldLvalue] at h
    | Vint i =>
        simp [evalFieldLvalue] at h
    | Vlong i =>
        simp [evalFieldLvalue] at h
    | Vfloat f =>
        simp [evalFieldLvalue] at h
    | Vsingle f =>
        simp [evalFieldLvalue] at h
    | Vptr b ofs =>
        cases hty : typeof a with
        | Tvoid =>
            simp [evalFieldLvalue, hty] at h
        | Tint sz sg att =>
            simp [evalFieldLvalue, hty] at h
        | Tlong sg att =>
            simp [evalFieldLvalue, hty] at h
        | Tfloat sz att =>
            simp [evalFieldLvalue, hty] at h
        | Tpointer elt att =>
            simp [evalFieldLvalue, hty] at h
        | Tarray elt n att =>
            simp [evalFieldLvalue, hty] at h
        | Tfunction args result cc =>
            simp [evalFieldLvalue, hty] at h
        | Tstruct id att =>
            cases hco : ge.genv_cenv.get? id with
            | none =>
                simp only [evalFieldLvalue, hty, hco] at h
                cases h
            | some co =>
                cases hoff : field_offset ge.genv_cenv field co.co_members with
                | error err =>
                    simp only [evalFieldLvalue, hty, hco, hoff] at h
                    cases h
                | ok result =>
                    cases result with
                    | mk delta bf =>
                        simp only [evalFieldLvalue, hty] at h
                        simp only [hco, hoff] at h
                        cases h
                        exact .eval_Efield_struct a field ty b ofs id co att delta bf
                          harg hty hco hoff
        | Tunion id att =>
            cases hco : ge.genv_cenv.get? id with
            | none =>
                simp only [evalFieldLvalue, hty, hco] at h
                cases h
            | some co =>
                cases hoff : union_field_offset ge.genv_cenv field co.co_members with
                | error err =>
                    simp only [evalFieldLvalue, hty, hco, hoff] at h
                    cases h
                | ok result =>
                    cases result with
                    | mk delta bf =>
                        simp only [evalFieldLvalue, hty] at h
                        simp only [hco, hoff] at h
                        cases h
                        exact .eval_Efield_union a field ty b ofs id co att delta bf
                          harg hty hco hoff

/- Mutual proof declarations must be `def` in Lean's `mutual` command.  The
   public theorem wrappers below retain the correspondence surface names. -/
set_option linter.defProp false in
mutual
  def evalExpr_sound_go
      (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
      (a : expr) (v : val)
      (h : evalExpr ge e le m a = .ok v) :
      eval_expr ge e le m a v := by
    cases a with
    | Econst_int i ty =>
        exact evalExpr_const_int_sound ge e le m i ty v h
    | Econst_float f ty =>
        exact evalExpr_const_float_sound ge e le m f ty v h
    | Econst_single f ty =>
        exact evalExpr_const_single_sound ge e le m f ty v h
    | Econst_long i ty =>
        exact evalExpr_const_long_sound ge e le m i ty v h
    | Evar id ty =>
        simp only [evalExpr] at h
        cases hloc : evalVarLvalue ge e id ty with
        | error err =>
            simp [hloc] at h
        | ok loc =>
            rw [hloc] at h
            exact .eval_Elvalue (.Evar id ty) loc.block loc.offset loc.bitfield v
              (evalVarLvalue_sound ge e le m id ty loc hloc)
              (derefLoc_sound ty m loc.block loc.offset loc.bitfield v h)
    | Etempvar id ty =>
        exact evalExpr_tempvar_sound ge e le m id ty v h
    | Ederef a ty =>
        cases harg_eval : evalExpr ge e le m a with
        | error err =>
            simp [evalExpr, harg_eval] at h
        | ok arg =>
            cases arg with
            | Vptr b ofs =>
                exact evalExpr_deref_sound ge e le m a ty b ofs v
                  (evalExpr_sound_go ge e le m a (.Vptr b ofs) harg_eval) harg_eval h
            | Vundef => simp [evalExpr, harg_eval] at h
            | Vint i => simp [evalExpr, harg_eval] at h
            | Vlong i => simp [evalExpr, harg_eval] at h
            | Vfloat f => simp [evalExpr, harg_eval] at h
            | Vsingle f => simp [evalExpr, harg_eval] at h
    | Eaddrof a ty =>
        cases hloc : evalLvalue ge e le m a with
        | error err =>
            simp [evalExpr, hloc] at h
        | ok loc =>
            cases loc with
            | mk b ofs bf =>
                cases bf with
                | Full =>
                    have hptr : v = .Vptr b ofs := by
                      simpa [evalExpr, hloc] using h.symm
                    subst v
                    exact .eval_Eaddrof a ty b ofs
                      (evalLvalue_sound_go ge e le m a b ofs .Full hloc)
                | Bits sz sg pos width =>
                    simp [evalExpr, hloc] at h
    | Eunop op a ty =>
        cases harg_eval : evalExpr ge e le m a with
        | error err =>
            simp [evalExpr, harg_eval] at h
        | ok v1 =>
            exact evalExpr_unop_sound ge e le m op a ty v1 v
              (evalExpr_sound_go ge e le m a v1 harg_eval) harg_eval h
    | Ebinop op a1 a2 ty =>
        cases harg1_eval : evalExpr ge e le m a1 with
        | error err =>
            simp [evalExpr, harg1_eval] at h
        | ok v1 =>
            cases harg2_eval : evalExpr ge e le m a2 with
            | error err =>
                simp [evalExpr, harg1_eval, harg2_eval] at h
            | ok v2 =>
                exact evalExpr_binop_sound ge e le m op a1 a2 ty v1 v2 v
                  (evalExpr_sound_go ge e le m a1 v1 harg1_eval)
                  (evalExpr_sound_go ge e le m a2 v2 harg2_eval)
                  harg1_eval harg2_eval h
    | Ecast a ty =>
        cases harg_eval : evalExpr ge e le m a with
        | error err =>
            simp [evalExpr, harg_eval] at h
        | ok v1 =>
            exact evalExpr_cast_sound ge e le m a ty v1 v
              (evalExpr_sound_go ge e le m a v1 harg_eval) harg_eval h
    | Efield a field ty =>
        cases harg_eval : evalExpr ge e le m a with
        | error err =>
            simp [evalExpr, harg_eval] at h
        | ok base =>
            cases hloc : evalFieldLvalue ge (typeof a) base field with
            | error err =>
                simp [evalExpr, harg_eval, hloc] at h
            | ok loc =>
                have hlvalue : evalLvalue ge e le m (.Efield a field ty) = .ok loc := by
                  simp [evalLvalue, harg_eval, hloc]
                have hfield : eval_lvalue ge e le m (.Efield a field ty)
                    loc.block loc.offset loc.bitfield :=
                  evalLvalue_field_sound ge e le m a field ty base loc
                    (evalExpr_sound_go ge e le m a base harg_eval) harg_eval hlvalue
                have hderef : derefLoc ty m loc.block loc.offset loc.bitfield = .ok v := by
                  simpa [evalExpr, harg_eval, hloc] using h
                exact .eval_Elvalue (.Efield a field ty) loc.block loc.offset loc.bitfield v
                  hfield (derefLoc_sound ty m loc.block loc.offset loc.bitfield v hderef)
    | Esizeof ty1 ty =>
        exact evalExpr_sizeof_sound ge e le m ty1 ty v h
    | Ealignof ty1 ty =>
        exact evalExpr_alignof_sound ge e le m ty1 ty v h

  /-- Successful lvalue evaluation is sound for the authoritative Clight
      lvalue relation, retaining the exact bitfield designation. -/
  def evalLvalue_sound_go
      (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
      (a : expr) (b : block) (ofs : ptrofs) (bf : bitfield)
      (h : evalLvalue ge e le m a = .ok { block := b, offset := ofs, bitfield := bf }) :
      eval_lvalue ge e le m a b ofs bf := by
    cases a with
    | Evar id ty =>
        exact evalLvalue_var_sound ge e le m id ty { block := b, offset := ofs, bitfield := bf } h
    | Ederef a ty =>
        cases harg_eval : evalExpr ge e le m a with
        | error err =>
            simp [evalLvalue, harg_eval] at h
        | ok arg =>
            cases arg with
            | Vptr bPtr ofsPtr =>
                have hloc : ({ block := b, offset := ofs, bitfield := bf } : Lvalue) =
                    ({ block := bPtr, offset := ofsPtr, bitfield := .Full } : Lvalue) := by
                  simpa [evalLvalue, harg_eval] using h.symm
                have hresult : evalLvalue ge e le m (.Ederef a ty) =
                    .ok ({ block := bPtr, offset := ofsPtr, bitfield := .Full } : Lvalue) := by
                  rw [← hloc]
                  exact h
                have hb : b = bPtr := congrArg Lvalue.block hloc
                have hofs : ofs = ofsPtr := congrArg Lvalue.offset hloc
                have hbf : bf = .Full := congrArg Lvalue.bitfield hloc
                subst b
                subst ofs
                subst bf
                exact evalLvalue_deref_sound ge e le m a ty bPtr ofsPtr
                  (evalExpr_sound_go ge e le m a (.Vptr bPtr ofsPtr) harg_eval) harg_eval hresult
            | Vundef => simp [evalLvalue, harg_eval] at h
            | Vint i => simp [evalLvalue, harg_eval] at h
            | Vlong i => simp [evalLvalue, harg_eval] at h
            | Vfloat f => simp [evalLvalue, harg_eval] at h
            | Vsingle f => simp [evalLvalue, harg_eval] at h
    | Efield a field ty =>
        cases harg_eval : evalExpr ge e le m a with
        | error err =>
            simp [evalLvalue, harg_eval] at h
        | ok base =>
            exact evalLvalue_field_sound ge e le m a field ty base
              { block := b, offset := ofs, bitfield := bf }
              (evalExpr_sound_go ge e le m a base harg_eval) harg_eval h
    | Econst_int i ty => simp [evalLvalue] at h
    | Econst_float f ty => simp [evalLvalue] at h
    | Econst_single f ty => simp [evalLvalue] at h
    | Econst_long i ty => simp [evalLvalue] at h
    | Etempvar id ty => simp [evalLvalue] at h
    | Eaddrof a ty => simp [evalLvalue] at h
    | Eunop op a ty => simp [evalLvalue] at h
    | Ebinop op a1 a2 ty => simp [evalLvalue] at h
    | Ecast a ty => simp [evalLvalue] at h
    | Esizeof ty1 ty => simp [evalLvalue] at h
    | Ealignof ty1 ty => simp [evalLvalue] at h
end

/-- Successful expression evaluation is sound for the authoritative Clight
    relation. -/
theorem evalExpr_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (a : expr) (v : val)
    (h : evalExpr ge e le m a = .ok v) :
    eval_expr ge e le m a v :=
  evalExpr_sound_go ge e le m a v h

/-- Successful lvalue evaluation is sound for the authoritative Clight lvalue
    relation, retaining the exact resolved bitfield designation. -/
theorem evalLvalue_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (a : expr) (loc : Lvalue)
    (h : evalLvalue ge e le m a = .ok loc) :
    eval_lvalue ge e le m a loc.block loc.offset loc.bitfield :=
  evalLvalue_sound_go ge e le m a loc.block loc.offset loc.bitfield h

/-- Successful expression-list evaluation is sound for the authoritative
    argument-list relation. -/
theorem evalExprList_sound
    (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (al : List expr) (tyl : List type) (vl : List val)
    (h : evalExprList ge e le m al tyl = .ok vl) :
    eval_exprlist ge e le m al tyl vl := by
  induction al generalizing tyl vl with
  | nil =>
      cases tyl with
      | nil =>
          simp [evalExprList] at h
          cases h
          exact .eval_Enil
      | cons ty tyl =>
          simp [evalExprList] at h
  | cons a al ih =>
      cases tyl with
      | nil =>
          simp [evalExprList] at h
      | cons ty tyl =>
          cases harg_eval : evalExpr ge e le m a with
          | error err =>
              simp [evalExprList, harg_eval] at h
          | ok v1 =>
              cases hcast : sem_cast v1 (typeof a) ty m with
              | none =>
                  simp [evalExprList, harg_eval, hcast] at h
              | some v2 =>
                  cases htail_eval : evalExprList ge e le m al tyl with
                  | error err =>
                      simp [evalExprList, harg_eval, hcast, htail_eval] at h
                  | ok vl' =>
                      have hvalues : vl = v2 :: vl' := by
                        simpa [evalExprList, harg_eval, hcast, htail_eval] using h.symm
                      subst vl
                      exact .eval_Econs a al ty tyl v1 v2 vl'
                        (evalExpr_sound ge e le m a v1 harg_eval) hcast
                        (ih tyl vl' htail_eval)

   /-- The empty expression list computes to, and is related as, the empty
  argument-value list. -/
  theorem evalExprList_nil_sound
      (ge : genv) (e : env) (le : temp_env) (m : Memory.mem) :
      evalExprList ge e le m [] [] = .ok [] ∧
        eval_exprlist ge e le m [] [] [] := by
    exact ⟨rfl, .eval_Enil⟩

  /-- A successful nonempty expression-list computation is relationally sound
  when its evaluated head and recursively evaluated tail already have their
  respective relational derivations.  This is deliberately a compositional
  rule, rather than an attempted mutual induction over `evalExpr`. -/
  theorem evalExprList_cons_sound
      (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
      (a : expr) (al : List expr) (ty : type) (tyl : List type)
      (v1 v2 : val) (vl : List val)
      (harg : eval_expr ge e le m a v1)
      (harg_eval : evalExpr ge e le m a = .ok v1)
      (htail : eval_exprlist ge e le m al tyl vl)
      (htail_eval : evalExprList ge e le m al tyl = .ok vl)
      (h : evalExprList ge e le m (a :: al) (ty :: tyl) = .ok (v2 :: vl)) :
      eval_exprlist ge e le m (a :: al) (ty :: tyl) (v2 :: vl) := by
    unfold evalExprList at h
    rw [harg_eval] at h
    cases hcast : sem_cast v1 (typeof a) ty m with
    | none =>
        simp [hcast] at h
    | some castValue =>
        simp only [hcast, htail_eval] at h
        cases h
        exact .eval_Econs a al ty tyl v1 v2 vl harg hcast htail

  end CLightLean.Exec
