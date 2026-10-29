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

import CLightLean.AST
import CLightLean.Values
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats

/-!
# Associating semantics to built-in functions

Port of `common/Builtins0.v`. This module provides definitions and
mechanisms to associate semantics with names of built-in functions. It is
independent of the target architecture; each target provides its own
"platform builtins" (ported in `Builtins1.lean`, via a typeclass rather
than CompCert's per-architecture file selection).
-/

namespace Builtins0

variable [Archi]

def val_opt_has_rettype (ov : Option val) (t : xtype) : Prop :=
  match ov with
  | some v => Val.has_rettype v t
  | none => True

def val_opt_inject (j : meminj) (ov ov' : Option val) : Prop :=
  match ov, ov' with
  | none, _ => True
  | some v, some v' => Val.inject j v v'
  | some _, none => False

/-- The semantics of a built-in function is a partial function from lists
    of values to values. It must agree with the return type stated in the
    signature, and be compatible with value injections.

    Note: we skip `Builtins0.v`'s `valty`/`valxty`/`inj_num`/`proj_num`
    "numeric function" convenience layer and the `mkbuiltin_n*`
    constructors built on it. That layer exists in Coq purely to spare
    each individual builtin from re-proving well-typedness/injection by
    hand: it encodes e.g. `Xint16unsigned`'s refinement directly into a
    dependent subtype (`{n : int | n = Int.zero_ext 16 n}`) and lets
    `Program Definition`'s automatic obligation generation discharge the
    membership proof at each use site. Lean has no equivalent automatic
    discharge for that pattern, and replicating it by hand would cost as
    much proof work as just proving each builtin's well-typedness directly
    against `mkbuiltin_v*`/`mkbuiltin_v*p` below — which is what we do for
    `standard_builtin_sem`. The `builtin_sem` values produced are identical
    either way. -/
structure builtin_sem (tret : xtype) : Type where
  bs_sem : List val → Option val
  bs_well_typed : ∀ vl, val_opt_has_rettype (bs_sem vl) tret
  bs_inject : ∀ j vl vl', Val.inject_list j vl vl' → val_opt_inject j (bs_sem vl) (bs_sem vl')

/-- Allows applying a `builtin_sem` directly as a function, matching Coq's
    `bs_sem :> list val -> option val` coercion. -/
instance {tret : xtype} : CoeFun (builtin_sem tret) (fun _ => List val → Option val) :=
  ⟨builtin_sem.bs_sem⟩

/-- Builtin functions can be created from functions over values, such as
    those from `Val`. Proofs of well-typedness and compatibility with
    injections must be provided. The constructor functions have names
    `mkbuiltin_vNt` for a total function of `N` value arguments, or
    `mkbuiltin_vNp` for a partial function of `N` value arguments. -/
def mkbuiltin_v1t (tret : xtype) (f : val → val)
    (WT : ∀ v1, Val.has_rettype (f v1) tret)
    (INJ : ∀ j v1 v1', Val.inject j v1 v1' → Val.inject j (f v1) (f v1')) :
    builtin_sem tret where
  bs_sem := fun vl => match vl with | [v1] => some (f v1) | _ => none
  bs_well_typed := by
    intro vl
    match vl with
    | [] => trivial
    | [v1] => exact WT v1
    | _ :: _ :: _ => trivial
  bs_inject := by
    intro j vl vl' H
    cases H with
    | inject_list_nil => trivial
    | inject_list_cons v v' vl vl' H1 H2 =>
        cases H2 with
        | inject_list_nil => exact INJ j v v' H1
        | inject_list_cons _ _ _ _ _ _ => trivial

def mkbuiltin_v2t (tret : xtype) (f : val → val → val)
    (WT : ∀ v1 v2, Val.has_rettype (f v1 v2) tret)
    (INJ : ∀ j v1 v1' v2 v2', Val.inject j v1 v1' → Val.inject j v2 v2' →
      Val.inject j (f v1 v2) (f v1' v2')) :
    builtin_sem tret where
  bs_sem := fun vl => match vl with | [v1, v2] => some (f v1 v2) | _ => none
  bs_well_typed := by
    intro vl
    match vl with
    | [] => trivial
    | [_] => trivial
    | [v1, v2] => exact WT v1 v2
    | _ :: _ :: _ :: _ => trivial
  bs_inject := by
    intro j vl vl' H
    cases H with
    | inject_list_nil => trivial
    | inject_list_cons v v' vl vl' H1 H2 =>
        cases H2 with
        | inject_list_nil => trivial
        | inject_list_cons v2 v2' vl2 vl2' H1' H2' =>
            cases H2' with
            | inject_list_nil => exact INJ j v v' v2 v2' H1 H1'
            | inject_list_cons _ _ _ _ _ _ => trivial

def mkbuiltin_v3t (tret : xtype) (f : val → val → val → val)
    (WT : ∀ v1 v2 v3, Val.has_rettype (f v1 v2 v3) tret)
    (INJ : ∀ j v1 v1' v2 v2' v3 v3', Val.inject j v1 v1' → Val.inject j v2 v2' →
      Val.inject j v3 v3' → Val.inject j (f v1 v2 v3) (f v1' v2' v3')) :
    builtin_sem tret where
  bs_sem := fun vl => match vl with | [v1, v2, v3] => some (f v1 v2 v3) | _ => none
  bs_well_typed := by
    intro vl
    match vl with
    | [] => trivial
    | [_] => trivial
    | [_, _] => trivial
    | [v1, v2, v3] => exact WT v1 v2 v3
    | _ :: _ :: _ :: _ :: _ => trivial
  bs_inject := by
    intro j vl vl' H
    cases H with
    | inject_list_nil => trivial
    | inject_list_cons v v' vl vl' H1 H2 =>
        cases H2 with
        | inject_list_nil => trivial
        | inject_list_cons v2 v2' vl2 vl2' H1' H2' =>
            cases H2' with
            | inject_list_nil => trivial
            | inject_list_cons v3 v3' vl3 vl3' H1'' H2'' =>
                cases H2'' with
                | inject_list_nil => exact INJ j v v' v2 v2' v3 v3' H1 H1' H1''
                | inject_list_cons _ _ _ _ _ _ => trivial

def mkbuiltin_v1p (tret : xtype) (f : val → Option val)
    (WT : ∀ v1, val_opt_has_rettype (f v1) tret)
    (INJ : ∀ j v1 v1', Val.inject j v1 v1' → val_opt_inject j (f v1) (f v1')) :
    builtin_sem tret where
  bs_sem := fun vl => match vl with | [v1] => f v1 | _ => none
  bs_well_typed := by
    intro vl
    match vl with
    | [] => trivial
    | [v1] => exact WT v1
    | _ :: _ :: _ => trivial
  bs_inject := by
    intro j vl vl' H
    cases H with
    | inject_list_nil => trivial
    | inject_list_cons v v' vl vl' H1 H2 =>
        cases H2 with
        | inject_list_nil => exact INJ j v v' H1
        | inject_list_cons _ _ _ _ _ _ => trivial

def mkbuiltin_v2p (tret : xtype) (f : val → val → Option val)
    (WT : ∀ v1 v2, val_opt_has_rettype (f v1 v2) tret)
    (INJ : ∀ j v1 v1' v2 v2', Val.inject j v1 v1' → Val.inject j v2 v2' →
      val_opt_inject j (f v1 v2) (f v1' v2')) :
    builtin_sem tret where
  bs_sem := fun vl => match vl with | [v1, v2] => f v1 v2 | _ => none
  bs_well_typed := by
    intro vl
    match vl with
    | [] => trivial
    | [_] => trivial
    | [v1, v2] => exact WT v1 v2
    | _ :: _ :: _ :: _ => trivial
  bs_inject := by
    intro j vl vl' H
    cases H with
    | inject_list_nil => trivial
    | inject_list_cons v v' vl vl' H1 H2 =>
        cases H2 with
        | inject_list_nil => trivial
        | inject_list_cons v2 v2' vl2 vl2' H1' H2' =>
            cases H2' with
            | inject_list_nil => exact INJ j v v' v2 v2' H1 H1'
            | inject_list_cons _ _ _ _ _ _ => trivial

/-! ## Looking up builtins by name and signature -/

def lookup_builtin {A : Type} (sig_of : A → signature) (name : String) (sg : signature) :
    List (String × A) → Option A
  | [] => none
  | (n, b) :: l =>
      if name == n && sg == sig_of b then some b else lookup_builtin sig_of name sg l

omit [Archi] in
theorem lookup_builtin_sig {A : Type} (sig_of : A → signature) (name : String) (sg : signature) :
    ∀ {b : A} {l : List (String × A)}, lookup_builtin sig_of name sg l = some b → sig_of b = sg := by
  intro b l
  induction l with
  | nil => intro h; simp [lookup_builtin] at h
  | cons hd tl ih =>
      obtain ⟨n, b'⟩ := hd
      intro h
      unfold lookup_builtin at h
      by_cases hc : name == n && sg == sig_of b'
      · simp only [hc] at h
        injection h with h
        subst h
        have := (Bool.and_eq_true _ _).mp hc
        exact (beq_iff_eq ..).mp this.2 |>.symm
      · simp only [hc] at h
        exact ih h

/-! ## The standard, platform-independent built-ins -/

inductive standard_builtin : Type where
  | BI_select (t : typ)
  | BI_fabs
  | BI_fabsf
  | BI_fsqrt
  | BI_negl
  | BI_addl
  | BI_subl
  | BI_mull
  | BI_i16_bswap
  | BI_i32_bswap
  | BI_i64_bswap
  | BI_unreachable
  | BI_i64_umulh
  | BI_i64_smulh
  | BI_i64_sdiv
  | BI_i64_udiv
  | BI_i64_smod
  | BI_i64_umod
  | BI_i64_shl
  | BI_i64_shr
  | BI_i64_sar
  | BI_i64_dtos
  | BI_i64_dtou
  | BI_i64_stod
  | BI_i64_utod
  | BI_i64_stof
  | BI_i64_utof
  deriving DecidableEq

def standard_builtin_table : List (String × standard_builtin) :=
  [ ("__builtin_sel", .BI_select .Tint)
  , ("__builtin_sel", .BI_select .Tlong)
  , ("__builtin_sel", .BI_select .Tfloat)
  , ("__builtin_sel", .BI_select .Tsingle)
  , ("__builtin_fabs", .BI_fabs)
  , ("__builtin_fabsf", .BI_fabsf)
  , ("__builtin_fsqrt", .BI_fsqrt)
  , ("__builtin_sqrt", .BI_fsqrt)
  , ("__builtin_negl", .BI_negl)
  , ("__builtin_addl", .BI_addl)
  , ("__builtin_subl", .BI_subl)
  , ("__builtin_mull", .BI_mull)
  , ("__builtin_bswap16", .BI_i16_bswap)
  , ("__builtin_bswap", .BI_i32_bswap)
  , ("__builtin_bswap32", .BI_i32_bswap)
  , ("__builtin_bswap64", .BI_i64_bswap)
  , ("__builtin_unreachable", .BI_unreachable)
  , ("__compcert_i64_umulh", .BI_i64_umulh)
  , ("__compcert_i64_smulh", .BI_i64_smulh)
  , ("__compcert_i64_sdiv", .BI_i64_sdiv)
  , ("__compcert_i64_udiv", .BI_i64_udiv)
  , ("__compcert_i64_smod", .BI_i64_smod)
  , ("__compcert_i64_umod", .BI_i64_umod)
  , ("__compcert_i64_shl", .BI_i64_shl)
  , ("__compcert_i64_shr", .BI_i64_shr)
  , ("__compcert_i64_sar", .BI_i64_sar)
  , ("__compcert_i64_dtos", .BI_i64_dtos)
  , ("__compcert_i64_dtou", .BI_i64_dtou)
  , ("__compcert_i64_stod", .BI_i64_stod)
  , ("__compcert_i64_utod", .BI_i64_utod)
  , ("__compcert_i64_stof", .BI_i64_stof)
  , ("__compcert_i64_utof", .BI_i64_utof)
  ]

def standard_builtin_sig (b : standard_builtin) : signature :=
  match b with
  | .BI_select t =>
      let t' := inj_type t
      { sig_args := [.Xint, t', t'], sig_res := t', sig_cc := cc_default }
  | .BI_fabs | .BI_fsqrt =>
      { sig_args := [.Xfloat], sig_res := .Xfloat, sig_cc := cc_default }
  | .BI_fabsf =>
      { sig_args := [.Xsingle], sig_res := .Xsingle, sig_cc := cc_default }
  | .BI_negl =>
      { sig_args := [.Xlong], sig_res := .Xlong, sig_cc := cc_default }
  | .BI_addl | .BI_subl | .BI_i64_umulh | .BI_i64_smulh
  | .BI_i64_sdiv | .BI_i64_udiv | .BI_i64_smod | .BI_i64_umod =>
      { sig_args := [.Xlong, .Xlong], sig_res := .Xlong, sig_cc := cc_default }
  | .BI_mull =>
      { sig_args := [.Xint, .Xint], sig_res := .Xlong, sig_cc := cc_default }
  | .BI_i32_bswap =>
      { sig_args := [.Xint], sig_res := .Xint, sig_cc := cc_default }
  | .BI_i64_bswap =>
      { sig_args := [.Xlong], sig_res := .Xlong, sig_cc := cc_default }
  | .BI_i16_bswap =>
      { sig_args := [.Xint16unsigned], sig_res := .Xint16unsigned, sig_cc := cc_default }
  | .BI_unreachable =>
      { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }
  | .BI_i64_shl | .BI_i64_shr | .BI_i64_sar =>
      { sig_args := [.Xlong, .Xint], sig_res := .Xlong, sig_cc := cc_default }
  | .BI_i64_dtos | .BI_i64_dtou =>
      { sig_args := [.Xfloat], sig_res := .Xlong, sig_cc := cc_default }
  | .BI_i64_stod | .BI_i64_utod =>
      { sig_args := [.Xlong], sig_res := .Xfloat, sig_cc := cc_default }
  | .BI_i64_stof | .BI_i64_utof =>
      { sig_args := [.Xlong], sig_res := .Xsingle, sig_cc := cc_default }

/-- 16-bit byte swap, wrapped to fit `Xint16unsigned`'s refinement
    (`n = zero_ext 16 n`) directly, so the well-typedness obligation reduces
    to `zero_ext_idem`. (Not literally replaying Coq's generic
    `encode_int`/`decode_int`/`rev` round trip — this closed-form formula
    computes the same byte-swapped value.) -/
def bswap16 (n : CompCert.Int) : CompCert.Int :=
  CompCert.Int.zero_ext 16
    (CompCert.Int.repr ((((n.toNat / 256) % 256) + (n.toNat % 256) * 256 : Nat) : Int))

def bswap32 (n : CompCert.Int) : CompCert.Int :=
  let b0 := n.toNat % 256
  let b1 := (n.toNat / 256) % 256
  let b2 := (n.toNat / 65536) % 256
  let b3 := (n.toNat / 16777216) % 256
  CompCert.Int.repr ((b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 : Nat) : Int)

def bswap64 (n : CompCert.Int64) : CompCert.Int64 :=
  let b0 := n.toNat % 256
  let b1 := (n.toNat / 256) % 256
  let b2 := (n.toNat / 65536) % 256
  let b3 := (n.toNat / 16777216) % 256
  let b4 := (n.toNat / 4294967296) % 256
  let b5 := (n.toNat / 1099511627776) % 256
  let b6 := (n.toNat / 281474976710656) % 256
  let b7 := (n.toNat / 72057594037927936) % 256
  CompCert.Int64.repr
    ((b0 * 72057594037927936 + b1 * 281474976710656 + b2 * 1099511627776 + b3 * 4294967296
      + b4 * 16777216 + b5 * 65536 + b6 * 256 + b7 : Nat) : Int)

def standard_builtin_sem (b : standard_builtin) : builtin_sem (standard_builtin_sig b).sig_res :=
  match b with
  | .BI_select t =>
      mkbuiltin_v3t (inj_type t)
        (fun n v1 v2 => match n with
          | .Vint i => Val.normalize (if i == CompCert.Int.zero then v2 else v1) t
          | _ => .Vundef)
        (by
          intro n v1 v2
          cases n with
          | Vint i => exact Val.has_inj_type _ _ (Val.normalize_type _ t)
          | _ => cases (inj_type t) <;> simp [Val.has_rettype])
        (by
          intro j n n' v1 v1' v2 v2' Hn H1 H2
          cases Hn with
          | inject_int i =>
              simp only []
              split
              · exact Val.normalize_inject _ _ _ t H2
              · exact Val.normalize_inject _ _ _ t H1
          | _ => exact .val_inject_undef _)
  | .BI_fabs =>
      mkbuiltin_v1t .Xfloat
        (fun v => match v with | .Vfloat f => .Vfloat (CompCert.Float64.abs f) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_float f => exact .inject_float _
          | _ => exact .val_inject_undef _)
  | .BI_fabsf =>
      mkbuiltin_v1t .Xsingle
        (fun v => match v with | .Vsingle f => .Vsingle (CompCert.Float32.abs f) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_single f => exact .inject_single _
          | _ => exact .val_inject_undef _)
  | .BI_fsqrt =>
      mkbuiltin_v1t .Xfloat
        (fun v => match v with | .Vfloat f => .Vfloat f.sqrt | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_float f => exact .inject_float _
          | _ => exact .val_inject_undef _)
  | .BI_negl =>
      mkbuiltin_v1t .Xlong
        (fun v => match v with | .Vlong n => .Vlong (CompCert.Int64.neg n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_long n => exact .inject_long _
          | _ => exact .val_inject_undef _)
  | .BI_addl => mkbuiltin_v2t .Xlong Val.addl (by
        intro v1 v2
        unfold Val.addl
        cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;>
          (split <;> simp [Val.has_rettype, *]))
      Val.addl_inject
  | .BI_subl => mkbuiltin_v2t .Xlong Val.subl (by
        intro v1 v2
        unfold Val.subl
        cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;>
          split_ifs <;> simp [Val.has_rettype, *])
      Val.subl_inject
  | .BI_mull =>
      mkbuiltin_v2t .Xlong Val.mull'
        (by intro v1 v2; unfold Val.mull'; cases v1 <;> cases v2 <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_int i =>
              cases H2 with
              | inject_int i' => exact .inject_long _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_i16_bswap =>
      mkbuiltin_v1t .Xint16unsigned
        (fun v => match v with | .Vint n => .Vint (bswap16 n) | _ => .Vundef)
        (by
          intro v
          cases v with
          | Vint n => exact (CompCert.Int.zero_ext_idem 16 _).symm
          | _ => trivial)
        (by
          intro j v v' H
          cases H with
          | inject_int n => exact .inject_int _
          | _ => exact .val_inject_undef _)
  | .BI_i32_bswap =>
      mkbuiltin_v1t .Xint
        (fun v => match v with | .Vint n => .Vint (bswap32 n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_int n => exact .inject_int _
          | _ => exact .val_inject_undef _)
  | .BI_i64_bswap =>
      mkbuiltin_v1t .Xlong
        (fun v => match v with | .Vlong n => .Vlong (bswap64 n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_long n => exact .inject_long _
          | _ => exact .val_inject_undef _)
  | .BI_unreachable =>
      { bs_sem := fun _ => none
        bs_well_typed := by intro vl; trivial
        bs_inject := by intro j vl vl' H; trivial }
  | .BI_i64_umulh =>
      mkbuiltin_v2t .Xlong
        (fun v1 v2 => match v1, v2 with
          | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.mulhu n1 n2)
          | _, _ => .Vundef)
        (by intro v1 v2; cases v1 <;> cases v2 <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_long n2 => exact .inject_long _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_i64_smulh =>
      mkbuiltin_v2t .Xlong
        (fun v1 v2 => match v1, v2 with
          | .Vlong n1, .Vlong n2 => .Vlong (CompCert.Int64.mulhs n1 n2)
          | _, _ => .Vundef)
        (by intro v1 v2; cases v1 <;> cases v2 <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_long n2 => exact .inject_long _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_i64_sdiv =>
      mkbuiltin_v2p .Xlong Val.divls
        (by
          intro v1 v2
          unfold Val.divls
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;>
            split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_long n2 =>
                  unfold Val.divls
                  simp only []
                  split_ifs <;> first | trivial | exact Val.inject.inject_long _
              | _ => trivial
          | _ => trivial)
  | .BI_i64_udiv =>
      mkbuiltin_v2p .Xlong Val.divlu
        (by
          intro v1 v2
          unfold Val.divlu
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;>
            split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_long n2 =>
                  unfold Val.divlu
                  simp only []
                  split_ifs <;> first | trivial | exact Val.inject.inject_long _
              | _ => trivial
          | _ => trivial)
  | .BI_i64_smod =>
      mkbuiltin_v2p .Xlong Val.modls
        (by
          intro v1 v2
          unfold Val.modls
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;>
            split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_long n2 =>
                  unfold Val.modls
                  simp only []
                  split_ifs <;> first | trivial | exact Val.inject.inject_long _
              | _ => trivial
          | _ => trivial)
  | .BI_i64_umod =>
      mkbuiltin_v2p .Xlong Val.modlu
        (by
          intro v1 v2
          unfold Val.modlu
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;>
            split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_long n2 =>
                  unfold Val.modlu
                  simp only []
                  split_ifs <;> first | trivial | exact Val.inject.inject_long _
              | _ => trivial
          | _ => trivial)
  | .BI_i64_shl =>
      mkbuiltin_v2t .Xlong Val.shll
        (by
          intro v1 v2
          unfold Val.shll
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;> split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_int n2 =>
                  unfold Val.shll
                  simp only []
                  split_ifs <;> first | exact .val_inject_undef _ | exact Val.inject.inject_long _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_i64_shr =>
      mkbuiltin_v2t .Xlong Val.shrl
        (by
          intro v1 v2
          unfold Val.shrl
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;> split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_int n2 =>
                  unfold Val.shrl
                  simp only []
                  split_ifs <;> first | exact .val_inject_undef _ | exact Val.inject.inject_long _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_i64_sar =>
      mkbuiltin_v2t .Xlong Val.shrlu
        (by
          intro v1 v2
          unfold Val.shrlu
          cases v1 <;> cases v2 <;> simp only [] <;> (try trivial) <;> split_ifs <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_long n1 =>
              cases H2 with
              | inject_int n2 =>
                  unfold Val.shrlu
                  simp only []
                  split_ifs <;> first | exact .val_inject_undef _ | exact Val.inject.inject_long _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_i64_dtos =>
      mkbuiltin_v1p .Xlong
        (fun v => match v with
          | .Vfloat f => (CompCert.Float64.to_long f).map .Vlong
          | _ => none)
        (by
          intro v
          cases v <;> simp only [] <;> (try trivial)
          case Vfloat f => cases (CompCert.Float64.to_long f) <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_float f =>
              simp only []
              cases (CompCert.Float64.to_long f) with
              | none => trivial
              | some l => exact Val.inject.inject_long _
          | _ => trivial)
  | .BI_i64_dtou =>
      mkbuiltin_v1p .Xlong
        (fun v => match v with
          | .Vfloat f => (CompCert.Float64.to_longu f).map .Vlong
          | _ => none)
        (by
          intro v
          cases v <;> simp only [] <;> (try trivial)
          case Vfloat f => cases (CompCert.Float64.to_longu f) <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_float f =>
              simp only []
              cases (CompCert.Float64.to_longu f) with
              | none => trivial
              | some l => exact Val.inject.inject_long _
          | _ => trivial)
  | .BI_i64_stod =>
      mkbuiltin_v1t .Xfloat
        (fun v => match v with | .Vlong n => .Vfloat (CompCert.Float64.of_long n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_long n => exact .inject_float _
          | _ => exact .val_inject_undef _)
  | .BI_i64_utod =>
      mkbuiltin_v1t .Xfloat
        (fun v => match v with | .Vlong n => .Vfloat (CompCert.Float64.of_longu n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_long n => exact .inject_float _
          | _ => exact .val_inject_undef _)
  | .BI_i64_stof =>
      mkbuiltin_v1t .Xsingle
        (fun v => match v with | .Vlong n => .Vsingle (CompCert.Float32.of_long n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_long n => exact .inject_single _
          | _ => exact .val_inject_undef _)
  | .BI_i64_utof =>
      mkbuiltin_v1t .Xsingle
        (fun v => match v with | .Vlong n => .Vsingle (CompCert.Float32.of_longu n) | _ => .Vundef)
        (by intro v; cases v <;> trivial)
        (by
          intro j v v' H
          cases H with
          | inject_long n => exact .inject_single _
          | _ => exact .val_inject_undef _)

end Builtins0
