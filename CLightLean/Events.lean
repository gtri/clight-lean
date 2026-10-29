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

import CLightLean.Globalenvs
import CLightLean.Builtins
import Mathlib.Data.Stream.Init

/-!
# Events and traces

Port of `common/Events.v` from CompCert. Observable events, execution traces,
and (eventually) the semantics of external calls.

The observable behaviour of programs is stated in terms of input/output
events, which represent the actions of the program that the external world
can observe. CompCert leaves much flexibility as to the exact content of
events: the only requirement is that they do not expose memory states nor
pointer values (other than pointers to global variables), because these are
not preserved literally during compilation.
-/

namespace Events

variable [Archi]

/-- Values attached to events. As mentioned above, we do not expose pointer
    values directly. Pointers relative to a global variable are shown with
    the name (identifier) of the variable instead of the block identifier. -/
inductive eventval : Type where
  | EVint        : CompCert.Int -> eventval
  | EVlong       : CompCert.Int64 -> eventval
  | EVfloat      : CompCert.Float64 -> eventval
  | EVsingle     : CompCert.Float32 -> eventval
  | EVptr_global : ident -> Ptrofs -> eventval
  deriving DecidableEq

/-- Observable events. Each event represents either:
    - a system call, recording its name, parameters, and result;
    - a volatile load from a global memory location, recording the chunk
      and address being read and the value just read;
    - a volatile store to a global memory location, recording the chunk
      and address being written and the value stored there;
    - an annotation, recording the text of the annotation and the values
      of the arguments. -/
inductive event : Type where
  | Event_syscall : String -> List eventval -> eventval -> event
  | Event_vload   : memory_chunk -> ident -> Ptrofs -> eventval -> event
  | Event_vstore  : memory_chunk -> ident -> Ptrofs -> eventval -> event
  | Event_annot   : String -> List eventval -> event

/-- The dynamic semantics for programs collect traces of events. Traces are
    of two kinds: finite (type `trace`) or infinite (type `traceinf`). -/
abbrev trace := List event

def E0 : trace := []

/-- Infinite traces, modeled as infinite streams of events.

    Coq represents this with `CoInductive traceinf := Econsinf : event ->
    traceinf -> traceinf`, and separately needs a `traceinf_sim`
    bisimulation relation because Coq's coinductive Leibniz equality is
    unusable for proofs. Since Mathlib's `Stream' α := Nat -> α` is a plain
    function type, equality of streams is just pointwise/functional
    equality, so no bisimulation machinery is needed here. -/
abbrev traceinf := Stream' event

/-- Append a finite trace onto an infinite trace. -/
def Eappinf (t : trace) (T : traceinf) : traceinf :=
  match t with
  | [] => T
  | ev :: t' => Stream'.cons ev (Eappinf t' T)

@[simp] theorem E0_left (t : trace) : E0 ++ t = t := rfl

@[simp] theorem E0_right (t : trace) : t ++ E0 = t := List.append_nil t

theorem Eapp_assoc (t1 t2 t3 : trace) : (t1 ++ t2) ++ t3 = t1 ++ (t2 ++ t3) :=
  List.append_assoc t1 t2 t3

theorem Eapp_E0_inv {t1 t2 : trace} (h : t1 ++ t2 = E0) : t1 = E0 ∧ t2 = E0 :=
  List.append_eq_nil_iff.mp h

@[simp] theorem E0_left_inf (T : traceinf) : Eappinf E0 T = T := rfl

theorem Eappinf_assoc (t1 t2 : trace) (T : traceinf) :
    Eappinf (t1 ++ t2) T = Eappinf t1 (Eappinf t2 T) := by
  induction t1 with
  | nil => rfl
  | cons ev t1' ih => simp [Eappinf, ih]

/-- Bisimilarity between infinite traces.

    Since `traceinf` is a plain function type here (see above), this
    relation is definitionally equality. It is kept as a named definition
    purely for naming continuity with the CompCert source, so that later
    ports (e.g. `Smallstep.lean`) that reference `traceinf_sim` by name
    carry over directly, while the actual proofs reduce to `Eq` lemmas. -/
def traceinf_sim (T1 T2 : traceinf) : Prop := T1 = T2

theorem traceinf_sim_refl (T : traceinf) : traceinf_sim T T := rfl

theorem traceinf_sim_sym {T1 T2 : traceinf} (h : traceinf_sim T1 T2) :
    traceinf_sim T2 T1 := h.symm

theorem traceinf_sim_trans {T1 T2 T3 : traceinf}
    (h1 : traceinf_sim T1 T2) (h2 : traceinf_sim T2 T3) : traceinf_sim T1 T3 :=
  h1.trans h2

/-- Prefixes of traces. -/

def trace_prefix (t1 t2 : trace) : Prop := ∃ t3, t2 = t1 ++ t3

def traceinf_prefix (t1 : trace) (T2 : traceinf) : Prop :=
  ∃ T3, T2 = Eappinf t1 T3

theorem trace_prefix_app {t1 t2 : trace} (h : trace_prefix t1 t2) (t : trace) :
    trace_prefix (t ++ t1) (t ++ t2) := by
  obtain ⟨t3, rfl⟩ := h
  exact ⟨t3, (List.append_assoc t t1 t3).symm⟩

theorem traceinf_prefix_app {t1 : trace} {T2 : traceinf}
    (h : traceinf_prefix t1 T2) (t : trace) :
    traceinf_prefix (t ++ t1) (Eappinf t T2) := by
  obtain ⟨T3, rfl⟩ := h
  exact ⟨T3, (Eappinf_assoc t t1 T3).symm⟩

/-! ## Relating values and event values

    Ported from CompCert's `EVENTVAL` section. The Coq version is
    parameterized over an abstract `Senv.t` (symbol environment); since we
    did not port a separate `Senv` module, we parameterize directly over a
    `Genv.t F V` (which provides exactly the `find_symbol`/`public_symbol`/
    `block_is_volatile` operations `Senv` exposes). -/

variable {F V : Type}

/-- Translation between values and event values, relative to a symbol
    environment `ge`. -/
inductive eventval_match (ge : Genv.t F V) : eventval → typ → val → Prop where
  | ev_match_int (i : CompCert.Int) :
      eventval_match ge (.EVint i) .Tint (.Vint i)
  | ev_match_long (i : CompCert.Int64) :
      eventval_match ge (.EVlong i) .Tlong (.Vlong i)
  | ev_match_float (f : CompCert.Float64) :
      eventval_match ge (.EVfloat f) .Tfloat (.Vfloat f)
  | ev_match_single (f : CompCert.Float32) :
      eventval_match ge (.EVsingle f) .Tsingle (.Vsingle f)
  | ev_match_ptr (id : ident) (b : block) (ofs : ptrofs)
      (H1 : Genv.public_symbol ge id = true)
      (H2 : Genv.find_symbol ge id = some b) :
      eventval_match ge (.EVptr_global id ofs) Tptr (.Vptr b ofs)

inductive eventval_list_match (ge : Genv.t F V) :
    List eventval → List typ → List val → Prop where
  | evl_match_nil : eventval_list_match ge [] [] []
  | evl_match_cons (ev1 : eventval) (evl : List eventval) (ty1 : typ) (tyl : List typ)
      (v1 : val) (vl : List val)
      (H1 : eventval_match ge ev1 ty1 v1) (H2 : eventval_list_match ge evl tyl vl) :
      eventval_list_match ge (ev1 :: evl) (ty1 :: tyl) (v1 :: vl)

/-- Validity: an `eventval` is valid w.r.t. `ge` if any global-variable
    reference it contains is a public symbol. -/
def eventval_valid (ge : Genv.t F V) (ev : eventval) : Prop :=
  match ev with
  | .EVint _ => True
  | .EVlong _ => True
  | .EVfloat _ => True
  | .EVsingle _ => True
  | .EVptr_global id _ => Genv.public_symbol ge id = true

/-- The type carried by an `eventval`, independent of any `ge`. -/
def eventval_type (ev : eventval) : typ :=
  match ev with
  | .EVint _ => .Tint
  | .EVlong _ => .Tlong
  | .EVfloat _ => .Tfloat
  | .EVsingle _ => .Tsingle
  | .EVptr_global _ _ => Tptr

/-- Every constructor of `eventval_match` produces a type index that is
    literally `eventval_type` of its `eventval` argument. This is not in
    the original CompCert source, but it lets later lemmas relating two
    different `eventval_match` derivations (e.g. `eventval_match_same_type`)
    avoid ever comparing `Tptr` against `Tint`/`Tlong` by case analysis,
    which is not decidable without concrete knowledge of `Archi.ptr64`. -/
theorem eventval_type_eq_of_match {ge : Genv.t F V} {ev : eventval} {ty : typ} {v : val}
    (h : eventval_match ge ev ty v) : eventval_type ev = ty := by
  cases h <;> rfl

/-- Full inversion of `eventval_match`, as a disjunction of the five possible
    shapes. This is not in the original CompCert source. It exists because
    `cases`-ing on a *second* `eventval_match` hypothesis whose `ty` (or
    `ev`) index has already been pinned to a concrete literal by an earlier
    `cases` runs into an undecidable comparison against `Tptr` (which
    unfolds to an `Archi.ptr64`-guarded `if`). Applying this lemma to each
    `eventval_match` hypothesis *independently* (each application is a safe,
    single-hypothesis `cases`) sidesteps that problem entirely: any
    resulting contradiction between two derivations is then found via the
    (always decidable) shape of the *value* component instead. -/
theorem eventval_match_inv {ge : Genv.t F V} {ev : eventval} {ty : typ} {v : val}
    (h : eventval_match ge ev ty v) :
    (∃ i, ev = .EVint i ∧ ty = .Tint ∧ v = .Vint i) ∨
    (∃ i, ev = .EVlong i ∧ ty = .Tlong ∧ v = .Vlong i) ∨
    (∃ f, ev = .EVfloat f ∧ ty = .Tfloat ∧ v = .Vfloat f) ∨
    (∃ f, ev = .EVsingle f ∧ ty = .Tsingle ∧ v = .Vsingle f) ∨
    (∃ id b ofs, ev = .EVptr_global id ofs ∧ ty = Tptr ∧ v = .Vptr b ofs ∧
      Genv.public_symbol ge id = true ∧ Genv.find_symbol ge id = some b) := by
  cases h with
  | ev_match_int i => exact .inl ⟨i, rfl, rfl, rfl⟩
  | ev_match_long i => exact .inr (.inl ⟨i, rfl, rfl, rfl⟩)
  | ev_match_float f => exact .inr (.inr (.inl ⟨f, rfl, rfl, rfl⟩))
  | ev_match_single f => exact .inr (.inr (.inr (.inl ⟨f, rfl, rfl, rfl⟩)))
  | ev_match_ptr id b ofs H1 H2 => exact .inr (.inr (.inr (.inr ⟨id, b, ofs, rfl, rfl, rfl, H1, H2⟩)))

/-- Some properties of these translation predicates. -/

theorem eventval_match_type {ge : Genv.t F V} {ev : eventval} {ty : typ} {v : val}
    (h : eventval_match ge ev ty v) : Val.has_type v ty := by
  cases h <;> first
    | trivial
    | exact Val.Vptr_has_type _ _

theorem eventval_list_match_length {ge : Genv.t F V} {evl : List eventval} {tyl : List typ}
    {vl : List val} (h : eventval_list_match ge evl tyl vl) : vl.length = tyl.length := by
  induction h with
  | evl_match_nil => rfl
  | evl_match_cons _ _ _ _ _ _ _ _ ih => simp [ih]

theorem eventval_match_lessdef {ge : Genv.t F V} {ev : eventval} {ty : typ} {v1 v2 : val}
    (h : eventval_match ge ev ty v1) (hl : Val.lessdef v1 v2) : eventval_match ge ev ty v2 := by
  cases h with
  | ev_match_int i => cases hl; exact .ev_match_int i
  | ev_match_long i => cases hl; exact .ev_match_long i
  | ev_match_float f => cases hl; exact .ev_match_float f
  | ev_match_single f => cases hl; exact .ev_match_single f
  | ev_match_ptr id b ofs H1 H2 => cases hl; exact .ev_match_ptr id b ofs H1 H2

theorem eventval_list_match_lessdef {ge : Genv.t F V} {evl : List eventval} {tyl : List typ}
    {vl1 : List val} (h : eventval_list_match ge evl tyl vl1) :
    ∀ {vl2 : List val}, Val.lessdef_list vl1 vl2 → eventval_list_match ge evl tyl vl2 := by
  induction h with
  | evl_match_nil => intro vl2 hl; cases hl; exact .evl_match_nil
  | evl_match_cons ev1 evl ty1 tyl v1 vl hm _hlm ih =>
      intro vl2 hl
      cases hl with
      | lessdef_list_cons _ v2 _ vl2' hv hvl =>
          exact .evl_match_cons ev1 evl ty1 tyl v2 vl2'
            (eventval_match_lessdef hm hv) (ih hvl)

/-- Determinism. -/

theorem eventval_match_determ_1 {ge : Genv.t F V} {ev : eventval} {ty : typ} {v1 v2 : val}
    (h1 : eventval_match ge ev ty v1) (h2 : eventval_match ge ev ty v2) : v1 = v2 := by
  cases h1 with
  | ev_match_int i => cases h2; rfl
  | ev_match_long i => cases h2; rfl
  | ev_match_float f => cases h2; rfl
  | ev_match_single f => cases h2; rfl
  | ev_match_ptr id b ofs H1 H2 =>
      cases h2 with
      | ev_match_ptr _ b' _ _ H2' => rw [H2] at H2'; injection H2' with hb; rw [hb]

theorem eventval_match_determ_2 {ge : Genv.t F V} {ev1 ev2 : eventval} {ty : typ} {v : val}
    (find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
      Genv.find_symbol ge id2 = some b → id1 = id2)
    (h1 : eventval_match ge ev1 ty v) (h2 : eventval_match ge ev2 ty v) : ev1 = ev2 := by
  rcases eventval_match_inv h1 with
    ⟨i, rfl, -, hv1⟩ | ⟨i, rfl, -, hv1⟩ | ⟨f, rfl, -, hv1⟩ | ⟨f, rfl, -, hv1⟩ |
    ⟨id, b, ofs, rfl, -, hv1, _, hfs1⟩ <;>
  rcases eventval_match_inv h2 with
    ⟨i', rfl, -, hv2⟩ | ⟨i', rfl, -, hv2⟩ | ⟨f', rfl, -, hv2⟩ | ⟨f', rfl, -, hv2⟩ |
    ⟨id', b', ofs', rfl, -, hv2, _, hfs2⟩ <;>
  rw [hv1] at hv2 <;>
  first
    | (injection hv2 with h; rw [h])
    | (injection hv2 with hb hofs; subst hb; subst hofs; rw [find_symbol_injective id id' b hfs1 hfs2])
    | (exact absurd hv2 (by decide))
    | (injection hv2)

theorem eventval_list_match_determ_2 {ge : Genv.t F V} {evl1 : List eventval} {tyl : List typ}
    {vl : List val}
    (find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
      Genv.find_symbol ge id2 = some b → id1 = id2)
    (h1 : eventval_list_match ge evl1 tyl vl) :
    ∀ {evl2 : List eventval}, eventval_list_match ge evl2 tyl vl → evl1 = evl2 := by
  induction h1 with
  | evl_match_nil => intro evl2 h2; cases h2; rfl
  | evl_match_cons ev1 evl1' ty1 tyl' v1 vl' hm _hlm ih =>
      intro evl2 h2
      cases h2 with
      | evl_match_cons ev2 evl2' _ _ _ _ hm' hlm' =>
          rw [eventval_match_determ_2 find_symbol_injective hm hm', ih hlm']

/-- `Tptr` is `Tint` when `Archi.ptr64 = false`. -/
theorem Tptr_eq_int (h : Archi.ptr64 = false) : Tptr = (typ.Tint : typ) := by
  unfold Tptr; simp [h]

/-- `Tptr` is `Tlong` when `Archi.ptr64 = true`. -/
theorem Tptr_eq_long (h : Archi.ptr64 = true) : Tptr = (typ.Tlong : typ) := by
  unfold Tptr; simp [h]

/-- `Tptr` is never `Tfloat`, regardless of `Archi.ptr64`. -/
theorem Tptr_ne_float : Tptr ≠ (typ.Tfloat : typ) := by
  unfold Tptr; by_cases h : Archi.ptr64 <;> simp [h]

/-- `Tptr` is never `Tsingle`, regardless of `Archi.ptr64`. -/
theorem Tptr_ne_single : Tptr ≠ (typ.Tsingle : typ) := by
  unfold Tptr; by_cases h : Archi.ptr64 <;> simp [h]

/-- Receptiveness: if `ev2` has the same validity and type as `ev1`, and
    `ev1` matches type `ty`, then `ev2` also matches type `ty` (for some
    value). -/
theorem eventval_match_receptive {ge : Genv.t F V} {ev1 : eventval} {ty : typ} {v1 : val}
    {ev2 : eventval}
    (h : eventval_match ge ev1 ty v1)
    (hv1 : eventval_valid ge ev1) (hv2 : eventval_valid ge ev2)
    (htyp : eventval_type ev1 = eventval_type ev2) :
    ∃ v2, eventval_match ge ev2 ty v2 := by
  cases h with
  | ev_match_int i =>
    cases ev2 with
    | EVint i0 => exact ⟨.Vint i0, .ev_match_int i0⟩
    | EVlong i0 => simp [eventval_type] at htyp
    | EVfloat f0 => simp [eventval_type] at htyp
    | EVsingle f0 => simp [eventval_type] at htyp
    | EVptr_global id0 ofs0 =>
      cases hptr : Archi.ptr64
      · obtain ⟨b, hb⟩ := Genv.public_symbol_exists ge id0 hv2
        exact ⟨.Vptr b ofs0, Tptr_eq_int hptr ▸ .ev_match_ptr id0 b ofs0 hv2 hb⟩
      · exact absurd htyp (by simp [eventval_type, Tptr_eq_long hptr])
  | ev_match_long i =>
    cases ev2 with
    | EVint i0 => simp [eventval_type] at htyp
    | EVlong i0 => exact ⟨.Vlong i0, .ev_match_long i0⟩
    | EVfloat f0 => simp [eventval_type] at htyp
    | EVsingle f0 => simp [eventval_type] at htyp
    | EVptr_global id0 ofs0 =>
      cases hptr : Archi.ptr64
      · exact absurd htyp (by simp [eventval_type, Tptr_eq_int hptr])
      · obtain ⟨b, hb⟩ := Genv.public_symbol_exists ge id0 hv2
        exact ⟨.Vptr b ofs0, Tptr_eq_long hptr ▸ .ev_match_ptr id0 b ofs0 hv2 hb⟩
  | ev_match_float f =>
    cases ev2 with
    | EVint i0 => simp [eventval_type] at htyp
    | EVlong i0 => simp [eventval_type] at htyp
    | EVfloat f0 => exact ⟨.Vfloat f0, .ev_match_float f0⟩
    | EVsingle f0 => simp [eventval_type] at htyp
    | EVptr_global id0 ofs0 =>
      simp [eventval_type] at htyp; exact absurd htyp.symm Tptr_ne_float
  | ev_match_single f =>
    cases ev2 with
    | EVint i0 => simp [eventval_type] at htyp
    | EVlong i0 => simp [eventval_type] at htyp
    | EVfloat f0 => simp [eventval_type] at htyp
    | EVsingle f0 => exact ⟨.Vsingle f0, .ev_match_single f0⟩
    | EVptr_global id0 ofs0 =>
      simp [eventval_type] at htyp; exact absurd htyp.symm Tptr_ne_single
  | ev_match_ptr id b ofs H1 H2 =>
    cases ev2 with
    | EVint i0 =>
      cases hptr : Archi.ptr64
      · exact ⟨.Vint i0, (Tptr_eq_int hptr).symm ▸ eventval_match.ev_match_int i0⟩
      · exact absurd htyp (by simp [eventval_type, Tptr_eq_long hptr])
    | EVlong i0 =>
      cases hptr : Archi.ptr64
      · exact absurd htyp (by simp [eventval_type, Tptr_eq_int hptr])
      · exact ⟨.Vlong i0, (Tptr_eq_long hptr).symm ▸ eventval_match.ev_match_long i0⟩
    | EVfloat f0 => simp [eventval_type] at htyp; exact absurd htyp Tptr_ne_float
    | EVsingle f0 => simp [eventval_type] at htyp; exact absurd htyp Tptr_ne_single
    | EVptr_global id0 ofs0 =>
      obtain ⟨b0, hb0⟩ := Genv.public_symbol_exists ge id0 hv2
      exact ⟨.Vptr b0 ofs0, .ev_match_ptr id0 b0 ofs0 hv2 hb0⟩

theorem eventval_match_valid {ge : Genv.t F V} {ev : eventval} {ty : typ} {v : val}
    (h : eventval_match ge ev ty v) : eventval_valid ge ev := by
  cases h with
  | ev_match_int i => trivial
  | ev_match_long i => trivial
  | ev_match_float f => trivial
  | ev_match_single f => trivial
  | ev_match_ptr id b ofs H1 H2 => exact H1

theorem eventval_match_same_type {ge : Genv.t F V} {ev1 ev2 : eventval} {ty : typ}
    {v1 v2 : val} (h1 : eventval_match ge ev1 ty v1) (h2 : eventval_match ge ev2 ty v2) :
    eventval_type ev1 = eventval_type ev2 := by
  rw [eventval_type_eq_of_match h1, eventval_type_eq_of_match h2]

/-! ## Invariance under changes to the global environment

    Ported from `EVENTVAL_INV`. `ge1` and `ge2` may range over `Genv.t`
    instantiated at different `F`/`V` (as in Coq, where they may be
    different `Senv.t` values coming from different intermediate
    languages). -/

theorem eventval_valid_preserved {F1 V1 F2 V2 : Type} {ge1 : Genv.t F1 V1} {ge2 : Genv.t F2 V2}
    (public_preserved : ∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id)
    {ev : eventval} (h : eventval_valid ge1 ev) : eventval_valid ge2 ev := by
  cases ev <;> simp_all [eventval_valid]

theorem eventval_match_preserved {F1 V1 F2 V2 : Type} {ge1 : Genv.t F1 V1} {ge2 : Genv.t F2 V2}
    (public_preserved : ∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id)
    (symbols_preserved : ∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
    {ev : eventval} {ty : typ} {v : val}
    (h : eventval_match ge1 ev ty v) : eventval_match ge2 ev ty v := by
  cases h with
  | ev_match_int i => exact .ev_match_int i
  | ev_match_long i => exact .ev_match_long i
  | ev_match_float f => exact .ev_match_float f
  | ev_match_single f => exact .ev_match_single f
  | ev_match_ptr id b ofs H1 H2 =>
      exact .ev_match_ptr id b ofs (public_preserved id ▸ H1) (symbols_preserved id ▸ H2)

theorem eventval_list_match_preserved {F1 V1 F2 V2 : Type} {ge1 : Genv.t F1 V1}
    {ge2 : Genv.t F2 V2}
    (public_preserved : ∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id)
    (symbols_preserved : ∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
    {evl : List eventval} {tyl : List typ} {vl : List val}
    (h : eventval_list_match ge1 evl tyl vl) : eventval_list_match ge2 evl tyl vl := by
  induction h with
  | evl_match_nil => exact .evl_match_nil
  | evl_match_cons ev1 evl' ty1 tyl' v1 vl' hm _hlm ih =>
      exact .evl_match_cons ev1 evl' ty1 tyl' v1 vl'
        (eventval_match_preserved public_preserved symbols_preserved hm) ih

/-! ## Compatibility with memory injections

    Ported from `EVENTVAL_INJECT`. -/

def symbols_inject {F1 V1 F2 V2 : Type} (mi : meminj) (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2) :
    Prop :=
  (∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id) ∧
  (∀ id b1 b2 delta, mi b1 = some (b2, delta) → Genv.find_symbol ge1 id = some b1 →
    delta = 0 ∧ Genv.find_symbol ge2 id = some b2) ∧
  (∀ id b1, Genv.public_symbol ge1 id = true → Genv.find_symbol ge1 id = some b1 →
    ∃ b2, mi b1 = some (b2, 0) ∧ Genv.find_symbol ge2 id = some b2) ∧
  (∀ b1 b2 delta, mi b1 = some (b2, delta) →
    Genv.block_is_volatile ge2 b2 = Genv.block_is_volatile ge1 b1)

theorem eventval_match_inject {F1 V1 F2 V2 : Type} {mi : meminj} {ge1 : Genv.t F1 V1}
    {ge2 : Genv.t F2 V2} (symb_inj : symbols_inject mi ge1 ge2)
    {ev : eventval} {ty : typ} {v1 v2 : val}
    (h : eventval_match ge1 ev ty v1) (hinj : Val.inject mi v1 v2) :
    eventval_match ge2 ev ty v2 := by
  obtain ⟨A, _B, C, _D⟩ := symb_inj
  cases h with
  | ev_match_int i => cases hinj; exact .ev_match_int i
  | ev_match_long i => cases hinj; exact .ev_match_long i
  | ev_match_float f => cases hinj; exact .ev_match_float f
  | ev_match_single f => cases hinj; exact .ev_match_single f
  | ev_match_ptr id b ofs H1 H2 =>
      cases hinj with
      | inject_ptr _ _ b2 ofs2 delta hmi hofs2 =>
          obtain ⟨b3, heq, hfs2⟩ := C id b H1 H2
          rw [hmi] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨hb, hd⟩ := heq
          subst hb
          have hofs2' : ofs2 = ofs := by
            rw [hofs2, hd, show Ptrofs.repr 0 = Ptrofs.zero from rfl, Ptrofs.add_zero]
          rw [hofs2']
          exact .ev_match_ptr id b2 ofs (A id ▸ H1) hfs2

theorem eventval_match_inject_2 {F1 V1 F2 V2 : Type} {mi : meminj} {ge1 : Genv.t F1 V1}
    {ge2 : Genv.t F2 V2} (symb_inj : symbols_inject mi ge1 ge2)
    {ev : eventval} {ty : typ} {v1 : val} (h : eventval_match ge1 ev ty v1) :
    ∃ v2, eventval_match ge2 ev ty v2 ∧ Val.inject mi v1 v2 := by
  obtain ⟨A, _B, C, _D⟩ := symb_inj
  cases h with
  | ev_match_int i => exact ⟨.Vint i, .ev_match_int i, .inject_int i⟩
  | ev_match_long i => exact ⟨.Vlong i, .ev_match_long i, .inject_long i⟩
  | ev_match_float f => exact ⟨.Vfloat f, .ev_match_float f, .inject_float f⟩
  | ev_match_single f => exact ⟨.Vsingle f, .ev_match_single f, .inject_single f⟩
  | ev_match_ptr id b ofs H1 H2 =>
      obtain ⟨b2, hmi, hfs2⟩ := C id b H1 H2
      refine ⟨.Vptr b2 ofs, .ev_match_ptr id b2 ofs (A id ▸ H1) hfs2, ?_⟩
      have hofs : ofs = Ptrofs.add ofs (Ptrofs.repr 0) := by
        rw [show Ptrofs.repr 0 = Ptrofs.zero from rfl, Ptrofs.add_zero]
      exact Val.inject.inject_ptr b ofs b2 ofs 0 hmi hofs

theorem eventval_list_match_inject {F1 V1 F2 V2 : Type} {mi : meminj} {ge1 : Genv.t F1 V1}
    {ge2 : Genv.t F2 V2} (symb_inj : symbols_inject mi ge1 ge2)
    {evl : List eventval} {tyl : List typ} {vl1 : List val}
    (h : eventval_list_match ge1 evl tyl vl1) :
    ∀ {vl2 : List val}, Val.inject_list mi vl1 vl2 → eventval_list_match ge2 evl tyl vl2 := by
  induction h with
  | evl_match_nil => intro vl2 hl; cases hl; exact .evl_match_nil
  | evl_match_cons ev1 evl' ty1 tyl' v1 vl' hm _hlm ih =>
      intro vl2 hl
      cases hl with
      | inject_list_cons _ v2 _ vl2' hv hvl =>
          exact .evl_match_cons ev1 evl' ty1 tyl' v2 vl2'
            (eventval_match_inject symb_inj hm hv) (ih hvl)

/-! ## Matching traces

    Ported from `MATCH_TRACES` / `MATCH_TRACES_INV`. Matching between traces
    corresponding to single transitions: arguments (provided by the
    program) must be equal; results (provided by the outside world) can
    vary as long as they convert safely to values. Needed by `Smallstep`'s
    `receptive`/`determinate` semantic classes. -/

inductive match_traces (ge : Genv.t F V) : trace → trace → Prop where
  | match_traces_E0 : match_traces ge [] []
  | match_traces_syscall (id : String) (args : List eventval) (res1 res2 : eventval)
      (H1 : eventval_valid ge res1) (H2 : eventval_valid ge res2)
      (H3 : eventval_type res1 = eventval_type res2) :
      match_traces ge [.Event_syscall id args res1] [.Event_syscall id args res2]
  | match_traces_vload (chunk : memory_chunk) (id : ident) (ofs : ptrofs) (res1 res2 : eventval)
      (H1 : eventval_valid ge res1) (H2 : eventval_valid ge res2)
      (H3 : eventval_type res1 = eventval_type res2) :
      match_traces ge [.Event_vload chunk id ofs res1] [.Event_vload chunk id ofs res2]
  | match_traces_vstore (chunk : memory_chunk) (id : ident) (ofs : ptrofs) (arg : eventval) :
      match_traces ge [.Event_vstore chunk id ofs arg] [.Event_vstore chunk id ofs arg]
  | match_traces_annot (id : String) (args : List eventval) :
      match_traces ge [.Event_annot id args] [.Event_annot id args]

/-- Invariance of `match_traces` under change of global environment. -/
theorem match_traces_preserved {F1 V1 F2 V2 : Type} {ge1 : Genv.t F1 V1} {ge2 : Genv.t F2 V2}
    (public_preserved : ∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id)
    {t1 t2 : trace} (h : match_traces ge1 t1 t2) : match_traces ge2 t1 t2 := by
  induction h with
  | match_traces_E0 => exact .match_traces_E0
  | match_traces_syscall id args res1 res2 H1 H2 H3 =>
      exact .match_traces_syscall id args res1 res2
        (eventval_valid_preserved public_preserved H1)
        (eventval_valid_preserved public_preserved H2) H3
  | match_traces_vload chunk id ofs res1 res2 H1 H2 H3 =>
      exact .match_traces_vload chunk id ofs res1 res2
        (eventval_valid_preserved public_preserved H1)
        (eventval_valid_preserved public_preserved H2) H3
  | match_traces_vstore chunk id ofs arg => exact .match_traces_vstore chunk id ofs arg
  | match_traces_annot id args => exact .match_traces_annot id args

/-- An output trace consists only of events that don't take a result from
    the outside world (i.e. it excludes syscalls and volatile loads). -/
def output_event (ev : event) : Prop :=
  match ev with
  | .Event_syscall _ _ _ => False
  | .Event_vload _ _ _ _ => False
  | .Event_vstore _ _ _ _ => True
  | .Event_annot _ _ => True

def output_trace (t : trace) : Prop :=
  match t with
  | [] => True
  | ev :: t' => output_event ev ∧ output_trace t'

/-! ## Semantics of volatile memory accesses

    Ported from `Events.v`'s "Semantics of volatile memory accesses" section. -/

open Memory (mem load loadv storev alloc store free loadbytes storebytes size_chunk)

/-- A volatile load: either reads through the environment (if the address is
    a volatile global variable), producing an `Event_vload` event, or reads
    ordinary memory silently. -/
inductive volatile_load (ge : Genv.t F V) :
    memory_chunk → mem → block → ptrofs → trace → val → Prop where
  | volatile_load_vol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs)
      (id : ident) (ev : eventval) (v : val)
      (H1 : Genv.block_is_volatile ge b = true)
      (H2 : Genv.find_symbol ge id = some b)
      (H3 : eventval_match ge ev (type_of_chunk chunk) v) :
      volatile_load ge chunk m b ofs [.Event_vload chunk id ofs ev] (Val.load_result chunk v)
  | volatile_load_nonvol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs) (v : val)
      (H1 : Genv.block_is_volatile ge b = false)
      (H2 : loadv chunk m (.Vptr b ofs) = some v) :
      volatile_load ge chunk m b ofs E0 v

/-- A volatile store: either writes through the environment, producing an
    `Event_vstore` event (leaving memory untouched), or writes ordinary
    memory silently. -/
inductive volatile_store (ge : Genv.t F V) :
    memory_chunk → mem → block → ptrofs → val → trace → mem → Prop where
  | volatile_store_vol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs)
      (id : ident) (ev : eventval) (v : val)
      (H1 : Genv.block_is_volatile ge b = true)
      (H2 : Genv.find_symbol ge id = some b)
      (H3 : eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v)) :
      volatile_store ge chunk m b ofs v [.Event_vstore chunk id ofs ev] m
  | volatile_store_nonvol (chunk : memory_chunk) (m : mem) (b : block) (ofs : ptrofs) (v : val)
      (m' : mem)
      (H1 : Genv.block_is_volatile ge b = false)
      (H2 : storev chunk m (.Vptr b ofs) v = some m') :
      volatile_store ge chunk m b ofs v E0 m'

/-- Invariance under change of global environment that preserves symbols
    (in place of Coq's bundled `Senv.equiv`, spelled out as its three
    components directly). -/
theorem volatile_load_preserved {F1 V1 F2 V2 : Type} {ge1 : Genv.t F1 V1} {ge2 : Genv.t F2 V2}
    (public_preserved : ∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id)
    (symbols_preserved : ∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
    (volatile_preserved : ∀ b, Genv.block_is_volatile ge2 b = Genv.block_is_volatile ge1 b)
    {chunk : memory_chunk} {m : mem} {b : block} {ofs : ptrofs} {t : trace} {v : val}
    (h : volatile_load ge1 chunk m b ofs t v) : volatile_load ge2 chunk m b ofs t v := by
  cases h with
  | volatile_load_vol id ev v H1 H2 H3 =>
      exact .volatile_load_vol chunk m b ofs id ev v
        (volatile_preserved b ▸ H1) (symbols_preserved id ▸ H2)
        (eventval_match_preserved public_preserved symbols_preserved H3)
  | volatile_load_nonvol v H1 H2 =>
      exact .volatile_load_nonvol chunk m b ofs v (volatile_preserved b ▸ H1) H2

theorem volatile_store_preserved {F1 V1 F2 V2 : Type} {ge1 : Genv.t F1 V1} {ge2 : Genv.t F2 V2}
    (public_preserved : ∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id)
    (symbols_preserved : ∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
    (volatile_preserved : ∀ b, Genv.block_is_volatile ge2 b = Genv.block_is_volatile ge1 b)
    {chunk : memory_chunk} {m : mem} {b : block} {ofs : ptrofs} {v : val} {t : trace} {m' : mem}
    (h : volatile_store ge1 chunk m b ofs v t m') : volatile_store ge2 chunk m b ofs v t m' := by
  cases h with
  | volatile_store_vol id ev v H1 H2 H3 =>
      exact .volatile_store_vol chunk m b ofs id ev v
        (volatile_preserved b ▸ H1) (symbols_preserved id ▸ H2)
        (eventval_match_preserved public_preserved symbols_preserved H3)
  | volatile_store_nonvol v m' H1 H2 =>
      exact .volatile_store_nonvol chunk m b ofs v m' (volatile_preserved b ▸ H1) H2

theorem volatile_load_receptive {ge : Genv.t F V} {chunk : memory_chunk} {m : mem} {b : block}
    {ofs : ptrofs} {t1 : trace} {v1 : val} {t2 : trace}
    (h : volatile_load ge chunk m b ofs t1 v1) (hm : match_traces ge t1 t2) :
    ∃ v2, volatile_load ge chunk m b ofs t2 v2 := by
  cases h with
  | volatile_load_vol id ev v H1 H2 H3 =>
      cases hm with
      | match_traces_vload _ _ _ _ res2 Hv1 Hv2 Htyp =>
          obtain ⟨v', hv'⟩ := eventval_match_receptive H3 Hv1 Hv2 Htyp
          exact ⟨Val.load_result chunk v', .volatile_load_vol chunk m b ofs id res2 v' H1 H2 hv'⟩
  | volatile_load_nonvol _ H1 H2 =>
      cases hm with
      | match_traces_E0 => exact ⟨v1, .volatile_load_nonvol chunk m b ofs v1 H1 H2⟩

theorem volatile_store_receptive {ge : Genv.t F V} {chunk : memory_chunk} {m : mem} {b : block}
    {ofs : ptrofs} {v : val} {t1 : trace} {m1 : mem} {t2 : trace}
    (h : volatile_store ge chunk m b ofs v t1 m1) (hm : match_traces ge t1 t2) : t1 = t2 := by
  cases h with
  | volatile_store_vol id ev v H1 H2 H3 =>
      cases hm with
      | match_traces_vstore => rfl
  | volatile_store_nonvol v m' H1 H2 =>
      cases hm with
      | match_traces_E0 => rfl

/-- Determinism of `volatile_load` up to trace-matching. Needs
    `find_symbol` injectivity explicitly, since we split well-formedness
    out of `Genv.t` into the separate `Genv.wf` predicate (see Block 2's
    `eventval_match_determ_2`). -/
theorem volatile_load_determ {ge : Genv.t F V}
    (find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
      Genv.find_symbol ge id2 = some b → id1 = id2)
    {chunk : memory_chunk} {m : mem} {b : block} {ofs : ptrofs}
    {t1 : trace} {v1 : val} {t2 : trace} {v2 : val}
    (h1 : volatile_load ge chunk m b ofs t1 v1) (h2 : volatile_load ge chunk m b ofs t2 v2) :
    match_traces ge t1 t2 ∧ (t1 = t2 → v1 = v2) := by
  cases h1 with
  | volatile_load_vol id ev v H1 H2 H3 =>
      cases h2 with
      | volatile_load_vol id' ev' v' H1' H2' H3' =>
          have hid : id = id' := find_symbol_injective id id' b H2 H2'
          subst hid
          refine ⟨.match_traces_vload chunk id ofs ev ev'
              (eventval_match_valid H3) (eventval_match_valid H3')
              (eventval_match_same_type H3 H3'), ?_⟩
          intro heq
          have hev : ev = ev' := by
            simpa using heq
          rw [hev] at H3
          rw [eventval_match_determ_1 H3 H3']
      | volatile_load_nonvol v' H1' _ =>
          rw [H1] at H1'; simp at H1'
  | volatile_load_nonvol v H1 H2 =>
      cases h2 with
      | volatile_load_vol id' ev' v' H1' _ _ =>
          rw [H1] at H1'; simp at H1'
      | volatile_load_nonvol v' _ H2' =>
          refine ⟨.match_traces_E0, fun _ => ?_⟩
          rw [H2] at H2'
          injection H2'

/-- Determinism of `volatile_store` up to trace-matching. -/
theorem volatile_store_determ {ge : Genv.t F V}
    (find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
      Genv.find_symbol ge id2 = some b → id1 = id2)
    {chunk : memory_chunk} {m : mem} {b : block} {ofs : ptrofs} {v : val}
    {t1 : trace} {m1 : mem} {t2 : trace} {m2 : mem}
    (h1 : volatile_store ge chunk m b ofs v t1 m1) (h2 : volatile_store ge chunk m b ofs v t2 m2) :
    match_traces ge t1 t2 ∧ (t1 = t2 → m1 = m2) := by
  cases h1 with
  | volatile_store_vol id ev v H1 H2 H3 =>
      cases h2 with
      | volatile_store_vol id' ev' v' H1' H2' H3' =>
          have hid : id = id' := find_symbol_injective id id' b H2 H2'
          subst hid
          have hev : ev = ev' := eventval_match_determ_2 find_symbol_injective H3 H3'
          subst hev
          exact ⟨.match_traces_vstore chunk id ofs ev, fun _ => rfl⟩
      | volatile_store_nonvol _ _ H1' _ =>
          rw [H1] at H1'; simp at H1'
  | volatile_store_nonvol v m1 H1 H2 =>
      cases h2 with
      | volatile_store_vol id' ev' _ H1' _ _ =>
          rw [H1] at H1'; simp at H1'
      | volatile_store_nonvol _ m2 _ H2' =>
          refine ⟨.match_traces_E0, fun _ => ?_⟩
          rw [H2] at H2'
          injection H2'

/-! ## Semantics of external functions

    Ported from `Events.v`'s generic `extcall_sem` type and `extcall_properties`
    record, reduced to the fields that don't need permissions or memory
    injection/extension (see the design discussion for this section):
    well-typedness, symbol-preservation, bounded trace length, receptiveness,
    and determinism up to trace-matching. Dropped fields (`ec_valid_block`,
    `ec_max_perm`, `ec_readonly`, `ec_mem_extends`, `ec_mem_inject`) all
    fundamentally require `Mem.perm`/`Mem.extends`/`Mem.inject`, none of
    which exist in this memory model (see `docs/MEMORY_DESIGN.md` §3). -/

/-- The behavior of an external function/builtin is defined by a predicate
    relating: the global symbol environment, the arguments, the memory state
    before the call, the trace generated (possibly empty), the result value,
    and the memory state after the call. -/
def extcall_sem (F V : Type) : Type :=
  Genv.t F V → List val → mem → trace → val → mem → Prop

/-- The expected properties of an external-call semantics (leaner version of
    CompCert's `extcall_properties`; see the module comment above). -/
structure extcall_properties {F V : Type} (sem : extcall_sem F V) (sg : signature) : Prop where
  /-- The return value of an external call must agree with its signature. -/
  ec_well_typed :
    ∀ {ge vargs m1 t vres m2}, sem ge vargs m1 t vres m2 → Val.has_rettype vres sg.sig_res
  /-- The semantics is invariant under change of global environment that
      preserves symbols. -/
  ec_symbols_preserved :
    ∀ {ge1 ge2 : Genv.t F V} {vargs : List val} {m1 : mem} {t : trace} {vres : val} {m2 : mem},
      (∀ id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id) →
      (∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) →
      (∀ b, Genv.block_is_volatile ge2 b = Genv.block_is_volatile ge1 b) →
      sem ge1 vargs m1 t vres m2 → sem ge2 vargs m1 t vres m2
  /-- External calls produce at most one event. -/
  ec_trace_length :
    ∀ {ge vargs m t vres m'}, sem ge vargs m t vres m' → t.length ≤ 1
  /-- External calls must be receptive to changes of traces by another,
      matching trace. -/
  ec_receptive :
    ∀ {ge vargs m t1 vres1 m1 t2}, sem ge vargs m t1 vres1 m1 → match_traces ge t1 t2 →
      ∃ vres2 m2, sem ge vargs m t2 vres2 m2
  /-- External calls must be deterministic up to matching between traces.
      Needs `find_symbol` injectivity explicitly (see `volatile_load_determ`
      above) since we split well-formedness out of `Genv.t` into the
      separate `Genv.wf` predicate. -/
  ec_determ :
    ∀ {ge : Genv.t F V}
      (_find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
        Genv.find_symbol ge id2 = some b → id1 = id2)
      {vargs m t1 vres1 m1 t2 vres2 m2},
      sem ge vargs m t1 vres1 m1 → sem ge vargs m t2 vres2 m2 →
      match_traces ge t1 t2 ∧ (t1 = t2 → vres1 = vres2 ∧ m1 = m2)

/-! ### Semantics of volatile loads -/

inductive volatile_load_sem (chunk : memory_chunk) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | volatile_load_sem_intro (b : block) (ofs : ptrofs) (m : mem) (t : trace) (v : val)
      (H : volatile_load ge chunk m b ofs t v) :
      volatile_load_sem chunk ge [.Vptr b ofs] m t v m

theorem volatile_load_ok (chunk : memory_chunk) :
    extcall_properties
      (volatile_load_sem chunk : extcall_sem F V)
      { sig_args := [.Xptr], sig_res := xtype_of_chunk chunk, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h with
    | volatile_load_sem_intro b ofs _ _ _ hv =>
        cases hv with
        | volatile_load_vol id ev v H1 H2 H3 => exact Val.load_result_xtype chunk v
        | volatile_load_nonvol _ H1 H2 =>
            unfold Memory.loadv at H2
            exact Memory.Properties.load_has_rettype H2
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h with
    | volatile_load_sem_intro b ofs _ _ _ hv =>
        exact .volatile_load_sem_intro b ofs m1 t vres (volatile_load_preserved hpub hsym hvol hv)
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h with
    | volatile_load_sem_intro b ofs _ _ _ hv =>
        cases hv with
        | volatile_load_vol _ _ _ _ _ _ => simp
        | volatile_load_nonvol _ _ _ => simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h with
    | volatile_load_sem_intro b ofs _ _ _ hv =>
        obtain ⟨v2, hv2⟩ := volatile_load_receptive hv hm
        exact ⟨v2, m, .volatile_load_sem_intro b ofs m t2 v2 hv2⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1 with
    | volatile_load_sem_intro b ofs _ _ _ hv1 =>
        cases h2 with
        | volatile_load_sem_intro _ _ _ _ _ hv2 =>
            obtain ⟨hmt, hveq⟩ := volatile_load_determ find_symbol_injective hv1 hv2
            exact ⟨hmt, fun heq => ⟨hveq heq, rfl⟩⟩

/-! ### Semantics of volatile stores -/

inductive volatile_store_sem (chunk : memory_chunk) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | volatile_store_sem_intro (b : block) (ofs : ptrofs) (m1 : mem) (v : val) (t : trace) (m2 : mem)
      (H : volatile_store ge chunk m1 b ofs v t m2) :
      volatile_store_sem chunk ge [.Vptr b ofs, v] m1 t .Vundef m2

/-- Safe inversion of `volatile_store_sem` (see `volatile_load_sem_inv`). -/
theorem volatile_store_ok (chunk : memory_chunk) :
    extcall_properties
      (volatile_store_sem chunk : extcall_sem F V)
      { sig_args := [.Xptr, xtype_of_chunk chunk], sig_res := .Xvoid, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h with
    | volatile_store_sem_intro b ofs _ v _ _ hv => trivial
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h with
    | volatile_store_sem_intro b ofs _ v _ _ hv =>
        exact .volatile_store_sem_intro b ofs m1 v t m2 (volatile_store_preserved hpub hsym hvol hv)
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h with
    | volatile_store_sem_intro b ofs _ v _ _ hv =>
        cases hv with
        | volatile_store_vol id ev _ H1 H2 H3 => simp
        | volatile_store_nonvol _ _ H1 H2 => simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h with
    | volatile_store_sem_intro b ofs _ v _ _ hv =>
        have heq := volatile_store_receptive hv hm
        subst heq
        exact ⟨.Vundef, m1, .volatile_store_sem_intro b ofs m v t1 m1 hv⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1 with
    | volatile_store_sem_intro b ofs _ v _ _ hv1 =>
        cases h2 with
        | volatile_store_sem_intro _ _ _ _ _ _ hv2 =>
            obtain ⟨hmt, hm⟩ := volatile_store_determ find_symbol_injective hv1 hv2
            exact ⟨hmt, fun heq => ⟨rfl, hm heq⟩⟩

/-! ## Semantics of dynamic memory allocation (malloc)

    Ported from `Events.v`'s "Semantics of dynamic memory allocation
    (malloc)" section. `malloc` reserves a size header just before the
    returned pointer (at offset `-size_chunk Mptr`), storing the requested
    size there, and returns a pointer to offset 0. -/

inductive extcall_malloc_sem (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | extcall_malloc_sem_intro (sz : ptrofs) (m m' : mem) (b : block) (m'' : mem)
      (H1 : alloc m (-(size_chunk Mptr : Int)) (Ptrofs.unsigned sz) = (b, m'))
      (H2 : store Mptr m' b (-(size_chunk Mptr : Int)) (Vptrofs sz) = some m'') :
      extcall_malloc_sem ge [Vptrofs sz] m E0 (.Vptr b Ptrofs.zero) m''

/-- Safe inversion of `extcall_malloc_sem`. Needed because `vargs` is
    `[Vptrofs sz]` for an opaque (`Archi.ptr64`-guarded) `Vptrofs`, so once
    one hypothesis has already pinned `vargs` to a concrete `Vptrofs sz`
    term, `cases`-ing a *second* such hypothesis against it hits the same
    dependent-elimination obstacle as `Tptr` in Block 2 — Lean cannot decide
    `Vptrofs sz = Vptrofs sz'` without knowing `Archi.ptr64` concretely.
    Applying this lemma to each hypothesis independently (each a safe,
    single-hypothesis `cases`) sidesteps that, so `Vptrofs_inj` can be used
    on the resulting *plain* propositional equality instead. -/
theorem extcall_malloc_sem_inv {ge : Genv.t F V} {vargs : List val} {m1 : mem} {t : trace}
    {vres : val} {m2 : mem} (h : extcall_malloc_sem ge vargs m1 t vres m2) :
    ∃ sz b m', vargs = [Vptrofs sz] ∧ t = E0 ∧ vres = .Vptr b Ptrofs.zero ∧
      alloc m1 (-(size_chunk Mptr : Int)) (Ptrofs.unsigned sz) = (b, m') ∧
      store Mptr m' b (-(size_chunk Mptr : Int)) (Vptrofs sz) = some m2 := by
  cases h with
  | extcall_malloc_sem_intro sz _ m' b _ H1 H2 => exact ⟨sz, b, m', rfl, rfl, rfl, H1, H2⟩

theorem extcall_malloc_ok :
    extcall_properties
      (extcall_malloc_sem : extcall_sem F V)
      { sig_args := [Xsize_t], sig_res := .Xptr, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h with
    | extcall_malloc_sem_intro sz _ _ b _ _ _ => trivial
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h with
    | extcall_malloc_sem_intro sz _ m' b _ H1 H2 =>
        exact .extcall_malloc_sem_intro sz m1 m' b m2 H1 H2
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h with
    | extcall_malloc_sem_intro _ _ _ _ _ _ _ => simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    obtain ⟨sz, b, m', _, ht1, _, _, _⟩ := extcall_malloc_sem_inv h
    subst ht1
    cases hm with
    | match_traces_E0 => exact ⟨vres1, m1, h⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    obtain ⟨sz1, b1, m1', ha1, ht1, hv1, hA1, hB1⟩ := extcall_malloc_sem_inv h1
    obtain ⟨sz2, b2, m2', ha2, ht2, hv2, hA2, hB2⟩ := extcall_malloc_sem_inv h2
    rw [ha1] at ha2
    have hsz : sz1 = sz2 := Val.Vptrofs_inj (by injection ha2)
    subst hsz
    rw [hA1] at hA2
    obtain ⟨hb, hm'⟩ := Prod.mk.injEq .. |>.mp hA2
    subst hb; subst hm'
    rw [hB1] at hB2
    injection hB2 with hm2
    subst ht1; subst ht2
    refine ⟨.match_traces_E0, fun _ => ⟨?_, hm2⟩⟩
    rw [hv1, hv2]

/-! ## Semantics of dynamic memory deallocation (free)

    Ported from `Events.v`'s "Semantics of dynamic memory deallocation
    (free)" section. Freeing a non-null pointer loads the size back out of
    the header written by `malloc`, then frees the full `[header, data)`
    range; freeing a null pointer is a no-op (matches C's `free(NULL)`). -/

inductive extcall_free_sem (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | extcall_free_sem_ptr (b : block) (lo sz : ptrofs) (m m' : mem)
      (H1 : load Mptr m b (Ptrofs.unsigned lo - (size_chunk Mptr : Int)) = some (Vptrofs sz))
      (H2 : free m b (Ptrofs.unsigned lo - (size_chunk Mptr : Int))
              (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = some m') :
      extcall_free_sem ge [.Vptr b lo] m E0 .Vundef m'
  | extcall_free_sem_null (m : mem) :
      extcall_free_sem ge [Vnullptr] m E0 .Vundef m

/-- Safe inversion of `extcall_free_sem` (see `extcall_malloc_sem_inv`) —
    needed both for the opaque `Vptrofs` wrapper (as with malloc) and
    because `Vnullptr` is itself an `Archi.ptr64`-guarded opaque term. -/
theorem extcall_free_sem_inv {ge : Genv.t F V} {vargs : List val} {m1 : mem} {t : trace}
    {vres : val} {m2 : mem} (h : extcall_free_sem ge vargs m1 t vres m2) :
    (∃ b lo sz, vargs = [.Vptr b lo] ∧ t = E0 ∧ vres = .Vundef ∧
      load Mptr m1 b (Ptrofs.unsigned lo - (size_chunk Mptr : Int)) = some (Vptrofs sz) ∧
      free m1 b (Ptrofs.unsigned lo - (size_chunk Mptr : Int))
        (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = some m2) ∨
    (vargs = [Vnullptr] ∧ t = E0 ∧ vres = .Vundef ∧ m2 = m1) := by
  cases h with
  | extcall_free_sem_ptr b lo sz _ _ H1 H2 => exact .inl ⟨b, lo, sz, rfl, rfl, rfl, H1, H2⟩
  | extcall_free_sem_null _ => exact .inr ⟨rfl, rfl, rfl, rfl⟩

/-- `Vptr _ _` is never `Vnullptr`, regardless of `Archi.ptr64`. -/
theorem Vptr_ne_Vnullptr {b : block} {ofs : ptrofs} : (val.Vptr b ofs) ≠ Vnullptr := by
  unfold Vnullptr; by_cases hp : Archi.ptr64 <;> simp [hp]

theorem extcall_free_ok :
    extcall_properties
      (extcall_free_sem : extcall_sem F V)
      { sig_args := [.Xptr], sig_res := .Xvoid, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    rcases extcall_free_sem_inv h with ⟨_, _, _, _, _, hv, _, _⟩ | ⟨_, _, hv, _⟩ <;>
      (rw [hv]; trivial)
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    rcases extcall_free_sem_inv h with ⟨b, lo, sz, ha, ht, hv, H1, H2⟩ | ⟨ha, ht, hv, hm⟩
    · rw [ha, ht, hv]
      exact .extcall_free_sem_ptr b lo sz m1 m2 H1 H2
    · rw [ha, ht, hv, hm]
      exact .extcall_free_sem_null m1
  ec_trace_length := by
    intro ge vargs m t vres m' h
    rcases extcall_free_sem_inv h with ⟨_, _, _, _, ht, _, _, _⟩ | ⟨_, ht, _, _⟩ <;>
      (rw [ht]; simp [E0])
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    rcases extcall_free_sem_inv h with ⟨_, _, _, _, ht1, _, _, _⟩ | ⟨_, ht1, _, _⟩ <;>
      · subst ht1
        cases hm with
        | match_traces_E0 => exact ⟨vres1, m1, h⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    rcases extcall_free_sem_inv h1 with
      ⟨b1, lo1, sz1, ha1, ht1, hv1, H11, H21⟩ | ⟨ha1, ht1, hv1, hm1⟩ <;>
    rcases extcall_free_sem_inv h2 with
      ⟨b2, lo2, sz2, ha2, ht2, hv2, H12, H22⟩ | ⟨ha2, ht2, hv2, hm2⟩
    · -- ptr, ptr
      rw [ha1] at ha2
      injection ha2 with hp
      injection hp with hb hlo
      subst hb; subst hlo
      rw [H11] at H12
      injection H12 with hsz
      have hsz' : sz1 = sz2 := Val.Vptrofs_inj hsz
      subst hsz'
      rw [H21] at H22
      injection H22 with hm2eq
      subst ht1; subst ht2
      exact ⟨.match_traces_E0, fun _ => ⟨by rw [hv1, hv2], hm2eq⟩⟩
    · -- ptr, null
      rw [ha1] at ha2
      injection ha2 with hp
      exact absurd hp Vptr_ne_Vnullptr
    · -- null, ptr
      rw [ha1] at ha2
      injection ha2 with hp
      exact absurd hp.symm Vptr_ne_Vnullptr
    · -- null, null
      subst ht1; subst ht2
      exact ⟨.match_traces_E0, fun _ => ⟨by rw [hv1, hv2], by rw [hm1, hm2]⟩⟩

/-! ## Semantics of `memcpy` operations

    Ported from `Events.v`'s "Semantics of [memcpy] operations" section. -/

inductive extcall_memcpy_sem (sz al : Int) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | extcall_memcpy_sem_intro (bdst : block) (odst : ptrofs) (bsrc : block) (osrc : ptrofs)
      (m : mem) (bytes : List Memory.memval) (m' : mem)
      (Hal : al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8) (Hsz : sz ≥ 0) (Hdvd : al ∣ sz)
      (Hasrc : sz > 0 → al ∣ Ptrofs.unsigned osrc)
      (Hadst : sz > 0 → al ∣ Ptrofs.unsigned odst)
      (Hdisjoint : bsrc ≠ bdst ∨ Ptrofs.unsigned osrc = Ptrofs.unsigned odst ∨
                   Ptrofs.unsigned osrc + sz ≤ Ptrofs.unsigned odst ∨
                   Ptrofs.unsigned odst + sz ≤ Ptrofs.unsigned osrc)
      (Hload : loadbytes m bsrc (Ptrofs.unsigned osrc) sz = some bytes)
      (Hstore : storebytes m bdst (Ptrofs.unsigned odst) bytes = some m') :
      extcall_memcpy_sem sz al ge [.Vptr bdst odst, .Vptr bsrc osrc] m E0 .Vundef m'

theorem extcall_memcpy_ok (sz al : Int) :
    extcall_properties
      (extcall_memcpy_sem sz al : extcall_sem F V)
      { sig_args := [.Xptr, .Xptr], sig_res := .Xvoid, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h with
    | extcall_memcpy_sem_intro bdst odst bsrc osrc _ _ _ _ _ _ _ _ _ _ => trivial
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h with
    | extcall_memcpy_sem_intro bdst odst bsrc osrc _ bytes _ Hal Hsz Hdvd Hasrc Hadst
        Hdisjoint Hload Hstore =>
        exact .extcall_memcpy_sem_intro bdst odst bsrc osrc m1 bytes m2
          Hal Hsz Hdvd Hasrc Hadst Hdisjoint Hload Hstore
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h with
    | extcall_memcpy_sem_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h with
    | extcall_memcpy_sem_intro bdst odst bsrc osrc _ bytes _ Hal Hsz Hdvd Hasrc Hadst
        Hdisjoint Hload Hstore =>
        cases hm with
        | match_traces_E0 =>
            exact ⟨.Vundef, m1, .extcall_memcpy_sem_intro bdst odst bsrc osrc m bytes m1
              Hal Hsz Hdvd Hasrc Hadst Hdisjoint Hload Hstore⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1 with
    | extcall_memcpy_sem_intro bdst odst bsrc osrc _ bytes _ _ _ _ _ _ _ Hload1 Hstore1 =>
        cases h2 with
        | extcall_memcpy_sem_intro _ _ _ _ _ bytes' _ _ _ _ _ _ _ Hload2 Hstore2 =>
            rw [Hload1] at Hload2
            injection Hload2 with hbytes
            subst hbytes
            rw [Hstore1] at Hstore2
            injection Hstore2 with hm2
            exact ⟨.match_traces_E0, fun _ => ⟨rfl, hm2⟩⟩

/-! ## Semantics of annotations

    Ported from `Events.v`'s "Semantics of annotations" section. -/

inductive extcall_annot_sem (text : String) (targs : List typ) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | extcall_annot_sem_intro (vargs : List val) (m : mem) (args : List eventval)
      (H : eventval_list_match ge args targs vargs) :
      extcall_annot_sem text targs ge vargs m (.Event_annot text args :: E0) .Vundef m

theorem extcall_annot_ok (text : String) (targs : List typ) :
    extcall_properties
      (extcall_annot_sem text targs : extcall_sem F V)
      { sig_args := targs.map inj_type, sig_res := .Xvoid, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h
    trivial
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h
    rename_i args H
    exact .extcall_annot_sem_intro vargs m1 args (eventval_list_match_preserved hpub hsym H)
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h
    simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h
    rename_i args H
    cases hm
    exact ⟨.Vundef, m, .extcall_annot_sem_intro vargs m args H⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1
    rename_i args1 H1
    cases h2
    rename_i args2 H2
    have heq : args1 = args2 := eventval_list_match_determ_2 find_symbol_injective H1 H2
    subst heq
    exact ⟨.match_traces_annot text args1, fun _ => ⟨rfl, rfl⟩⟩

inductive extcall_annot_val_sem (text : String) (targ : typ) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | extcall_annot_val_sem_intro (varg : val) (m : mem) (arg : eventval)
      (H : eventval_match ge arg targ varg) :
      extcall_annot_val_sem text targ ge [varg] m (.Event_annot text [arg] :: E0) varg m

theorem extcall_annot_val_ok (text : String) (targ : typ) :
    extcall_properties
      (extcall_annot_val_sem text targ : extcall_sem F V)
      { sig_args := [inj_type targ], sig_res := inj_type targ, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h
    rename_i arg H
    exact Val.has_inj_type vres targ (eventval_match_type H)
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h
    rename_i arg H
    exact .extcall_annot_val_sem_intro vres m1 arg (eventval_match_preserved hpub hsym H)
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h
    simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h
    rename_i arg H
    cases hm
    exact ⟨vres1, m, .extcall_annot_val_sem_intro vres1 m arg H⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1
    rename_i arg1 H1
    cases h2
    rename_i arg2 H2
    have heq : arg1 = arg2 := eventval_match_determ_2 find_symbol_injective H1 H2
    subst heq
    exact ⟨.match_traces_annot text [arg1], fun _ => ⟨rfl, rfl⟩⟩

inductive extcall_debug_sem (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | extcall_debug_sem_intro (vargs : List val) (m : mem) :
      extcall_debug_sem ge vargs m E0 .Vundef m

theorem extcall_debug_ok (targs : List typ) :
    extcall_properties
      (extcall_debug_sem : extcall_sem F V)
      { sig_args := targs.map inj_type, sig_res := .Xvoid, sig_cc := cc_default } where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h
    trivial
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h
    exact .extcall_debug_sem_intro vargs m1
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h
    simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h
    cases hm
    exact ⟨.Vundef, m, .extcall_debug_sem_intro vargs m⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1
    cases h2
    exact ⟨.match_traces_E0, fun _ => ⟨rfl, rfl⟩⟩

/-! ## Semantics of known built-in functions

    Ported from `Events.v`'s "Semantics of known built-in functions" section.
    Some built-ins and runtime-support functions have known semantics, as
    defined in `Builtins.lean`; they have no observable effects and do not
    access memory. -/

variable [Builtins1.PlatformBuiltins]

inductive known_builtin_sem (bf : Builtins.builtin_function) (ge : Genv.t F V) :
    List val → mem → trace → val → mem → Prop where
  | known_builtin_sem_intro (vargs : List val) (vres : val) (m : mem)
      (H : Builtins.builtin_function_sem bf vargs = some vres) :
      known_builtin_sem bf ge vargs m E0 vres m

theorem known_builtin_ok (bf : Builtins.builtin_function) :
    extcall_properties
      (known_builtin_sem bf : extcall_sem F V)
      (Builtins.builtin_function_sig bf) where
  ec_well_typed := by
    intro ge vargs m1 t vres m2 h
    cases h
    rename_i H
    have hwt := (Builtins.builtin_function_sem bf).bs_well_typed vargs
    rw [H] at hwt
    exact hwt
  ec_symbols_preserved := by
    intro ge1 ge2 vargs m1 t vres m2 hpub hsym hvol h
    cases h
    rename_i H
    exact .known_builtin_sem_intro vargs vres m1 H
  ec_trace_length := by
    intro ge vargs m t vres m' h
    cases h
    rename_i H
    simp [E0]
  ec_receptive := by
    intro ge vargs m t1 vres1 m1 t2 h hm
    cases h
    rename_i H
    cases hm
    exact ⟨vres1, m, .known_builtin_sem_intro vargs vres1 m H⟩
  ec_determ := by
    intro ge find_symbol_injective vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1
    rename_i H1
    cases h2
    rename_i H2
    rw [H1] at H2
    injection H2 with hv
    exact ⟨.match_traces_E0, fun _ => ⟨hv, rfl⟩⟩

/-! ## Semantics of external functions

    Ported from `Events.v`'s "Semantics of external functions" section.
    Functions defined outside the program (`EF_external`) and inline
    assembly (`EF_inline_asm`) are treated opaquely: CompCert's own source
    leaves their semantics *assumed*, not defined, via a bare
    `Parameter`/`Axiom` pair, because the compiler correctness proof must
    hold no matter what these actually do at runtime. This is the one place
    in this port where an `axiom` is the faithful translation (rather than a
    deviation to avoid) — it matches CompCert's own choice to leave these two
    families of `external_function` unspecified. -/

axiom external_functions_sem : String → signature → extcall_sem F V

axiom external_functions_properties (id : String) (sg : signature) :
    extcall_properties (external_functions_sem id sg : extcall_sem F V) sg

/-- We treat inline assembly similarly. -/
axiom inline_assembly_sem : String → signature → extcall_sem F V

axiom inline_assembly_properties (id : String) (sg : signature) :
    extcall_properties (inline_assembly_sem id sg : extcall_sem F V) sg

/-! ## Combined semantics of external calls -/

def builtin_or_external_sem (name : String) (sg : signature) : extcall_sem F V :=
  match Builtins.lookup_builtin_function name sg with
  | some bf => known_builtin_sem bf
  | none => external_functions_sem name sg

theorem builtin_or_external_sem_ok (name : String) (sg : signature) :
    extcall_properties (builtin_or_external_sem name sg : extcall_sem F V) sg := by
  show extcall_properties
    (match Builtins.lookup_builtin_function name sg with
      | some bf => (known_builtin_sem bf : extcall_sem F V)
      | none => external_functions_sem name sg) sg
  split
  · rename_i bf hL
    rw [← Builtins.lookup_builtin_function_sig hL]
    exact known_builtin_ok bf
  · rename_i hL
    exact external_functions_properties name sg

/-- Combining the semantics given above for the various kinds of external
    calls, `external_call` relates: the external function being invoked, the
    values of the arguments passed to it, the memory state before the call,
    the result value of the call, the memory state after the call, and the
    trace generated by the call (possibly empty). This predicate is used in
    the semantics of all languages in this port. -/
def external_call (ef : external_function) : extcall_sem F V :=
  match ef with
  | .EF_external name sg => external_functions_sem name sg
  | .EF_builtin name sg => builtin_or_external_sem name sg
  | .EF_runtime name sg => builtin_or_external_sem name sg
  | .EF_vload chunk => volatile_load_sem chunk
  | .EF_vstore chunk => volatile_store_sem chunk
  | .EF_malloc => extcall_malloc_sem
  | .EF_free => extcall_free_sem
  | .EF_memcpy sz al => extcall_memcpy_sem sz al
  | .EF_annot _kind txt targs => extcall_annot_sem txt targs
  | .EF_annot_val _kind txt targ => extcall_annot_val_sem txt targ
  | .EF_inline_asm txt sg _clobbers => inline_assembly_sem txt sg
  | .EF_debug _kind _txt _targs => extcall_debug_sem

theorem external_call_spec (ef : external_function) :
    extcall_properties (external_call ef : extcall_sem F V) (ef_sig ef) := by
  cases ef with
  | EF_external name sg => exact external_functions_properties name sg
  | EF_builtin name sg => exact builtin_or_external_sem_ok name sg
  | EF_runtime name sg => exact builtin_or_external_sem_ok name sg
  | EF_vload chunk => exact volatile_load_ok chunk
  | EF_vstore chunk => exact volatile_store_ok chunk
  | EF_malloc => exact extcall_malloc_ok
  | EF_free => exact extcall_free_ok
  | EF_memcpy sz al => exact extcall_memcpy_ok sz al
  | EF_annot kind txt targs => exact extcall_annot_ok txt targs
  | EF_annot_val kind txt targ => exact extcall_annot_val_ok txt targ
  | EF_inline_asm txt sg clobbers => exact inline_assembly_properties txt sg
  | EF_debug kind txt targs => exact extcall_debug_ok targs

/-! ### Corollaries of `external_call_spec`

    Kept: direct consequences of `ec_well_typed`/`ec_determ`. Dropped (as
    elsewhere in this file): `external_call_nextblock` (needs
    `ec_valid_block`), `external_call_mem_inject` and
    `meminj_preserves_globals` (need `ec_mem_inject`) — all
    permission/injection-dependent, out of scope per `docs/MEMORY_DESIGN.md`
    §3. -/

theorem external_call_well_typed {ef : external_function} {ge : Genv.t F V} {vargs : List val}
    {m1 : mem} {t : trace} {vres : val} {m2 : mem}
    (h : external_call ef ge vargs m1 t vres m2) :
    Val.has_type vres (proj_sig_res (ef_sig ef)) :=
  Val.has_proj_xtype vres _ ((external_call_spec ef).ec_well_typed h)

theorem external_call_match_traces {ef : external_function} {ge : Genv.t F V} {vargs : List val}
    {m : mem} {t1 : trace} {vres1 : val} {m1 : mem} {t2 : trace} {vres2 : val} {m2 : mem}
    (find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
      Genv.find_symbol ge id2 = some b → id1 = id2)
    (h1 : external_call ef ge vargs m t1 vres1 m1)
    (h2 : external_call ef ge vargs m t2 vres2 m2) :
    match_traces ge t1 t2 :=
  ((external_call_spec ef).ec_determ find_symbol_injective h1 h2).1

theorem external_call_deterministic {ef : external_function} {ge : Genv.t F V} {vargs : List val}
    {m : mem} {t : trace} {vres1 : val} {m1 : mem} {vres2 : val} {m2 : mem}
    (find_symbol_injective : ∀ id1 id2 b, Genv.find_symbol ge id1 = some b →
      Genv.find_symbol ge id2 = some b → id1 = id2)
    (h1 : external_call ef ge vargs m t vres1 m1)
    (h2 : external_call ef ge vargs m t vres2 m2) :
    vres1 = vres2 ∧ m1 = m2 :=
  ((external_call_spec ef).ec_determ find_symbol_injective h1 h2).2 rfl

end Events
