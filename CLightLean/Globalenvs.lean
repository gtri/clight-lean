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

/- Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. -/

import CLightLean.AST
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats
import CLightLean.Values
import CLightLean.Memory
import CLightLean.Archi

variable [Archi]

open Memory (mem store unchanged_on loadbytes encode_val size_chunk align_chunk valid_pointer)
open Memory.Properties (unchanged_on_refl unchanged_on_trans store_unchanged_on)

/-- Auxiliary function for initialization of global variables.
    Stores `n` zero bytes starting at position `p` in block `b`. -/
def store_zeros (m : mem) (b : block) (p : Int) (n : Int) : Option mem :=
  if n ≤ 0 then
    some m
  else
    match store .Mint8unsigned m b p Vzero with
    | some m' => store_zeros m' b (p + 1) (n - 1)
    | none => none
termination_by n.toNat
decreasing_by omega

-- * Global environments

namespace Genv

/-- The type of global environments, parameterized by the type of function
    descriptions `F` and the type of information attached to variables `V`.

    Unlike CompCert's dependent record (which bakes well-formedness proofs
    directly into the structure), we keep `t` as plain data and track
    well-formedness via the separate `Genv.wf` predicate below. This mirrors
    the `mem` / `mem_wf` split in Memory.lean: `Genv.t` is built incrementally
    (via a fold over `prog_defs`), and baking proofs into the structure would
    force every incremental step to carry an inline preservation proof. -/
structure t (F V : Type) : Type where
  genv_public : List ident                            -- which symbol names are public
  genv_symb : Std.HashMap ident block           -- mapping symbol -> block
  genv_defs : Std.HashMap block (globdef F V)   -- mapping block -> definition
  genv_next : block                             -- next symbol pointer

/-- Well-formedness invariant for global environments (mirrors `Memory.mem_wf`).
    - Every symbol maps to a block below `genv_next`.
    - Every defined block is below `genv_next`.
    - The symbol table is injective (no two names map to the same block). -/
def wf {F V : Type} (ge : t F V) : Prop :=
  (∀ id b, ge.genv_symb.get? id = some b → b < ge.genv_next) ∧
  (∀ b g, ge.genv_defs.get? b = some g → b < ge.genv_next) ∧
  (∀ id1 id2 b, ge.genv_symb.get? id1 = some b → ge.genv_symb.get? id2 = some b → id1 = id2)

variable {F V : Type}

-- ** Lookup functions

/-- [find_symbol ge id] returns the block associated with the given name, if any. -/
def find_symbol (ge : t F V) (id : ident) : Option block :=
  ge.genv_symb.get? id

/-- [symbol_address ge id ofs] returns a pointer into the block associated
    with [id], at byte offset [ofs].  [Vundef] is returned if no block is
    associated to [id]. -/
def symbol_address (ge : t F V) (id : ident) (ofs : ptrofs) : val :=
  match find_symbol ge id with
  | some b => .Vptr b ofs
  | none => .Vundef

/-- [public_symbol ge id] says whether the name [id] is public and defined. -/
def public_symbol (ge : t F V) (id : ident) : Bool :=
  match find_symbol ge id with
  | none => false
  | some _ => ge.genv_public.contains id

/-- [find_def ge b] returns the global definition associated with the given address. -/
def find_def (ge : t F V) (b : block) : Option (globdef F V) :=
  ge.genv_defs.get? b

/-- [find_funct_ptr ge b] returns the function description associated with
    the given address. -/
def find_funct_ptr (ge : t F V) (b : block) : Option F :=
  match find_def ge b with
  | some (.Gfun f) => some f
  | _ => none

/-- [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. -/
def find_funct (ge : t F V) (v : val) : Option F :=
  match v with
  | .Vptr b ofs => if ofs = Ptrofs.zero then find_funct_ptr ge b else none
  | _ => none

/-- [invert_symbol ge b] returns the name associated with the given block, if any. -/
def invert_symbol (ge : t F V) (b : block) : Option ident :=
  ge.genv_symb.fold (fun res id b' => if b == b' then some id else res) none

/-- [find_var_info ge b] returns the information attached to the variable
    at address [b]. -/
def find_var_info (ge : t F V) (b : block) : Option (globvar V) :=
  match find_def ge b with
  | some (.Gvar v) => some v
  | _ => none

/-- [block_is_volatile ge b] returns [true] if [b] points to a global variable
    of volatile type, [false] otherwise. -/
def block_is_volatile (ge : t F V) (b : block) : Bool :=
  match find_var_info ge b with
  | none => false
  | some gv => gv.gvar_volatile

-- ** Constructing the global environment

/-- Add a global definition to the environment: bind its identifier to the
    next fresh block, record the definition at that block, and advance
    `genv_next`.

    Note: CompCert uses a dependent `Program Definition` here with three
    inline obligation proofs (that `wf`'s three invariants are preserved
    by the update). Since our `t` carries no embedded proofs, `add_global`
    is just a plain record update; the corresponding preservation fact is
    proved separately as `add_global_wf` below (this is exactly the kind of
    incremental-step proof burden the plain-struct design was meant to avoid). -/
def add_global (ge : t F V) (idg : ident × globdef F V) : t F V :=
  { genv_public := ge.genv_public
    genv_symb := ge.genv_symb.insert idg.1 ge.genv_next
    genv_defs := ge.genv_defs.insert ge.genv_next idg.2
    genv_next := ge.genv_next + 1 }

/-- `add_global` preserves well-formedness (combines the three proof
    obligations from CompCert's `Program Definition add_global`). -/
theorem add_global_wf (ge : t F V) (idg : ident × globdef F V) (h : wf ge) :
    wf (add_global ge idg) := by
  obtain ⟨hsymb, hdefs, hinj⟩ := h
  unfold add_global
  refine ⟨?_, ?_, ?_⟩
  · intro id b hb
    simp only at hb
    rw [Std.HashMap.get?_insert] at hb
    split at hb
    · injection hb with hb
      subst hb
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hsymb id b hb)
  · intro b g hg
    simp only at hg
    rw [Std.HashMap.get?_insert] at hg
    split at hg
    · rename_i hcond
      rw [beq_iff_eq] at hcond
      subst hcond
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hdefs b g hg)
  · intro id1 id2 b hb1 hb2
    simp only at hb1 hb2
    rw [Std.HashMap.get?_insert] at hb1 hb2
    split at hb1 <;> split at hb2
    · rename_i h1 h2
      rw [beq_iff_eq] at h1 h2
      exact h1.symm.trans h2
    · rename_i h1 _
      exfalso
      rw [beq_iff_eq] at h1
      injection hb1 with hb1
      subst h1; subst hb1
      exact Nat.lt_irrefl _ (hsymb id2 ge.genv_next hb2)
    · rename_i _ h2
      exfalso
      rw [beq_iff_eq] at h2
      injection hb2 with hb2
      subst h2; subst hb2
      exact Nat.lt_irrefl _ (hsymb id1 ge.genv_next hb1)
    · exact hinj id1 id2 b hb1 hb2

/-- Add a list of global definitions, left to right. -/
def add_globals (ge : t F V) (gl : List (ident × globdef F V)) : t F V :=
  gl.foldl add_global ge

theorem add_globals_app (gl1 gl2 : List (ident × globdef F V)) (ge : t F V) :
    add_globals ge (gl1 ++ gl2) = add_globals (add_globals ge gl1) gl2 := by
  unfold add_globals
  exact List.foldl_append

/-- The empty global environment, with only the given public names, no
    symbols or definitions yet, and `genv_next` starting at block 1
    (block 0 is reserved as invalid, matching `Memory.lean`'s convention). -/
def empty_genv (pub : List ident) : t F V :=
  { genv_public := pub
    genv_symb := ∅
    genv_defs := ∅
    genv_next := 1 }

theorem empty_genv_wf (pub : List ident) : wf (empty_genv pub : t F V) := by
  simp [wf, empty_genv]

/-- Build the global environment for a whole program. -/
def globalenv (p : program F V) : t F V :=
  add_globals (empty_genv p.prog_public) p.prog_defs

-- Proof principles

section GLOBALENV_PRINCIPLES

variable {P : t F V → Prop}

theorem add_globals_preserves
    (gl : List (ident × globdef F V)) (ge : t F V)
    (h : ∀ ge' id g, P ge' → (id, g) ∈ gl → P (add_global ge' (id, g)))
    (hge : P ge) : P (add_globals ge gl) := by
  suffices H : ∀ gl ge, (∀ ge' id g, P ge' → (id, g) ∈ gl → P (add_global ge' (id, g))) →
      P ge → P (add_globals ge gl) by exact H gl ge h hge
  intro gl
  induction gl with
  | nil => intro ge _ hge; exact hge
  | cons a gl' ih =>
      intro ge h hge
      obtain ⟨id, g⟩ := a
      unfold add_globals
      rw [List.foldl_cons]
      apply ih
      · intro ge' id' g' hP hmem
        exact h ge' id' g' hP (List.mem_cons_of_mem _ hmem)
      · exact h ge id g hge List.mem_cons_self

theorem add_globals_ensures
    (id : ident) (g : globdef F V) (gl : List (ident × globdef F V)) (ge : t F V)
    (h1 : ∀ ge' id' g', P ge' → (id', g') ∈ gl → P (add_global ge' (id', g')))
    (h2 : ∀ ge', P (add_global ge' (id, g)))
    (hin : (id, g) ∈ gl) : P (add_globals ge gl) := by
  suffices H : ∀ gl ge, (∀ ge' id' g', P ge' → (id', g') ∈ gl → P (add_global ge' (id', g'))) →
      (id, g) ∈ gl → P (add_globals ge gl) by exact H gl ge h1 hin
  intro gl
  induction gl with
  | nil => intro ge _ hin; simp at hin
  | cons a gl' ih =>
      intro ge h1 hin
      unfold add_globals
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hin with heq | hmem
      · apply add_globals_preserves gl' (add_global ge a)
        · intro ge' id' g' hP hmem'
          exact h1 ge' id' g' hP (List.mem_cons_of_mem _ hmem')
        · rw [← heq]; exact h2 ge
      · apply ih (add_global ge a)
        · intro ge' id' g' hP hmem'
          exact h1 ge' id' g' hP (List.mem_cons_of_mem _ hmem')
        · exact hmem

theorem add_globals_unique_preserves
    (id : ident) (gl : List (ident × globdef F V)) (ge : t F V)
    (h : ∀ ge' id1 g, P ge' → (id1, g) ∈ gl → id1 ≠ id → P (add_global ge' (id1, g)))
    (hnotin : id ∉ gl.map Prod.fst) (hge : P ge) : P (add_globals ge gl) := by
  suffices H : ∀ gl ge, (∀ ge' id1 g, P ge' → (id1, g) ∈ gl → id1 ≠ id →
      P (add_global ge' (id1, g))) → id ∉ gl.map Prod.fst → P ge → P (add_globals ge gl) by
    exact H gl ge h hnotin hge
  intro gl
  induction gl with
  | nil => intro ge _ _ hge; exact hge
  | cons a gl' ih =>
      intro ge h hnotin hge
      obtain ⟨id1, g⟩ := a
      simp only [List.map_cons, List.mem_cons] at hnotin
      apply ih (add_global ge (id1, g))
      · intro ge' id1' g' hP hmem' hne
        exact h ge' id1' g' hP (List.mem_cons_of_mem _ hmem') hne
      · exact (not_or.mp hnotin).2
      · exact h ge id1 g hge List.mem_cons_self (Ne.symm (not_or.mp hnotin).1)

theorem add_globals_unique_ensures
    (gl1 : List (ident × globdef F V)) (id : ident) (g : globdef F V)
    (gl2 : List (ident × globdef F V)) (ge : t F V)
    (h1 : ∀ ge' id1 g1, P ge' → (id1, g1) ∈ gl2 → id1 ≠ id → P (add_global ge' (id1, g1)))
    (h2 : ∀ ge', P (add_global ge' (id, g)))
    (hnotin : id ∉ gl2.map Prod.fst) :
    P (add_globals ge (gl1 ++ (id, g) :: gl2)) := by
  rw [add_globals_app]
  unfold add_globals
  rw [List.foldl_cons]
  apply add_globals_unique_preserves id gl2 (add_global (add_globals ge gl1) (id, g))
  · exact h1
  · exact hnotin
  · exact h2 (add_globals ge gl1)

/-- (Does not depend on `P`; purely a list-structure fact.) -/
theorem in_norepet_unique
    (id : ident) (g : globdef F V) (gl : List (ident × globdef F V))
    (hin : (id, g) ∈ gl) (hnodup : (gl.map Prod.fst).Nodup) :
    ∃ gl1 gl2, gl = gl1 ++ (id, g) :: gl2 ∧ id ∉ gl2.map Prod.fst := by
  induction gl with
  | nil => simp at hin
  | cons a gl' ih =>
      obtain ⟨id1, g1⟩ := a
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hin with heq | hmem
      · injection heq with heq1 heq2
        subst heq1; subst heq2
        exact ⟨[], gl', rfl, hnodup.1⟩
      · obtain ⟨gl1, gl2, heqgl, hnotin⟩ := ih hmem hnodup.2
        exact ⟨(id1, g1) :: gl1, gl2, by rw [heqgl, List.cons_append], hnotin⟩

theorem add_globals_norepet_ensures
    (id : ident) (g : globdef F V) (gl : List (ident × globdef F V)) (ge : t F V)
    (h1 : ∀ ge' id1 g1, P ge' → (id1, g1) ∈ gl → id1 ≠ id → P (add_global ge' (id1, g1)))
    (h2 : ∀ ge', P (add_global ge' (id, g)))
    (hin : (id, g) ∈ gl) (hnodup : (gl.map Prod.fst).Nodup) :
    P (add_globals ge gl) := by
  obtain ⟨gl1, gl2, heqgl, hnotin⟩ := in_norepet_unique id g gl hin hnodup
  subst heqgl
  apply add_globals_unique_ensures gl1 id g gl2 ge
  · intro ge' id1 g1 hP hmem hne
    exact h1 ge' id1 g1 hP (List.mem_append_right gl1 (List.mem_cons_of_mem _ hmem)) hne
  · exact h2
  · exact hnotin

end GLOBALENV_PRINCIPLES

-- ** Properties of the operations over global environments

theorem public_symbol_exists (ge : t F V) (id : ident) (h : public_symbol ge id = true) :
    ∃ b, find_symbol ge id = some b := by
  unfold public_symbol at h
  cases hf : find_symbol ge id with
  | none => rw [hf] at h; simp at h
  | some b => exact ⟨b, rfl⟩

theorem shift_symbol_address (ge : t F V) (id : ident) (ofs delta : ptrofs) :
    symbol_address ge id (Ptrofs.add ofs delta) = Val.offset_ptr (symbol_address ge id ofs) delta := by
  unfold symbol_address
  cases find_symbol ge id with
  | some b => rfl
  | none => rfl

theorem shift_symbol_address_32 (ge : t F V) (id : ident) (ofs : ptrofs) (n : CompCert.Int)
    (h : Archi.ptr64 = false) :
    symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) =
      Val.add (symbol_address ge id ofs) (.Vint n) := by
  unfold symbol_address
  cases find_symbol ge id with
  | some b => simp [Val.add, h]
  | none => rfl

theorem shift_symbol_address_64 (ge : t F V) (id : ident) (ofs : ptrofs) (n : CompCert.Int64)
    (h : Archi.ptr64 = true) :
    symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) =
      Val.addl (symbol_address ge id ofs) (.Vlong n) := by
  unfold symbol_address
  cases find_symbol ge id with
  | some b => simp [Val.addl, h]
  | none => rfl

theorem find_funct_inv (ge : t F V) (v : val) (f : F) (h : find_funct ge v = some f) :
    ∃ b, v = .Vptr b Ptrofs.zero := by
  cases v with
  | Vptr b ofs =>
      unfold find_funct at h
      simp only at h
      split at h
      · rename_i heq
        exact ⟨b, by rw [heq]⟩
      · simp at h
  | _ => unfold find_funct at h; simp at h

theorem find_funct_find_funct_ptr (ge : t F V) (b : block) :
    find_funct ge (.Vptr b Ptrofs.zero) = find_funct_ptr ge b := by
  unfold find_funct
  simp

theorem find_funct_ptr_iff (ge : t F V) (b : block) (f : F) :
    find_funct_ptr ge b = some f ↔ find_def ge b = some (.Gfun f) := by
  unfold find_funct_ptr
  cases find_def ge b with
  | none => simp
  | some gd => cases gd <;> simp

theorem find_var_info_iff (ge : t F V) (b : block) (v : globvar V) :
    find_var_info ge b = some v ↔ find_def ge b = some (.Gvar v) := by
  unfold find_var_info
  cases find_def ge b with
  | none => simp
  | some gd => cases gd <;> simp

/-- `Std.HashMap.insertMany` unfolds to a plain `List.foldl` with `insert`,
    matching `add_globals`'s own fold structure (both process the list
    left-to-right, later entries winning on key clashes). -/
private theorem insertMany_eq_foldl (l : List (ident × globdef F V))
    (m : Std.HashMap ident (globdef F V)) :
    Std.HashMap.insertMany m l = l.foldl (fun m' p => m'.insert p.1 p.2) m := by
  induction l generalizing m with
  | nil => simp
  | cons a l' ih =>
      rw [Std.HashMap.insertMany_cons, List.foldl_cons]
      exact ih (m.insert a.1 a.2)

private theorem ofList_eq_foldl (l : List (ident × globdef F V)) :
    Std.HashMap.ofList l =
      l.foldl (fun m p => m.insert p.1 p.2) (∅ : Std.HashMap ident (globdef F V)) := by
  rw [Std.HashMap.ofList_eq_insertMany_empty]
  exact insertMany_eq_foldl l ∅

theorem find_def_symbol (p : program F V) (id : ident) (g : globdef F V) :
    (prog_defmap F V p).get? id = some g ↔
      ∃ b, find_symbol (globalenv p) id = some b ∧ find_def (globalenv p) b = some g := by
  unfold prog_defmap globalenv
  rw [ofList_eq_foldl]
  have REC : ∀ (l : List (ident × globdef F V)) (m : Std.HashMap ident (globdef F V))
      (ge : t F V), wf ge →
      (m.get? id = some g ↔ ∃ b, find_symbol ge id = some b ∧ find_def ge b = some g) →
      ((l.foldl (fun m' p => m'.insert p.1 p.2) m).get? id = some g ↔
        ∃ b, find_symbol (add_globals ge l) id = some b ∧ find_def (add_globals ge l) b = some g) := by
    intro l
    induction l with
    | nil => intro m ge _ hP; exact hP
    | cons idg1 l' ih =>
        intro m ge hwf hP
        obtain ⟨id1, g1⟩ := idg1
        rw [List.foldl_cons]
        show _ ↔ ∃ b, find_symbol (add_globals (add_global ge (id1, g1)) l') id = some b ∧
          find_def (add_globals (add_global ge (id1, g1)) l') b = some g
        apply ih (m.insert id1 g1) (add_global ge (id1, g1)) (add_global_wf ge (id1, g1) hwf)
        rw [Std.HashMap.get?_insert]
        split
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          constructor
          · intro heqg
            injection heqg with heqg
            subst heqg
            refine ⟨ge.genv_next, ?_, ?_⟩
            · unfold add_global find_symbol
              simp
            · unfold add_global find_def
              simp
          · rintro ⟨b, hb1, hb2⟩
            unfold add_global find_symbol at hb1
            simp only at hb1
            rw [Std.HashMap.get?_insert] at hb1
            simp only [beq_self_eq_true, if_true] at hb1
            injection hb1 with hb1
            subst hb1
            unfold add_global find_def at hb2
            simp only at hb2
            rw [Std.HashMap.get?_insert] at hb2
            simp only [beq_self_eq_true, if_true] at hb2
            injection hb2 with hb2
            subst hb2
            rfl
        · rename_i hne
          rw [hP]
          constructor
          · rintro ⟨b, hb1, hb2⟩
            have hbne : b ≠ ge.genv_next := by
              intro heq
              have hlt := hwf.1 id b hb1
              rw [heq] at hlt
              exact Nat.lt_irrefl _ hlt
            refine ⟨b, ?_, ?_⟩
            · unfold add_global find_symbol
              simp only
              rw [Std.HashMap.get?_insert]
              split
              · rename_i heq'
                exact absurd heq' hne
              · exact hb1
            · unfold add_global find_def
              simp only
              rw [Std.HashMap.get?_insert]
              split
              · rename_i heq
                rw [beq_iff_eq] at heq
                exact absurd heq.symm hbne
              · exact hb2
          · rintro ⟨b, hb1, hb2⟩
            unfold add_global find_symbol at hb1
            simp only at hb1
            rw [Std.HashMap.get?_insert] at hb1
            rw [if_neg (fun h => absurd h hne)] at hb1
            refine ⟨b, hb1, ?_⟩
            have hbne : b ≠ ge.genv_next := by
              intro heq
              have hlt := hwf.1 id b hb1
              rw [heq] at hlt
              exact Nat.lt_irrefl _ hlt
            unfold add_global find_def at hb2
            simp only at hb2
            rw [Std.HashMap.get?_insert] at hb2
            split at hb2
            · rename_i heq
              rw [beq_iff_eq] at heq
              exact absurd heq.symm hbne
            · exact hb2
  have base : (∅ : Std.HashMap ident (globdef F V)).get? id = some g ↔
      ∃ b, find_symbol (empty_genv p.prog_public : t F V) id = some b ∧
        find_def (empty_genv p.prog_public : t F V) b = some g := by
    constructor
    · intro h; simp at h
    · rintro ⟨b, hb, _⟩; unfold find_symbol empty_genv at hb; simp at hb
  exact REC p.prog_defs ∅ (empty_genv p.prog_public) (empty_genv_wf p.prog_public) base

theorem find_symbol_exists (p : program F V) (id : ident) (g : globdef F V)
    (h : (id, g) ∈ p.prog_defs) :
    ∃ b, find_symbol (globalenv p) id = some b := by
  unfold globalenv
  apply add_globals_ensures (P := fun ge => ∃ b, find_symbol ge id = some b) id g p.prog_defs
  · intro ge' id' g' hP _hmem
    obtain ⟨b, hb⟩ := hP
    unfold add_global find_symbol at *
    simp only
    rw [Std.HashMap.get?_insert]
    split
    · exact ⟨ge'.genv_next, rfl⟩
    · exact ⟨b, hb⟩
  · intro ge'
    refine ⟨ge'.genv_next, ?_⟩
    unfold add_global find_symbol
    simp
  · exact h

theorem find_symbol_inversion (p : program F V) (x : ident) (b : block)
    (h : find_symbol (globalenv p) x = some b) :
    x ∈ prog_defs_names F V p := by
  unfold globalenv at h
  have base : find_symbol (empty_genv p.prog_public : t F V) x = some b →
      x ∈ prog_defs_names F V p := by
    intro hfs
    unfold find_symbol empty_genv at hfs
    simp at hfs
  have step : ∀ ge' id g, (find_symbol ge' x = some b → x ∈ prog_defs_names F V p) →
      (id, g) ∈ p.prog_defs → find_symbol (add_global ge' (id, g)) x = some b →
      x ∈ prog_defs_names F V p := by
    intro ge' id g hP hmem hfs
    unfold add_global find_symbol at hfs
    simp only at hfs
    rw [Std.HashMap.get?_insert] at hfs
    split at hfs
    · rename_i heq
      rw [beq_iff_eq] at heq
      subst heq
      unfold prog_defs_names
      exact List.mem_map.mpr ⟨(id, g), hmem, rfl⟩
    · exact hP hfs
  exact add_globals_preserves (P := fun ge => find_symbol ge x = some b → x ∈ prog_defs_names F V p)
    p.prog_defs (empty_genv p.prog_public) step base h

theorem find_def_inversion (p : program F V) (b : block) (g : globdef F V)
    (h : find_def (globalenv p) b = some g) :
    ∃ id, (id, g) ∈ p.prog_defs := by
  unfold globalenv at h
  have base : find_def (empty_genv p.prog_public : t F V) b = some g →
      ∃ id, (id, g) ∈ p.prog_defs := by
    intro hfd
    unfold find_def empty_genv at hfd
    simp at hfd
  have step : ∀ ge' id g', (find_def ge' b = some g → ∃ id, (id, g) ∈ p.prog_defs) →
      (id, g') ∈ p.prog_defs → find_def (add_global ge' (id, g')) b = some g →
      ∃ id, (id, g) ∈ p.prog_defs := by
    intro ge' id g' hP hmem hfd
    unfold add_global find_def at hfd
    simp only at hfd
    rw [Std.HashMap.get?_insert] at hfd
    split at hfd
    · injection hfd with hfd
      subst hfd
      exact ⟨id, hmem⟩
    · exact hP hfd
  exact add_globals_preserves (P := fun ge => find_def ge b = some g → ∃ id, (id, g) ∈ p.prog_defs)
    p.prog_defs (empty_genv p.prog_public) step base h

theorem find_funct_ptr_inversion (p : program F V) (b : block) (f : F)
    (h : find_funct_ptr (globalenv p) b = some f) :
    ∃ id, (id, (.Gfun f : globdef F V)) ∈ p.prog_defs :=
  find_def_inversion p b (.Gfun f) ((find_funct_ptr_iff (globalenv p) b f).mp h)

theorem find_funct_inversion (p : program F V) (v : val) (f : F)
    (h : find_funct (globalenv p) v = some f) :
    ∃ id, (id, (.Gfun f : globdef F V)) ∈ p.prog_defs := by
  obtain ⟨b, hb⟩ := find_funct_inv (globalenv p) v f h
  subst hb
  rw [find_funct_find_funct_ptr] at h
  exact find_funct_ptr_inversion p b f h

theorem find_funct_ptr_prop {P : F → Prop} (p : program F V) (b : block) (f : F)
    (hP : ∀ id f, (id, (.Gfun f : globdef F V)) ∈ p.prog_defs → P f)
    (h : find_funct_ptr (globalenv p) b = some f) : P f := by
  obtain ⟨id, hin⟩ := find_funct_ptr_inversion p b f h
  exact hP id f hin

theorem find_funct_prop {P : F → Prop} (p : program F V) (v : val) (f : F)
    (hP : ∀ id f, (id, (.Gfun f : globdef F V)) ∈ p.prog_defs → P f)
    (h : find_funct (globalenv p) v = some f) : P f := by
  obtain ⟨id, hin⟩ := find_funct_inversion p v f h
  exact hP id f hin

/-- Deviates from CompCert by taking well-formedness explicitly (`hwf`), since
    `id1 ≠ id2 → find_symbol ge id1 = ... → find_symbol ge id2 = ... → b1 ≠ b2`
    is exactly `wf`'s third conjunct — CompCert's dependent `Genv.t` bakes
    this in as an embedded proof field, but our `t` carries no such proof
    (see the module comment on `wf` above), so it must be supplied. -/
theorem global_addresses_distinct (ge : t F V) (hwf : wf ge) (id1 id2 : ident) (b1 b2 : block)
    (h : id1 ≠ id2) (h1 : find_symbol ge id1 = some b1) (h2 : find_symbol ge id2 = some b2) :
    b1 ≠ b2 := by
  intro heq
  subst heq
  exact h (hwf.2.2 id1 id2 b1 h1 h2)

/-- Helper: if folding the "find first/last matching key for value `b`"
    function over `l` (starting from `acc`) yields `some id`, then either
    some entry of `l` witnesses it, or the fold never touched `acc`. -/
private theorem foldl_invert_exists (l : List (ident × block)) (b : block) (id : ident) :
    ∀ acc, l.foldl (fun res p => if b == p.2 then some p.1 else res) acc = some id →
      (∃ b', (id, b') ∈ l ∧ b == b') ∨ acc = some id := by
  induction l with
  | nil => intro acc h; right; exact h
  | cons p l' ih =>
      intro acc h
      simp only [List.foldl_cons] at h
      rcases ih _ h with ⟨b', hmem, hbeq⟩ | hacc
      · exact .inl ⟨b', List.mem_cons_of_mem _ hmem, hbeq⟩
      · by_cases hcond : b == p.2
        · rw [if_pos hcond] at hacc
          injection hacc with hacc
          subst hacc
          exact .inl ⟨p.2, List.mem_cons_self, hcond⟩
        · rw [if_neg hcond] at hacc
          exact .inr hacc

theorem invert_find_symbol (ge : t F V) (id : ident) (b : block)
    (h : invert_symbol ge b = some id) : find_symbol ge id = some b := by
  unfold invert_symbol at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  rcases foldl_invert_exists ge.genv_symb.toList b id none h with ⟨b', hmem, hbeq⟩ | hacc
  · rw [beq_iff_eq] at hbeq
    subst hbeq
    show ge.genv_symb.get? id = some b
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
  · simp at hacc

/-- Helper: if a fold's accumulator already agrees with the unique matching
    key for `b` (per `huniq`), later entries never change it. -/
private theorem foldl_stable (l : List (ident × block)) (b : block) (id : ident)
    (huniq : ∀ p ∈ l, b == p.2 → p.1 = id) :
    l.foldl (fun res p => if b == p.2 then some p.1 else res) (some id) = some id := by
  induction l with
  | nil => rfl
  | cons p l' ih =>
      simp only [List.foldl_cons]
      by_cases hcond : b == p.2
      · rw [if_pos hcond, huniq p (List.mem_cons_self) hcond]
        exact ih (fun q hq hbq => huniq q (List.mem_cons_of_mem _ hq) hbq)
      · rw [if_neg hcond]
        exact ih (fun q hq hbq => huniq q (List.mem_cons_of_mem _ hq) hbq)

/-- Helper: given `(id, b) ∈ l` and that `id` is the *only* key in `l` mapping
    to `b`, the fold finds exactly `id`. -/
private theorem foldl_eq_some_of_unique (l : List (ident × block)) (b : block) (id : ident)
    (hin : (id, b) ∈ l) (huniq : ∀ p ∈ l, b == p.2 → p.1 = id) :
    l.foldl (fun res p => if b == p.2 then some p.1 else res) none = some id := by
  induction l with
  | nil => simp at hin
  | cons p l' ih =>
      rcases List.mem_cons.mp hin with heq | hmem
      · subst heq
        simp only [List.foldl_cons]
        rw [if_pos (show b == (id, b).2 by simp)]
        exact foldl_stable l' b id (fun q hq hbq => huniq q (List.mem_cons_of_mem _ hq) hbq)
      · simp only [List.foldl_cons]
        by_cases hcond : b == p.2
        · rw [if_pos hcond, huniq p (List.mem_cons_self) hcond]
          exact foldl_stable l' b id (fun q hq hbq => huniq q (List.mem_cons_of_mem _ hq) hbq)
        · rw [if_neg hcond]
          exact ih hmem (fun q hq hbq => huniq q (List.mem_cons_of_mem _ hq) hbq)

/-- Deviates from CompCert by taking well-formedness explicitly (`hwf`) —
    see `global_addresses_distinct` above for why. -/
theorem find_invert_symbol (ge : t F V) (hwf : wf ge) (id : ident) (b : block)
    (h : find_symbol ge id = some b) : invert_symbol ge b = some id := by
  unfold invert_symbol
  rw [Std.HashMap.fold_eq_foldl_toList]
  apply foldl_eq_some_of_unique
  · have hb : ge.genv_symb.get? id = some b := h
    rw [Std.HashMap.get?_eq_getElem?] at hb
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hb
  · rintro ⟨id', b'⟩ hp hbeq
    simp only at hbeq ⊢
    rw [beq_iff_eq] at hbeq
    subst hbeq
    have hb' : ge.genv_symb.get? id' = some b := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
    have hfs : find_symbol ge id = some b := h
    exact hwf.2.2 id' id b hb' hfs

/-- Blocks used by folding `add_global` over `gl`, starting from `x`. -/
def advance_next (gl : List (ident × globdef F V)) (x : block) : block :=
  gl.foldl (fun n _ => n + 1) x

theorem genv_next_add_globals (gl : List (ident × globdef F V)) (ge : t F V) :
    (add_globals ge gl).genv_next = advance_next gl ge.genv_next := by
  induction gl generalizing ge with
  | nil => rfl
  | cons a gl' ih => exact ih (add_global ge a)

theorem genv_public_add_globals (gl : List (ident × globdef F V)) (ge : t F V) :
    (add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons a gl' ih => exact ih (add_global ge a)

theorem globalenv_public (p : program F V) : (globalenv p).genv_public = p.prog_public := by
  unfold globalenv
  rw [genv_public_add_globals]
  rfl

/-- Deviates from CompCert by taking well-formedness explicitly (`hwf`) —
    see `global_addresses_distinct` above for why. -/
theorem block_is_volatile_below (ge : t F V) (hwf : wf ge) (b : block)
    (h : block_is_volatile ge b = true) : b < ge.genv_next := by
  unfold block_is_volatile at h
  cases hfv : find_var_info ge b with
  | none => rw [hfv] at h; simp at h
  | some gv =>
      rw [find_var_info_iff] at hfv
      exact hwf.2.1 b (.Gvar gv) hfv

-- ** Coercing a global environment into a symbol environment
--
-- Skipped: CompCert's `Genv.to_senv` coerces a `Genv.t F V` down to the
-- restricted `Senv.t` interface. Since we already skipped the `Senv` module
-- itself (it exists to support generic cross-language linking/compiler-pass
-- proofs, which are out of scope for single-program Clight verification),
-- there is nothing here to port.

-- * Construction of the initial memory state

section INITMEM

variable (ge : t F V)

/-- Store one global-variable initializer at offset `p` in block `b`. -/
def store_init_data (m : mem) (b : block) (p : Int) (id : init_data) : Option mem :=
  match id with
  | .Init_int8 n => store .Mint8unsigned m b p (.Vint n)
  | .Init_int16 n => store .Mint16unsigned m b p (.Vint n)
  | .Init_int32 n => store .Mint32 m b p (.Vint n)
  | .Init_int64 n => store .Mint64 m b p (.Vlong n)
  | .Init_float32 n => store .Mfloat32 m b p (.Vsingle n)
  | .Init_float64 n => store .Mfloat64 m b p (.Vfloat n)
  | .Init_addrof symb ofs =>
      match find_symbol ge symb with
      | none => none
      | some b' => store Mptr m b p (.Vptr b' (Ptrofs.repr ofs))
  | .Init_space _ => some m

def store_init_data_list (m : mem) (b : block) (p : Int) (idl : List init_data) : Option mem :=
  match idl with
  | [] => some m
  | id :: idl' =>
      match store_init_data ge m b p id with
      | none => none
      | some m' => store_init_data_list m' b (p + init_data_size id) idl'

-- `perm_globvar` is skipped: it computes a CompCert `permission` value
-- (Nonempty/Readable/Writable) to be passed to `Mem.drop_perm`. Our memory
-- model tracks no permissions at all (see `Memory.mem`'s design comment:
-- "Permissions are for compiler optimization proofs. For semantics + Iris,
-- separation logic handles ownership."), so there is nothing to compute.

/-- Allocate and initialize one global definition.

    Note: CompCert's version ends with `Mem.drop_perm ... (perm_globvar v)`
    (for `Gvar`) or `Mem.drop_perm ... Nonempty` (for `Gfun`) — setting the
    block's final permission (e.g. making a `const` global read-only, or a
    function block unreadable/unwritable). Since our memory model has no
    permission tracking, these steps are vacuous no-ops here: allocation
    alone already gives the function/variable its distinct block/address,
    which is all our model represents. -/
def alloc_global (m : mem) (idg : ident × globdef F V) : Option mem :=
  match idg with
  | (_, .Gfun _) =>
      let (_, m1) := Memory.alloc m 0 1
      some m1
  | (_, .Gvar v) =>
      let init := v.gvar_init
      let sz := init_data_list_size init
      let (b, m1) := Memory.alloc m 0 sz
      match store_zeros m1 b 0 sz with
      | none => none
      | some m2 => store_init_data_list ge m2 b 0 init

def alloc_globals (m : mem) (gl : List (ident × globdef F V)) : Option mem :=
  match gl with
  | [] => some m
  | g :: gl' =>
      match alloc_global ge m g with
      | none => none
      | some m' => alloc_globals m' gl'

theorem alloc_globals_app (gl1 gl2 : List (ident × globdef F V)) (m m1 : mem)
    (h : alloc_globals ge m gl1 = some m1) :
    alloc_globals ge m1 gl2 = alloc_globals ge m (gl1 ++ gl2) := by
  induction gl1 generalizing m with
  | nil =>
      unfold alloc_globals at h
      injection h with h
      subst h
      rfl
  | cons g gl1' ih =>
      unfold alloc_globals at h
      cases hag : alloc_global ge m g with
      | none => rw [hag] at h; simp at h
      | some m' =>
          rw [hag] at h
          simp only at h
          rw [List.cons_append]
          simpa [alloc_globals, hag] using ih m' h

-- Next-block properties

/-- Any `store` (via `storebytes`) never allocates, so `nextblock` is
    preserved. -/
private theorem nextblock_of_store (chunk : memory_chunk) (m : mem) (b : block) (p : Int)
    (v : val) (m' : mem) (h : Memory.store chunk m b p v = some m') :
    m'.nextblock = m.nextblock :=
  (Memory.Properties.store_blocks chunk m b p v m' h).2

theorem store_init_data_nextblock (m : mem) (b : block) (p : Int) (i : init_data) (m' : mem)
    (h : store_init_data ge m b p i = some m') : m'.nextblock = m.nextblock := by
  cases i with
  | Init_int8 n => exact nextblock_of_store .Mint8unsigned m b p (.Vint n) m' h
  | Init_int16 n => exact nextblock_of_store .Mint16unsigned m b p (.Vint n) m' h
  | Init_int32 n => exact nextblock_of_store .Mint32 m b p (.Vint n) m' h
  | Init_int64 n => exact nextblock_of_store .Mint64 m b p (.Vlong n) m' h
  | Init_float32 n => exact nextblock_of_store .Mfloat32 m b p (.Vsingle n) m' h
  | Init_float64 n => exact nextblock_of_store .Mfloat64 m b p (.Vfloat n) m' h
           | Init_space n =>
      unfold store_init_data at h
      injection h with h
      subst h
      rfl
  | Init_addrof symb ofs =>
      unfold store_init_data at h
      simp only at h
      cases hf : find_symbol ge symb with
      | none => rw [hf] at h; simp at h
      | some b' =>
          rw [hf] at h
          exact nextblock_of_store Mptr m b p (.Vptr b' (Ptrofs.repr ofs)) m' h

theorem store_init_data_list_nextblock (idl : List init_data) (b : block) (m : mem) (p : Int)
    (m' : mem) (h : store_init_data_list ge m b p idl = some m') :
    m'.nextblock = m.nextblock := by
  induction idl generalizing m p with
  | nil => unfold store_init_data_list at h; injection h with h; subst h; rfl
  | cons id idl' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p id with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          rw [ih m1 (p + init_data_size id) h, store_init_data_nextblock ge m b p id m1 hsi]

-- Skipped: "Permissions" (CompCert lines 747-833). These lemmas (e.g.
-- `store_zeros_perm`) state that initialization operations preserve
-- `Mem.perm` for unrelated blocks. Since our memory model has no permission
-- tracking at all (see `Memory.mem`'s design comment), there is nothing to
-- state or prove here.

/-- Generic well-founded-recursion "engine" for `store_zeros`, letting each
    consumer property (`nextblock`, `unchanged_on`, `loadbytes`, `read_as_zero`)
    be derived by supplying just a base case and an inductive step, instead of
    each redoing the strong induction on `n.toNat` themselves. -/
private theorem store_zeros_rec {motive : mem → Int → Int → mem → Prop} (b : block)
    (hbase : ∀ m p n, n ≤ 0 → motive m p n m)
    (hstep : ∀ m p n m1 m', ¬(n ≤ 0) → Memory.store .Mint8unsigned m b p Vzero = some m1 →
      store_zeros m1 b (p + 1) (n - 1) = some m' →
      motive m1 (p + 1) (n - 1) m' → motive m p n m') :
    ∀ m p n m', store_zeros m b p n = some m' → motive m p n m' := by
  have key : ∀ (k : Nat) (m : mem) (p n : Int) (m' : mem), n.toNat = k →
      store_zeros m b p n = some m' → motive m p n m' := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        intro m p n m' hk h
        unfold store_zeros at h
        split at h
        · rename_i hle
          injection h with h
          subst h
          exact hbase m p n hle
        · rename_i hnle
          cases hs : Memory.store .Mint8unsigned m b p Vzero with
          | none => rw [hs] at h; simp at h
          | some m1 =>
              rw [hs] at h
              have hknew : (n - 1).toNat = k - 1 := by omega
              have hlt : k - 1 < k := by omega
              exact hstep m p n m1 m' hnle hs h (ih (k - 1) hlt m1 (p + 1) (n - 1) m' hknew h)
  intro m p n m' h
  exact key n.toNat m p n m' rfl h

theorem store_zeros_nextblock (m : mem) (b : block) (p n : Int) (m' : mem)
    (h : store_zeros m b p n = some m') : m'.nextblock = m.nextblock :=
  store_zeros_rec b (motive := fun m p n m' => m'.nextblock = m.nextblock)
    (fun _ _ _ _ => rfl)
    (fun m _ _ m1 m' _ hs _ hrec => by rw [hrec, nextblock_of_store .Mint8unsigned m b _ Vzero m1 hs])
    m p n m' h

/-- `store_zeros` preserves `valid_pointer` at every position (unconditionally,
    since it only ever writes bytes via `store`, which never touches the
    block-bounds table — see `Memory.Properties.valid_pointer_store`). -/
theorem store_zeros_valid_pointer (m : mem) (b : block) (p n : Int) (m' : mem)
    (h : store_zeros m b p n = some m') (b' : block) (ofs : Int) :
    valid_pointer m b' ofs = valid_pointer m' b' ofs :=
  store_zeros_rec b (motive := fun m p n m' => valid_pointer m b' ofs = valid_pointer m' b' ofs)
    (fun _ _ _ _ => rfl)
    (fun m _ _ m1 m' _ hs _ hrec => by
      rw [Memory.Properties.valid_pointer_store .Mint8unsigned m b _ Vzero m1 b' ofs hs, hrec])
    m p n m' h

/-- `Memory.alloc`'s allocated block's memory always has `nextblock` bumped
    by exactly one. -/
private theorem alloc_snd_nextblock (m : mem) (lo hi : Int) :
    (Memory.alloc m lo hi).2.nextblock = m.nextblock + 1 := rfl

theorem alloc_global_nextblock (g : ident × globdef F V) (m m' : mem)
    (h : alloc_global ge m g = some m') : m'.nextblock = m.nextblock + 1 := by
  obtain ⟨id, gd⟩ := g
  cases gd with
  | Gfun f =>
      unfold alloc_global at h
      simp only at h
      injection h with h
      subst h
      exact alloc_snd_nextblock m 0 1
  | Gvar v =>
      unfold alloc_global at h
      simp only at h
      cases hsz : store_zeros (Memory.alloc m 0 (init_data_list_size v.gvar_init)).2
          (Memory.alloc m 0 (init_data_list_size v.gvar_init)).1 0
          (init_data_list_size v.gvar_init) with
      | none => rw [hsz] at h; simp at h
      | some m2 =>
          rw [hsz] at h
          simp only at h
          have h1 := store_zeros_nextblock _ _ _ _ _ hsz
          have h3 := store_init_data_list_nextblock ge _ _ _ _ _ h
          rw [h3, h1, alloc_snd_nextblock m 0 (init_data_list_size v.gvar_init)]

/-- `store_zeros` never touches the block-bounds table. -/
private theorem store_zeros_blocks (m : mem) (b : block) (p n : Int) (m' : mem)
    (h : store_zeros m b p n = some m') : m'.blocks = m.blocks :=
  store_zeros_rec b (motive := fun m p n m' => m'.blocks = m.blocks)
    (fun _ _ _ _ => rfl)
    (fun m _ _ m1 m' _ hs _ hrec => by
      rw [hrec, (Memory.Properties.store_blocks .Mint8unsigned m b _ Vzero m1 hs).1])
    m p n m' h

/-- `store_init_data` never touches the block-bounds table. -/
theorem store_init_data_blocks (m : mem) (b : block) (p : Int) (i : init_data) (m' : mem)
    (h : store_init_data ge m b p i = some m') : m'.blocks = m.blocks := by
  cases i with
  | Init_int8 n => exact (Memory.Properties.store_blocks _ m b p _ m' h).1
  | Init_int16 n => exact (Memory.Properties.store_blocks _ m b p _ m' h).1
  | Init_int32 n => exact (Memory.Properties.store_blocks _ m b p _ m' h).1
  | Init_int64 n => exact (Memory.Properties.store_blocks _ m b p _ m' h).1
  | Init_float32 n => exact (Memory.Properties.store_blocks _ m b p _ m' h).1
  | Init_float64 n => exact (Memory.Properties.store_blocks _ m b p _ m' h).1
  | Init_space n =>
      unfold store_init_data at h
      injection h with h
      subst h
      rfl
  | Init_addrof symb ofs =>
      unfold store_init_data at h
      simp only at h
      cases hf : find_symbol ge symb with
      | none => rw [hf] at h; simp at h
      | some b' =>
          rw [hf] at h
          exact (Memory.Properties.store_blocks _ m b p _ m' h).1

/-- `store_init_data_list` never touches the block-bounds table. -/
theorem store_init_data_list_blocks (b : block) (il : List init_data) (m : mem) (p : Int)
    (m' : mem) (h : store_init_data_list ge m b p il = some m') : m'.blocks = m.blocks := by
  induction il generalizing m p with
  | nil => unfold store_init_data_list at h; injection h with h; subst h; rfl
  | cons i il' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p i with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          rw [ih m1 (p + init_data_size i) h, store_init_data_blocks ge m b p i m1 hsi]

/-- `alloc_global` only ever touches the block-bounds table at the
    freshly-allocated block (`m.nextblock`) — every other, already-existing
    block's bounds are carried through unchanged. -/
theorem alloc_global_blocks_of_old (g : ident × globdef F V) (m m' : mem)
    (h : alloc_global ge m g = some m') (b : block) (hb : b < m.nextblock) :
    m'.blocks.get? b = m.blocks.get? b := by
  have hne : ¬ (m.nextblock == b) := by
    simp only [beq_iff_eq]
    exact (Nat.ne_of_lt hb).symm
  obtain ⟨id, gd⟩ := g
  cases gd with
  | Gfun f =>
      unfold alloc_global at h
      simp only at h
      injection h with h
      subst h
      show (m.blocks.insert m.nextblock ({ lo := 0, hi := 1 } : Memory.block_info)).get? b =
        m.blocks.get? b
      rw [Std.HashMap.get?_insert, if_neg hne]
  | Gvar v =>
      unfold alloc_global at h
      simp only at h
      cases hsz : store_zeros (Memory.alloc m 0 (init_data_list_size v.gvar_init)).2
          (Memory.alloc m 0 (init_data_list_size v.gvar_init)).1 0
          (init_data_list_size v.gvar_init) with
      | none => rw [hsz] at h; simp at h
      | some m2 =>
          rw [hsz] at h
          simp only at h
          rw [store_init_data_list_blocks ge _ _ _ _ _ h, store_zeros_blocks _ _ _ _ _ hsz]
          show (m.blocks.insert m.nextblock
            ({ lo := 0, hi := init_data_list_size v.gvar_init } : Memory.block_info)).get? b =
            m.blocks.get? b
          rw [Std.HashMap.get?_insert, if_neg hne]

theorem alloc_globals_nextblock (gl : List (ident × globdef F V)) (m m' : mem)
    (h : alloc_globals ge m gl = some m') :
    m'.nextblock = advance_next gl m.nextblock := by
  induction gl generalizing m with
  | nil => unfold alloc_globals at h; injection h with h; subst h; rfl
  | cons g gl' ih =>
      unfold alloc_globals at h
      cases hag : alloc_global ge m g with
      | none => rw [hag] at h; simp at h
      | some m1 =>
          rw [hag] at h
          simp only at h
          unfold advance_next
          rw [List.foldl_cons]
          rw [ih m1 h]
          congr 1
          exact alloc_global_nextblock ge g m m1 hag

-- Data preservation properties

theorem store_zeros_unchanged (P : block → Int → Prop) (m : mem) (b : block) (p n : Int)
    (m' : mem) (h : store_zeros m b p n = some m')
    (hP : ∀ i, p ≤ i → i < p + n → ¬ P b i) :
    unchanged_on P m m' := by
  have hsc : (Memory.size_chunk .Mint8unsigned : Int) = 1 := rfl
  revert hP
  refine store_zeros_rec b
    (motive := fun m p n m' => (∀ i, p ≤ i → i < p + n → ¬ P b i) → unchanged_on P m m')
    (fun m p n _ _ => Memory.Properties.unchanged_on_refl P m)
    (fun m p n m1 m' hnle hs _ hrec hP => ?_) m p n m' h
  have hu1 : unchanged_on P m m1 :=
    Memory.Properties.store_unchanged_on .Mint8unsigned m b p Vzero m1 P hs
      (fun i hi1 hi2 => hP i hi1 (by omega))
  have hu2 : unchanged_on P m1 m' := hrec (fun i hi1 hi2 => hP i (by omega) (by omega))
  exact Memory.Properties.unchanged_on_trans P m m1 m' hu1 hu2

theorem store_init_data_unchanged (P : block → Int → Prop) (b : block) (i : init_data) (m : mem)
    (p : Int) (m' : mem) (h : store_init_data ge m b p i = some m')
    (hP : ∀ ofs, p ≤ ofs → ofs < p + init_data_size i → ¬ P b ofs) :
    unchanged_on P m m' := by
  cases i with
  | Init_int8 n => exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP
  | Init_int16 n => exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP
  | Init_int32 n => exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP
  | Init_int64 n => exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP
  | Init_float32 n => exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP
  | Init_float64 n => exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP
  | Init_space n =>
      unfold store_init_data at h
      injection h with h
      subst h
      exact Memory.Properties.unchanged_on_refl P m
  | Init_addrof symb ofs =>
      unfold store_init_data at h
      simp only at h
      cases hf : find_symbol ge symb with
      | none => rw [hf] at h; simp at h
      | some b' =>
          rw [hf] at h
          have heq : init_data_size (init_data.Init_addrof symb ofs) = (size_chunk Mptr : Int) := by
            show (if Archi.ptr64 then (8 : Int) else 4) = (size_chunk Mptr : Int)
            unfold Mptr
            split <;> rfl
          rw [heq] at hP
          exact Memory.Properties.store_unchanged_on _ m b p _ m' P h hP

theorem store_init_data_list_unchanged (P : block → Int → Prop) (b : block) (il : List init_data)
    (m : mem) (p : Int) (m' : mem) (h : store_init_data_list ge m b p il = some m')
    (hP : ∀ ofs, p ≤ ofs → ¬ P b ofs) :
    unchanged_on P m m' := by
  induction il generalizing m p with
  | nil =>
      unfold store_init_data_list at h
      injection h with h
      subst h
      exact Memory.Properties.unchanged_on_refl P m
  | cons i il' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p i with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          have hnn : init_data_size i ≥ 0 := init_data_size_pos i
          have hu1 : unchanged_on P m m1 :=
            store_init_data_unchanged ge P b i m p m1 hsi (fun ofs hi1 _ => hP ofs hi1)
          have hu2 : unchanged_on P m1 m' :=
            ih m1 (p + init_data_size i) h (fun ofs hi1 => hP ofs (by omega))
          exact Memory.Properties.unchanged_on_trans P m m1 m' hu1 hu2

-- Properties related to `loadbytes`

/-- Every sub-range within `[ofs, ofs + len)` reads back as all-zero bytes. -/
def readbytes_as_zero (m : mem) (b : block) (ofs len : Int) : Prop :=
  ∀ (p : Int) (n : Nat), ofs ≤ p → p + (n : Int) ≤ ofs + len →
    loadbytes m b p (n : Int) =
      some (List.replicate n (.Byte 0 : Memory.memval))

/-- A single `store .Mint8unsigned _ _ Vzero` write leaves a defined, zero
    byte exactly at the position written. -/
private theorem store_zeros_byte_zero (m : mem) (b : block) (p : Int) (m1 : mem)
    (hs : Memory.store .Mint8unsigned m b p Vzero = some m1) :
    Memory.valid_pointer m1 b p = true ∧
      m1.contents.get? (b, p) = some (.Byte 0) := by
  have hva := (Memory.Properties.store_valid_access .Mint8unsigned m b p Vzero).mp ⟨m1, hs⟩
  have hvalid0 := hva.2.2 0 (by decide)
  have hvalid : Memory.valid_pointer m1 b p = true := by
    rw [← Memory.Properties.valid_pointer_store .Mint8unsigned m b p Vzero m1 b p hs]
    simpa only [Int.ofNat_zero, add_zero] using hvalid0
  have hlb := Memory.Properties.loadbytes_store_same .Mint8unsigned m b p Vzero m1 hs
  have hcell :
      [(m1.contents.get? (b, p)).getD (.Undef : Memory.memval)] =
        [(.Byte 0 : Memory.memval)] := by
    unfold Memory.loadbytes at hlb
    simp only [show (Memory.size_chunk .Mint8unsigned : Int) = 1 from rfl] at hlb
    simp only [show ¬((1 : Int) < 0) by decide, if_false] at hlb
    simp only [show (1 : Int).toNat = 1 from rfl] at hlb
    rw [show List.range 1 = [0] from rfl] at hlb
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Int.ofNat_zero, add_zero, Bool.and_true, hvalid, if_true] at hlb
    have hz : Memory.encode_val .Mint8unsigned Vzero =
        [(.Byte 0 : Memory.memval)] := by
      rfl
    rw [hz] at hlb
    exact Option.some.inj hlb
  have hget : m1.contents.get? (b, p) = some (.Byte 0) := by
    cases hg : m1.contents.get? (b, p) with
    | none => rw [hg] at hcell; simp at hcell
    | some x =>
        cases x with
        | Undef => rw [hg] at hcell; simp at hcell
        | Fragment v q i => rw [hg] at hcell; simp at hcell
        | Byte x =>
            rw [hg] at hcell
            have hx : x = 0 := by simpa using hcell
            simpa [hg, hx]
  exact ⟨hvalid, hget⟩

/-- Every byte written by `store_zeros`, from `m` all the way to the final
    `m'`, is a defined zero (established via `store_zeros_byte_zero` for the
    byte just written at each step, propagated forward by
    `store_zeros_unchanged` since later writes never touch earlier
    positions). -/
private theorem store_zeros_zero_bytes (m : mem) (b : block) (p n : Int) (m' : mem)
    (h : store_zeros m b p n = some m') :
    ∀ i, p ≤ i → i < p + n →
      Memory.valid_pointer m' b i = true ∧
        m'.contents.get? (b, i) = some (.Byte 0) :=
  store_zeros_rec b
    (motive := fun m p n m' => ∀ i, p ≤ i → i < p + n →
      Memory.valid_pointer m' b i = true ∧
        m'.contents.get? (b, i) = some (.Byte 0))
    (fun m p n hle i hi1 hi2 => absurd hi2 (by omega))
    (fun m p n m1 m' hnle hs hrec_eq hrec i hi1 hi2 => by
      by_cases heq : i = p
      · subst heq
        obtain ⟨hvalid1, hget1⟩ := store_zeros_byte_zero m b i m1 hs
        have hu : unchanged_on (fun b' j => b' = b ∧ j = i) m1 m' :=
          store_zeros_unchanged (fun b' j => b' = b ∧ j = i) m1 b (i + 1) (n - 1) m' hrec_eq
            (fun j _ _ hpj => by omega)
        obtain ⟨hiff, hceq⟩ := hu.2 b i ⟨rfl, rfl⟩
        exact ⟨hiff.mp hvalid1, by rw [hceq hvalid1]; exact hget1⟩
      · exact hrec i (by omega) (by omega))
    m p n m' h

theorem store_zeros_loadbytes (m : mem) (b : block) (p n : Int) (m' : mem)
    (h : store_zeros m b p n = some m') :
  readbytes_as_zero m' b p n := by
  have hpt := store_zeros_zero_bytes m b p n m' h
  intro q k hq1 hq2
  unfold Memory.loadbytes
  rw [if_neg (show ¬((k : Int) < 0) by omega)]
  have hk : (k : Int).toNat = k := by omega
  rw [hk]
  have hall : (((List.range k).map (fun i : Nat => (b, q + (i : Int)))).all
      (fun p' => Memory.valid_pointer m' p'.1 p'.2)) = true := by
    rw [List.all_eq_true]
    rintro ⟨b', ofs'⟩ hmem
    rw [List.mem_map] at hmem
    obtain ⟨i, hi, hpeq⟩ := hmem
    rw [List.mem_range] at hi
    cases hpeq
    exact (hpt (q + i) (by omega) (by omega)).1
  have hcells :
      ((List.range k).map (fun i : Nat => (b, q + (i : Int)))).map
          (fun p' => (m'.contents.get? (p'.1, p'.2)).getD (.Undef : Memory.memval)) =
        List.replicate k (.Byte 0) := by
    rw [List.map_map]
    rw [show List.replicate k (.Byte 0) =
      (List.range k).map (fun _ => (.Byte 0 : Memory.memval)) by simp]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hg := (hpt (q + i) (by omega) (by omega)).2
    change (m'.contents.get? (b, q + (i : Int))).getD
      (.Undef : Memory.memval) = .Byte 0
    rw [hg]
    rfl
  rw [if_pos hall, hcells]

/- The raw memory cells a single initializer contributes. -/
def bytes_of_init_data (ge : t F V) (i : init_data) : Option (List Memory.memval) :=
  match i with
  | .Init_int8 n => some (Memory.encode_val .Mint8unsigned (.Vint n))
  | .Init_int16 n => some (Memory.encode_val .Mint16unsigned (.Vint n))
  | .Init_int32 n => some (Memory.encode_val .Mint32 (.Vint n))
  | .Init_int64 n => some (Memory.encode_val .Mint64 (.Vlong n))
  | .Init_float32 n => some (Memory.encode_val .Mfloat32 (.Vsingle n))
  | .Init_float64 n => some (Memory.encode_val .Mfloat64 (.Vfloat n))
  | .Init_space n => some (List.replicate n.toNat (.Byte 0 : Memory.memval))
  | .Init_addrof symb ofs =>
      match find_symbol ge symb with
      | some b => some (Memory.encode_val Mptr (.Vptr b (Ptrofs.repr ofs)))
      | none => none

theorem init_data_size_addrof (id : ident) (ofs : Int) :
    init_data_size (.Init_addrof id ofs) = size_chunk Mptr := by
  show (if Archi.ptr64 then (8 : Int) else 4) = (size_chunk Mptr : Int)
  unfold Mptr
  split <;> rfl

theorem store_init_data_loadbytes (m : mem) (b : block) (p : Int) (i : init_data) (m' : mem)
    (h : store_init_data ge m b p i = some m')
    (hz : readbytes_as_zero m b p (init_data_size i)) :
    ∃ bytes, bytes_of_init_data ge i = some bytes ∧
      loadbytes m' b p (init_data_size i) = some bytes := by
  cases i with
  | Init_int8 n =>
      unfold store_init_data at h
      exact ⟨_, rfl,
        Memory.Properties.loadbytes_store_same .Mint8unsigned m b p (.Vint n) m' h⟩
  | Init_int16 n =>
      unfold store_init_data at h
      exact ⟨_, rfl,
        Memory.Properties.loadbytes_store_same .Mint16unsigned m b p (.Vint n) m' h⟩
  | Init_int32 n =>
      unfold store_init_data at h
      exact ⟨_, rfl,
        Memory.Properties.loadbytes_store_same .Mint32 m b p (.Vint n) m' h⟩
  | Init_int64 n =>
      unfold store_init_data at h
      exact ⟨_, rfl,
        Memory.Properties.loadbytes_store_same .Mint64 m b p (.Vlong n) m' h⟩
  | Init_float32 n =>
      unfold store_init_data at h
      exact ⟨_, rfl,
        Memory.Properties.loadbytes_store_same .Mfloat32 m b p (.Vsingle n) m' h⟩
  | Init_float64 n =>
      unfold store_init_data at h
      exact ⟨_, rfl,
        Memory.Properties.loadbytes_store_same .Mfloat64 m b p (.Vfloat n) m' h⟩
  | Init_space n =>
      unfold store_init_data at h
      injection h with h
      subst h
      refine ⟨List.replicate n.toNat (.Byte 0 : Memory.memval), rfl, ?_⟩
      have hz' : readbytes_as_zero m b p (max n 0) := hz
      have hread := hz' p (max n 0).toNat (le_refl p) (by omega)
      have hn : (max n 0).toNat = n.toNat := by omega
      rw [hn] at hread
      show loadbytes m b p (init_data_size (init_data.Init_space n)) =
        some (List.replicate n.toNat (.Byte 0 : Memory.memval))
      rw [show init_data_size (init_data.Init_space n) = max n 0 from rfl]
      have hcast : (n.toNat : Int) = max n 0 := by omega
      rw [← hcast]
      exact hread
  | Init_addrof symb ofs =>
      cases hf : find_symbol ge symb with
      | none =>
          simp only [store_init_data, hf] at h
          simp at h
      | some b' =>
          simp only [store_init_data, hf] at h
          let bytes := Memory.encode_val Mptr (.Vptr b' (Ptrofs.repr ofs))
          refine ⟨bytes, ?_, ?_⟩
          · simp only [bytes_of_init_data, hf, bytes]
          · rw [init_data_size_addrof]
            exact Memory.Properties.loadbytes_store_same Mptr m b p
              (.Vptr b' (Ptrofs.repr ofs)) m' h

def bytes_of_init_data_list (il : List init_data) : Option (List Memory.memval) :=
  match il with
  | [] => some []
  | i :: il' =>
      match bytes_of_init_data ge i, bytes_of_init_data_list il' with
      | some bytes, some bytes' => some (bytes ++ bytes')
      | _, _ => none

theorem store_init_data_list_loadbytes (b : block) (il : List init_data) (m : mem) (p : Int)
    (m' : mem) (h : store_init_data_list ge m b p il = some m')
    (hz : readbytes_as_zero m b p (init_data_list_size il)) :
    ∃ bytes, bytes_of_init_data_list ge il = some bytes ∧
      loadbytes m' b p (init_data_list_size il) = some bytes := by
  induction il generalizing m p with
  | nil =>
      unfold store_init_data_list at h
      injection h with h
      subst h
      refine ⟨[], rfl, ?_⟩
      show loadbytes m b p (0 : Int) = some []
      exact Memory.Properties.loadbytes_empty m b p
  | cons i1 il' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p i1 with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          have hz1 : readbytes_as_zero m b p (init_data_size i1) := by
            intro p' k hp1 hp2
            have hnn := init_data_list_size_pos il'
            refine hz p' k hp1 ?_
            show p' + k ≤ p + (init_data_size i1 + init_data_list_size il')
            omega
          obtain ⟨bytes1, hb1, hlb1⟩ :=
            store_init_data_loadbytes ge m b p i1 m1 hsi hz1
          have hu1 : unchanged_on (fun _ ofs1 => ofs1 < p + init_data_size i1) m1 m' :=
            store_init_data_list_unchanged ge (fun _ ofs1 => ofs1 < p + init_data_size i1)
              b il' m1 (p + init_data_size i1) m' h (fun ofs1 hi1 => by omega)
          have hlb1' : loadbytes m' b p (init_data_size i1) = some bytes1 := by
            rw [Memory.Properties.loadbytes_unchanged_on _ m1 m' b p (init_data_size i1) hu1
              (fun i _ hi2 => hi2)]
            exact hlb1
          have hz2 : readbytes_as_zero m1 b (p + init_data_size i1) (init_data_list_size il') := by
            intro p' k hp1 hp2
            have hn1 := init_data_size_pos i1
            have hu2 : unchanged_on (fun _ ofs1 => p + init_data_size i1 ≤ ofs1) m m1 :=
              store_init_data_unchanged ge (fun _ ofs1 => p + init_data_size i1 ≤ ofs1) b i1 m p m1
                hsi (fun ofs hi1 hi2 => by omega)
            rw [Memory.Properties.loadbytes_unchanged_on _ m m1 b p' k hu2
              (fun i hi1 _ => by omega)]
            refine hz p' k (by omega) ?_
            show p' + k ≤ p + (init_data_size i1 + init_data_list_size il')
            omega
          obtain ⟨bytes2, hb2, hlb2⟩ := ih m1 (p + init_data_size i1) h hz2
          refine ⟨bytes1 ++ bytes2, ?_, ?_⟩
          · simp [bytes_of_init_data_list, hb1, hb2]
          · have hn1 : init_data_size i1 ≥ 0 := init_data_size_pos i1
            have hn2 : init_data_list_size il' ≥ 0 := init_data_list_size_pos il'
            show loadbytes m' b p (init_data_size i1 + init_data_list_size il') =
              some (bytes1 ++ bytes2)
            exact Memory.Properties.loadbytes_concat m' b p (init_data_size i1)
              (init_data_list_size il') bytes1 bytes2 hlb1' hlb2 hn1 hn2

-- Properties related to `load`

/-- Every properly-aligned chunk read within `[ofs, ofs + len)` reads back as
    the zero value of its type.

    Deviates from CompCert for `Many32`/`Many64`: CompCert's `decode_val`
    always returns `Vundef` for these "type-oblivious" chunks (they exist to
    support byte-for-byte `memcpy`-style copies without committing to a
    scalar type), but this port's `decode_val` deliberately decodes them
    identically to `Mint32`/`Mint64` (see `Memory.lean`'s `decode_val`,
    which groups `.Mint32 | .Many32` and `.Mint64 | .Many64` in the same
    match arms) — so the zero value read back is `Vint`/`Vlong` zero, not
    `Vundef`, matching what's actually provable against our `decode_val`. -/
def read_as_zero (m : mem) (b : block) (ofs len : Int) : Prop :=
  ∀ (chunk : memory_chunk) (p : Int),
    ofs ≤ p → p + (size_chunk chunk : Int) ≤ ofs + len →
    (align_chunk chunk : Int) ∣ p →
    Memory.load chunk m b p =
      some (match chunk with
        | .Mbool | .Mint8unsigned | .Mint8signed | .Mint16unsigned | .Mint16signed | .Mint32
        | .Many32 =>
            .Vint CompCert.Int.zero
        | .Mint64 | .Many64 => .Vlong CompCert.Int64.zero
        | .Mfloat32 => .Vsingle CompCert.Float32.zero
        | .Mfloat64 => .Vfloat CompCert.Float64.zero)

theorem read_as_zero_unchanged (P : block → Int → Prop) (m : mem) (b : block) (ofs len : Int)
    (m' : mem) (h : read_as_zero m b ofs len) (hu : unchanged_on P m m')
    (hP : ∀ i, ofs ≤ i → i < ofs + len → P b i) :
    read_as_zero m' b ofs len := by
  intro chunk q hq1 hq2 halign
  rw [Memory.Properties.load_unchanged_on P m m' chunk b q hu
    (fun i hi1 hi2 => hP i (by omega) (by omega))]
  exact h chunk q hq1 hq2 halign

theorem store_zeros_read_as_zero (m : mem) (b : block) (p n : Int) (m' : mem)
    (h : store_zeros m b p n = some m') :
    read_as_zero m' b p n := by
  have hpt := store_zeros_zero_bytes m b p n m' h
  intro chunk q hq1 hq2 halign
  have halign_true : Memory.is_aligned q chunk = true := by
    unfold Memory.is_aligned
    have heq0 : q % (Memory.align_chunk chunk : Int) = 0 := Int.emod_eq_zero_of_dvd halign
    simp [heq0]
  have hall : (((List.range (Memory.size_chunk chunk)).map
      (fun i : Nat => (b, q + (i : Int)))).all
      (fun p' => Memory.valid_pointer m' p'.1 p'.2)) = true := by
    rw [List.all_eq_true]
    rintro ⟨b', ofs'⟩ hmem
    rw [List.mem_map] at hmem
    obtain ⟨i, hi, hpeq⟩ := hmem
    rw [List.mem_range] at hi
    cases hpeq
    exact (hpt (q + i) (by omega) (by omega)).1
  have hcells :
      ((List.range (Memory.size_chunk chunk)).map
        (fun i : Nat => (b, q + (i : Int)))).map
          (fun p' => (m'.contents.get? (p'.1, p'.2)).getD (.Undef : Memory.memval)) =
        List.replicate (Memory.size_chunk chunk) (.Byte 0 : Memory.memval) := by
    rw [List.map_map]
    rw [show List.replicate (Memory.size_chunk chunk) (.Byte 0 : Memory.memval) =
      (List.range (Memory.size_chunk chunk)).map
        (fun _ => (.Byte 0 : Memory.memval)) by simp]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hg := (hpt (q + i) (by omega) (by omega)).2
    change (m'.contents.get? (b, q + (i : Int))).getD
      (.Undef : Memory.memval) = .Byte 0
    rw [hg]
    rfl
  unfold Memory.load
  rw [if_neg (by simpa using halign_true), if_pos hall]
  rw [hcells]
  have hproj : ∀ n : Nat, Memory.proj_bytes
      (List.replicate n (.Byte 0 : Memory.memval)) =
      some (List.replicate n (0 : UInt8)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, Memory.proj_bytes, ih]
  simp only [Memory.decode_val, hproj]
  cases chunk <;>
    simp [Memory.size_chunk, Memory.decode_bytes, Memory.decode_encode_norm,
      CompCert.Int.zero, CompCert.Int64.zero] <;> norm_num <;> rfl

/-- After successful initialization, this characterizes exactly what `load`
    returns for each field, at its natural chunk type — the concrete
    per-field payoff of the whole construction. -/
def load_store_init_data (m : mem) (b : block) (p : Int) (il : List init_data) : Prop :=
  match il with
  | [] => True
  | .Init_int8 n :: il' =>
      Memory.load .Mint8unsigned m b p = some (.Vint (CompCert.Int.zero_ext 8 n))
      ∧ load_store_init_data m b (p + 1) il'
  | .Init_int16 n :: il' =>
      Memory.load .Mint16unsigned m b p = some (.Vint (CompCert.Int.zero_ext 16 n))
      ∧ load_store_init_data m b (p + 2) il'
  | .Init_int32 n :: il' =>
      Memory.load .Mint32 m b p = some (.Vint n)
      ∧ load_store_init_data m b (p + 4) il'
  | .Init_int64 n :: il' =>
      Memory.load .Mint64 m b p = some (.Vlong n)
      ∧ load_store_init_data m b (p + 8) il'
  | .Init_float32 n :: il' =>
      Memory.load .Mfloat32 m b p = some (.Vsingle n)
      ∧ load_store_init_data m b (p + 4) il'
  | .Init_float64 n :: il' =>
      Memory.load .Mfloat64 m b p = some (.Vfloat n)
      ∧ load_store_init_data m b (p + 8) il'
  | .Init_addrof symb ofs :: il' =>
      (∃ b', find_symbol ge symb = some b' ∧
        Memory.load Mptr m b p = some (.Vptr b' (Ptrofs.repr ofs)))
      ∧ load_store_init_data m b (p + (size_chunk Mptr : Int)) il'
  | .Init_space n :: il' =>
      read_as_zero m b p n
      ∧ load_store_init_data m b (p + max n 0) il'

theorem store_init_data_list_charact (b : block) (il : List init_data) (m : mem) (p : Int)
    (m' : mem) (h : store_init_data_list ge m b p il = some m')
    (hz : read_as_zero m b p (init_data_list_size il)) :
    load_store_init_data ge m' b p il := by
  induction il generalizing m p with
  | nil => trivial
  | cons i1 il' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p i1 with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          have hn1 : init_data_size i1 ≥ 0 := init_data_size_pos i1
          have hu : unchanged_on (fun _ ofs' => ofs' < p + init_data_size i1) m1 m' :=
            store_init_data_list_unchanged ge (fun _ ofs' => ofs' < p + init_data_size i1)
              b il' m1 (p + init_data_size i1) m' h (fun ofs' hi1 => by omega)
          have hz2 : read_as_zero m1 b (p + init_data_size i1) (init_data_list_size il') := by
            intro chunk q hq1 hq2 halign
            have hu2 : unchanged_on (fun _ ofs' => p + init_data_size i1 ≤ ofs') m m1 :=
              store_init_data_unchanged ge (fun _ ofs' => p + init_data_size i1 ≤ ofs') b i1 m p m1
                hsi (fun ofs hi1 hi2 => by omega)
            rw [Memory.Properties.load_unchanged_on _ m m1 chunk b q hu2 (fun i hi1 _ => by omega)]
            refine hz chunk q (by omega) ?_ halign
            show q + (size_chunk chunk : Int) ≤ p + (init_data_size i1 + init_data_list_size il')
            omega
          have htail : load_store_init_data ge m' b (p + init_data_size i1) il' :=
            ih m1 (p + init_data_size i1) h hz2
          have hload : ∀ (chunk : memory_chunk) (v : val),
               init_data_size i1 = (size_chunk chunk : Int) →
               store chunk m b p v = some m1 →
               Memory.load chunk m' b p = some (Memory.decode_val chunk (Memory.encode_val chunk v)) := by
            intro chunk v hcs hstore
            rw [Memory.Properties.load_unchanged_on _ m1 m' chunk b p hu (fun i _ hi2 => by omega)]
            exact Memory.Properties.load_store_same chunk m b p v m1 hstore
          cases i1 with
          | Init_int8 n =>
              refine ⟨?_, htail⟩
              have hL := hload .Mint8unsigned (.Vint n) rfl hsi
              rw [hL]
              rw [Memory.Properties.encode_decode_roundtrip .Mint8unsigned (.Vint n)
                (fun _ _ hcontra => by cases hcontra) (by simp [Memory.encode_bytes])]
              rfl
          | Init_int16 n =>
              refine ⟨?_, htail⟩
              have hL := hload .Mint16unsigned (.Vint n) rfl hsi
              rw [hL]
              rw [Memory.Properties.encode_decode_roundtrip .Mint16unsigned (.Vint n)
                (fun _ _ hcontra => by cases hcontra) (by simp [Memory.encode_bytes])]
              rfl
          | Init_int32 n =>
              refine ⟨?_, htail⟩
              have hL := hload .Mint32 (.Vint n) rfl hsi
              rw [hL]
              rw [Memory.Properties.encode_decode_roundtrip .Mint32 (.Vint n)
                (fun _ _ hcontra => by cases hcontra) (by simp [Memory.encode_bytes])]
              rfl
          | Init_int64 n =>
              refine ⟨?_, htail⟩
              have hL := hload .Mint64 (.Vlong n) rfl hsi
              rw [hL]
              rw [Memory.Properties.encode_decode_roundtrip .Mint64 (.Vlong n)
                (fun _ _ hcontra => by cases hcontra) (by simp [Memory.encode_bytes])]
              rfl
          | Init_float32 n =>
              refine ⟨?_, htail⟩
              have hL := hload .Mfloat32 (.Vsingle n) rfl hsi
              rw [hL]
              rw [Memory.Properties.encode_decode_roundtrip .Mfloat32 (.Vsingle n)
                (fun _ _ hcontra => by cases hcontra) (by simp [Memory.encode_bytes])]
              rfl
          | Init_float64 n =>
              refine ⟨?_, htail⟩
              have hL := hload .Mfloat64 (.Vfloat n) rfl hsi
              rw [hL]
              rw [Memory.Properties.encode_decode_roundtrip .Mfloat64 (.Vfloat n)
                (fun _ _ hcontra => by cases hcontra) (by simp [Memory.encode_bytes])]
              rfl
           | Init_addrof symb ofs =>
               unfold store_init_data at hsi
               simp only at hsi
               cases hf : find_symbol ge symb with
               | none => rw [hf] at hsi; simp at hsi
               | some b' =>
                   rw [hf] at hsi
                   simp only at hsi
                   refine ⟨⟨b', hf, ?_⟩, ?_⟩
                   · have hcs : init_data_size (init_data.Init_addrof symb ofs) =
                         (size_chunk Mptr : Int) := init_data_size_addrof symb ofs
                     have hL := hload Mptr (.Vptr b' (Ptrofs.repr ofs)) hcs hsi
                     rw [hL]
                     rw [Memory.Properties.decode_encode_ptr b' (Ptrofs.repr ofs)]
                     cases hp : Archi.ptr64 <;> simp [Mptr, Val.load_result, hp]
                   · show load_store_init_data ge m' b (p + (size_chunk Mptr : Int)) il'
                     rw [← init_data_size_addrof symb ofs]
                     exact htail
           | Init_space n =>
              unfold store_init_data at hsi
              injection hsi with hsi
              refine ⟨?_, ?_⟩
              · have hz1 : read_as_zero m b p (max n 0) := by
                  intro chunk q hq1 hq2 halign
                  refine hz chunk q hq1 ?_ halign
                  show q + (size_chunk chunk : Int) ≤ p + (max n 0 + init_data_list_size il')
                  have := init_data_list_size_pos il'
                  omega
                have hu' : unchanged_on (fun _ ofs' => ofs' < p + max n 0) m1 m' := by
                  rw [← hsi] at hu ⊢
                  exact hu
                have hz1' : read_as_zero m' b p (max n 0) := by
                  intro chunk q hq1 hq2 halign
                  rw [Memory.Properties.load_unchanged_on _ m1 m' chunk b q hu'
                    (fun i _ hi2 => by omega)]
                  rw [← hsi]
                  exact hz1 chunk q hq1 hq2 halign
                intro chunk q hq1 hq2 halign
                exact hz1' chunk q hq1 (by omega) halign
              · show load_store_init_data ge m' b (p + max n 0) il'
                have heq : init_data_size (init_data.Init_space n) = max n 0 := rfl
                rw [← heq]
                exact htail

/-- Deviates from CompCert's `alloc_global_unchanged` (which holds for
    *unrestricted* `P`): this port's `Memory.unchanged_on` is not gated on
    "valid in the earlier memory" the way CompCert's `unchanged_on_perm`
    field is (see `Memory.Properties.alloc_unchanged_on`'s doc comment), so
    an unrestricted `P` would force agreement even at the freshly-allocated
    block, which is false. The added `hPfresh` hypothesis — `P` only concerns
    blocks already below `m`'s `nextblock` — is always available at actual
    call sites (which reason about specific pre-existing blocks) and is
    exactly what's needed to route around the gap. -/
theorem alloc_global_unchanged (P : block → Int → Prop) (m : mem) (id : ident)
    (g : globdef F V) (m' : mem) (h : alloc_global ge m (id, g) = some m')
    (hPfresh : ∀ b' ofs, P b' ofs → b' < m.nextblock) :
    unchanged_on P m m' := by
  have hPne : ∀ b' ofs, P b' ofs → b' ≠ m.nextblock :=
    fun b' ofs hPb => Nat.ne_of_lt (hPfresh b' ofs hPb)
  cases g with
  | Gfun f =>
      unfold alloc_global at h
      simp only at h
      injection h with h
      subst h
      exact Memory.Properties.alloc_unchanged_on P m 0 1 m.nextblock (Memory.alloc m 0 1).2
        rfl hPne
  | Gvar v =>
      unfold alloc_global at h
      simp only at h
      set sz := init_data_list_size v.gvar_init
      set b0 := (Memory.alloc m 0 sz).1 with hb0
      set m1 := (Memory.alloc m 0 sz).2 with hm1
      have halloc : (b0, m1) = Memory.alloc m 0 sz := rfl
      have hu1 : unchanged_on P m m1 :=
        Memory.Properties.alloc_unchanged_on P m 0 sz b0 m1 halloc hPne
      have hb0eq : b0 = m.nextblock := by rw [hb0]; rfl
      cases hsz : store_zeros m1 b0 0 sz with
      | none => rw [hsz] at h; simp at h
      | some m2 =>
          rw [hsz] at h
          simp only at h
          have hPneb0 : ∀ i, (0:Int) ≤ i → i < 0 + sz → ¬ P b0 i :=
            fun i _ _ hPb0 => hPne b0 i hPb0 hb0eq
          have hu2 : unchanged_on P m1 m2 :=
            store_zeros_unchanged P m1 b0 0 sz m2 hsz hPneb0
          have hPneb0' : ∀ ofs, (0:Int) ≤ ofs → ¬ P b0 ofs :=
            fun ofs _ hPb0 => hPne b0 ofs hPb0 hb0eq
          have hu3 : unchanged_on P m2 m' :=
            store_init_data_list_unchanged ge P b0 v.gvar_init m2 0 m' h hPneb0'
          exact Memory.Properties.unchanged_on_trans P m m2 m'
            (Memory.Properties.unchanged_on_trans P m m1 m2 hu1 hu2) hu3

theorem alloc_globals_unchanged (P : block → Int → Prop) (gl : List (ident × globdef F V))
    (m m' : mem) (h : alloc_globals ge m gl = some m')
    (hPfresh : ∀ b' ofs, P b' ofs → b' < m.nextblock) :
    unchanged_on P m m' := by
  induction gl generalizing m with
  | nil =>
      unfold alloc_globals at h
      injection h with h
      subst h
      exact Memory.Properties.unchanged_on_refl P m
  | cons g gl' ih =>
      unfold alloc_globals at h
      cases hag : alloc_global ge m g with
      | none => rw [hag] at h; simp at h
      | some m1 =>
          rw [hag] at h
          simp only at h
          have hu1 : unchanged_on P m m1 := by
            obtain ⟨id, gd⟩ := g
            exact alloc_global_unchanged ge P m id gd m1 hag hPfresh
          have hnb : m1.nextblock = m.nextblock + 1 := alloc_global_nextblock ge g m m1 hag
          have hPfresh' : ∀ b' ofs, P b' ofs → b' < m1.nextblock := by
            intro b' ofs hPb
            rw [hnb]
            exact Nat.lt_succ_of_lt (hPfresh b' ofs hPb)
          have hu2 : unchanged_on P m1 m' := ih m1 h hPfresh'
          exact Memory.Properties.unchanged_on_trans P m m1 m' hu1 hu2

theorem load_store_init_data_invariant (m m' : mem) (b : block)
    (h : ∀ chunk ofs, Memory.load chunk m' b ofs = Memory.load chunk m b ofs)
    (il : List init_data) (p : Int) (hd : load_store_init_data ge m b p il) :
    load_store_init_data ge m' b p il := by
  induction il generalizing p with
  | nil => trivial
  | cons i1 il' ih =>
      cases i1 with
      | Init_int8 n => obtain ⟨h1, h2⟩ := hd; exact ⟨by rw [h]; exact h1, ih _ h2⟩
      | Init_int16 n => obtain ⟨h1, h2⟩ := hd; exact ⟨by rw [h]; exact h1, ih _ h2⟩
      | Init_int32 n => obtain ⟨h1, h2⟩ := hd; exact ⟨by rw [h]; exact h1, ih _ h2⟩
      | Init_int64 n => obtain ⟨h1, h2⟩ := hd; exact ⟨by rw [h]; exact h1, ih _ h2⟩
      | Init_float32 n => obtain ⟨h1, h2⟩ := hd; exact ⟨by rw [h]; exact h1, ih _ h2⟩
      | Init_float64 n => obtain ⟨h1, h2⟩ := hd; exact ⟨by rw [h]; exact h1, ih _ h2⟩
      | Init_addrof symb ofs =>
          obtain ⟨⟨b', hfs, hload⟩, h2⟩ := hd
          exact ⟨⟨b', hfs, by rw [h]; exact hload⟩, ih _ h2⟩
      | Init_space n =>
          obtain ⟨hrz, h2⟩ := hd
          refine ⟨?_, ih _ h2⟩
          intro chunk q hq1 hq2 halign
          rw [h chunk q]
          exact hrz chunk q hq1 hq2 halign

/-- The central well-formedness invariant: for every definition known to `g`,
    its block in `m` has exactly the right bounds (and, for non-volatile
    globals, exactly the right contents).

    Note: CompCert's two permission-based conjuncts per case (`range_perm` +
    a `forall`-bounded-above fact) together say exactly "block `b`'s valid
    range is precisely `[0, size)`". Since our `block_info` stores `(lo, hi)`
    directly rather than deriving validity from a permission map, this
    collapses to a single `m.blocks.get? b = some { lo := 0, hi := size }`
    equality — no information is lost, this is just a more direct statement
    of the same fact.

    `g` is the genv whose *definitions* are being checked (via `find_def`);
    the ambient section variable `ge` is used, as elsewhere in this section,
    to resolve `Init_addrof` symbols inside initializers. In practice these
    coincide when this is actually invoked, but are kept separate here for
    the same reason CompCert does (matches `alloc_global_initialized` below,
    where `g` is being incrementally extended while `ge` stays fixed). -/
def globals_initialized (g : t F V) (m : mem) : Prop :=
  ∀ b gd, find_def g b = some gd →
    match gd with
    | .Gfun _ =>
        m.blocks.get? b = some { lo := 0, hi := 1 }
    | .Gvar v =>
        m.blocks.get? b = some { lo := 0, hi := init_data_list_size v.gvar_init } ∧
        (v.gvar_volatile = false → load_store_init_data ge m b 0 v.gvar_init) ∧
        (v.gvar_volatile = false →
          loadbytes m b 0 (init_data_list_size v.gvar_init) =
            bytes_of_init_data_list ge v.gvar_init)

/-- Deviates from CompCert by requiring `wf g` explicitly: CompCert's `t`
    is a dependent record carrying its own well-formedness proof, so
    `genv_defs_range` is always available; this port's `t F V` carries no
    such embedded proof (see the `wf`/`hwf` deviations elsewhere in this
    file), so it must be threaded in here to know that an "old" block found
    via `find_def g b` is below `m.nextblock` (needed to invoke
    `alloc_global_unchanged`/`alloc_global_blocks_of_old`). -/
theorem alloc_global_initialized (g : t F V) (m : mem) (id : ident) (gd : globdef F V)
    (m' : mem) (hwf : wf g) (h_next : g.genv_next = m.nextblock)
    (h_alloc : alloc_global ge m (id, gd) = some m')
    (h_init : globals_initialized ge g m) :
    globals_initialized ge (add_global g (id, gd)) m' ∧
    (add_global g (id, gd)).genv_next = m'.nextblock := by
  have hnb : m'.nextblock = m.nextblock + 1 := alloc_global_nextblock ge (id, gd) m m' h_alloc
  refine ⟨?_, ?_⟩
  · intro b gd0 hfd
    unfold find_def add_global at hfd
    simp only at hfd
    rw [Std.HashMap.get?_insert] at hfd
    split at hfd
    · injection hfd with hfd
      subst hfd
      rename_i heq
      rw [beq_iff_eq] at heq
      cases gd with
      | Gfun f =>
          show m'.blocks.get? b = some { lo := 0, hi := 1 }
          rw [← heq, h_next]
          unfold alloc_global at h_alloc
          simp only at h_alloc
          injection h_alloc with h_alloc
          subst h_alloc
          show (m.blocks.insert m.nextblock
              ({ lo := 0, hi := 1 } : Memory.block_info)).get? m.nextblock =
            some { lo := 0, hi := 1 }
          rw [Std.HashMap.get?_insert, if_pos (by simp)]
       | Gvar v =>
           change m'.blocks.get? b = some { lo := 0, hi := init_data_list_size v.gvar_init } ∧
             (v.gvar_volatile = false → load_store_init_data ge m' b 0 v.gvar_init) ∧
             (v.gvar_volatile = false →
               loadbytes m' b 0 (init_data_list_size v.gvar_init) =
                 bytes_of_init_data_list ge v.gvar_init)
           rw [← heq, h_next]
           unfold alloc_global at h_alloc
           simp only at h_alloc
           cases hsz : store_zeros (Memory.alloc m 0 (init_data_list_size v.gvar_init)).2
               (Memory.alloc m 0 (init_data_list_size v.gvar_init)).1 0
               (init_data_list_size v.gvar_init) with
           | none => rw [hsz] at h_alloc; simp at h_alloc
           | some m2 =>
               rw [hsz] at h_alloc
               simp only at h_alloc
               have hsz' : store_zeros (Memory.alloc m 0 (init_data_list_size v.gvar_init)).2
                   m.nextblock 0 (init_data_list_size v.gvar_init) = some m2 := hsz
               have h_alloc' : store_init_data_list ge m2 m.nextblock 0 v.gvar_init = some m' :=
                 h_alloc
               have hzero := store_zeros_loadbytes _ _ _ _ _ hsz'
               have hrz := store_zeros_read_as_zero _ _ _ _ _ hsz'
               refine ⟨?_, ?_, ?_⟩
               · have hblocks := store_init_data_list_blocks ge _ _ _ _ _ h_alloc'
                 rw [hblocks, store_zeros_blocks _ _ _ _ _ hsz']
                 show (m.blocks.insert m.nextblock
                     ({ lo := 0, hi := init_data_list_size v.gvar_init } :
                       Memory.block_info)).get? m.nextblock =
                   some { lo := 0, hi := init_data_list_size v.gvar_init }
                 rw [Std.HashMap.get?_insert, if_pos (by simp)]
               · intro _
                 exact store_init_data_list_charact ge _ _ _ _ _ h_alloc' hrz
               · intro _
                 obtain ⟨bytes, hbeq, hlb⟩ :=
                   store_init_data_list_loadbytes ge _ _ _ _ _ h_alloc' hzero
                 rw [hlb, hbeq]
    · rename_i hne
      rw [beq_iff_eq] at hne
      have hfd' : find_def g b = some gd0 := hfd
      have hbb : b < m.nextblock := by
        have := hwf.2.1 b gd0 hfd'
        rw [← h_next]
        exact this
      have hUeq : unchanged_on (fun b' _ => b' = b) m m' :=
        alloc_global_unchanged ge (fun b' _ => b' = b) m id gd m' h_alloc
          (fun b' ofs heq2 => heq2 ▸ hbb)
      have hbval := h_init b gd0 hfd'
      have hblocks_eq := alloc_global_blocks_of_old ge (id, gd) m m' h_alloc b hbb
      have hload_eq : ∀ chunk ofs, Memory.load chunk m' b ofs = Memory.load chunk m b ofs :=
        fun chunk ofs => Memory.Properties.load_unchanged_on (fun b' _ => b' = b) m m' chunk b ofs
          hUeq (fun i _ _ => rfl)
      cases gd0 with
      | Gfun f =>
          show m'.blocks.get? b = some { lo := 0, hi := 1 }
          rw [hblocks_eq]
          exact hbval
       | Gvar v =>
           obtain ⟨hbnd, hload, hlb⟩ := hbval
           refine ⟨?_, ?_, ?_⟩
           · rw [hblocks_eq]; exact hbnd
           · intro hnv
             exact load_store_init_data_invariant ge m m' b hload_eq _ 0 (hload hnv)
           · intro hnv
             have hlbeq : loadbytes m' b 0 (init_data_list_size v.gvar_init) =
                 loadbytes m b 0 (init_data_list_size v.gvar_init) :=
               Memory.Properties.loadbytes_unchanged_on (fun b' _ => b' = b) m m' b 0
                 (init_data_list_size v.gvar_init) hUeq (fun i _ _ => rfl)
             rw [hlbeq]
             exact hlb hnv
  · unfold add_global
    simp only
    rw [h_next]
    exact hnb.symm

/-- Deviates from CompCert by requiring `wf g` explicitly, for the same
    reason as `alloc_global_initialized` (whose `hwf` requirement propagates
    through this induction, re-derived via `add_global_wf` at each step). -/
theorem alloc_globals_initialized (gl : List (ident × globdef F V)) (g : t F V) (m m' : mem)
    (hwf : wf g)
    (h_alloc : alloc_globals ge m gl = some m')
    (h_next : g.genv_next = m.nextblock)
    (h_init : globals_initialized ge g m) :
    globals_initialized ge (add_globals g gl) m' := by
  induction gl generalizing g m with
  | nil =>
      unfold alloc_globals at h_alloc
      injection h_alloc with h_alloc
      subst h_alloc
      show globals_initialized ge (add_globals g []) m
      unfold add_globals
      rw [List.foldl_nil]
      exact h_init
  | cons idg gl' ih =>
      unfold alloc_globals at h_alloc
      cases hag : alloc_global ge m idg with
      | none => rw [hag] at h_alloc; simp at h_alloc
      | some m1 =>
          rw [hag] at h_alloc
          simp only at h_alloc
          obtain ⟨id, gd⟩ := idg
          obtain ⟨hinit1, hnext1⟩ := alloc_global_initialized ge g m id gd m1 hwf h_next hag h_init
          have hwf1 : wf (add_global g (id, gd)) := add_global_wf g (id, gd) hwf
          have hres := ih (add_global g (id, gd)) m1 hwf1 h_alloc hnext1 hinit1
          show globals_initialized ge (add_globals g ((id, gd) :: gl')) m'
          unfold add_globals
          rw [List.foldl_cons]
          exact hres

end INITMEM

/-- Build the initial memory state for a whole program: the global
    environment resolves its own `Init_addrof` symbols, folded over an
    initially-empty memory. -/
def init_mem (p : program F V) : Option mem :=
  alloc_globals (globalenv p) Memory.empty p.prog_defs

theorem globalenv_wf (p : program F V) : wf (globalenv p) := by
  unfold globalenv
  apply add_globals_preserves (P := wf) p.prog_defs (empty_genv p.prog_public)
  · intro ge' id g' hwf' _
    exact add_global_wf ge' (id, g') hwf'
  · exact empty_genv_wf p.prog_public

theorem init_mem_genv_next (p : program F V) (m : mem) (h : init_mem p = some m) :
    (globalenv p).genv_next = m.nextblock := by
  unfold init_mem at h
  have h1 := alloc_globals_nextblock (globalenv p) p.prog_defs Memory.empty m h
  unfold globalenv
  rw [genv_next_add_globals, h1]
  rfl

theorem find_symbol_not_fresh (p : program F V) (id : ident) (b : block) (m : mem)
    (h : init_mem p = some m) (hs : find_symbol (globalenv p) id = some b) :
    b < m.nextblock := by
  rw [← init_mem_genv_next p m h]
  exact (globalenv_wf p).1 id b hs

theorem find_def_not_fresh (p : program F V) (b : block) (g : globdef F V) (m : mem)
    (h : init_mem p = some m) (hd : find_def (globalenv p) b = some g) :
    b < m.nextblock := by
  rw [← init_mem_genv_next p m h]
  exact (globalenv_wf p).2.1 b g hd

theorem find_funct_ptr_not_fresh (p : program F V) (b : block) (f : F) (m : mem)
    (h : init_mem p = some m) (hf : find_funct_ptr (globalenv p) b = some f) :
    b < m.nextblock := by
  unfold find_funct_ptr at hf
  cases hd : find_def (globalenv p) b with
  | none => rw [hd] at hf; simp at hf
  | some gd =>
      rw [hd] at hf
      exact find_def_not_fresh p b gd m h hd

theorem find_var_info_not_fresh (p : program F V) (b : block) (gv : globvar V) (m : mem)
    (h : init_mem p = some m) (hv : find_var_info (globalenv p) b = some gv) :
    b < m.nextblock := by
  unfold find_var_info at hv
  cases hd : find_def (globalenv p) b with
  | none => rw [hd] at hv; simp at hv
  | some gd =>
      rw [hd] at hv
      exact find_def_not_fresh p b gd m h hd

theorem init_mem_characterization_gen (p : program F V) (m : mem) (h : init_mem p = some m) :
    globals_initialized (globalenv p) (globalenv p) m := by
  unfold init_mem at h
  apply alloc_globals_initialized (globalenv p) p.prog_defs (empty_genv p.prog_public)
      Memory.empty m (empty_genv_wf p.prog_public) h
  · rfl
  · intro b gd hfd
    unfold find_def empty_genv at hfd
    simp at hfd

/-- The key theorem for reasoning about a specific global variable's initial
    contents: given `gv` found at block `b`, its memory has exactly bounds
    `[0, size)`, and (if non-volatile) its fields load back to exactly their
    declared values, and its raw bytes match exactly. -/
theorem init_mem_characterization (p : program F V) (b : block) (gv : globvar V) (m : mem)
    (h_var : find_var_info (globalenv p) b = some gv) (h : init_mem p = some m) :
    m.blocks.get? b = some { lo := 0, hi := init_data_list_size gv.gvar_init } ∧
    (gv.gvar_volatile = false → load_store_init_data (globalenv p) m b 0 gv.gvar_init) ∧
     (gv.gvar_volatile = false →
       loadbytes m b 0 (init_data_list_size gv.gvar_init) =
         bytes_of_init_data_list (globalenv p) gv.gvar_init) := by
  have hgd : find_def (globalenv p) b = some (globdef.Gvar gv) := by
    unfold find_var_info at h_var
    cases hd : find_def (globalenv p) b with
    | none => rw [hd] at h_var; simp at h_var
    | some gd =>
        rw [hd] at h_var
        cases gd with
        | Gfun f => simp at h_var
        | Gvar v => simp only at h_var; injection h_var with h_var; rw [h_var]
  simpa using (init_mem_characterization_gen p m h b (.Gvar gv) hgd)

theorem init_mem_characterization_2 (p : program F V) (b : block) (fd : F) (m : mem)
    (h_fun : find_funct_ptr (globalenv p) b = some fd) (h : init_mem p = some m) :
    m.blocks.get? b = some { lo := 0, hi := 1 } := by
  have hgd : find_def (globalenv p) b = some (globdef.Gfun fd) := by
    unfold find_funct_ptr at h_fun
    cases hd : find_def (globalenv p) b with
    | none => rw [hd] at h_fun; simp at h_fun
    | some gd =>
        rw [hd] at h_fun
        cases gd with
        | Gfun f => simp only at h_fun; injection h_fun with h_fun; rw [h_fun]
        | Gvar v => simp at h_fun
  exact init_mem_characterization_gen p m h b (.Gfun fd) hgd

-- Skipped: "Compatibility with memory injections" (`INITMEM_INJ`, CompCert
-- lines 1340-1440). This section proves that `init_mem` respects memory
-- injections (`Mem.inject`) — i.e. that separately-compiled/injected
-- programs' initial memories stay related under a `meminj`. This is
-- compiler-pass/simulation infrastructure (the same category as `Linking.v`
-- and the `MATCH_GENVS`/`MATCH_PROGRAMS`/`TRANSFORM_*` sections we've
-- already decided to skip throughout this file), not needed for
-- single-program Clight verification.

-- ** Sufficient and necessary conditions for the initial memory to exist.

-- Alignment properties

def init_data_alignment (i : init_data) : Int :=
  match i with
  | .Init_int8 _ => 1
  | .Init_int16 _ => 2
  | .Init_int32 _ => 4
  | .Init_int64 _ => 8
  | .Init_float32 _ => 4
  | .Init_float64 _ => 8
  | .Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | .Init_space _ => 1

def init_data_list_aligned (p : Int) (il : List init_data) : Prop :=
  match il with
  | [] => True
  | i1 :: il' => init_data_alignment i1 ∣ p ∧ init_data_list_aligned (p + init_data_size i1) il'

section INITMEM_INVERSION

variable (ge : t F V)

theorem store_init_data_aligned (m : mem) (b : block) (p : Int) (i : init_data) (m' : mem)
    (h : store_init_data ge m b p i = some m') :
    init_data_alignment i ∣ p := by
  have isdvd : ∀ chunk, Memory.is_aligned p chunk = true → (Memory.align_chunk chunk : Int) ∣ p := by
    intro chunk hal
    unfold Memory.is_aligned at hal
    simp only [decide_eq_true_eq] at hal
    have h2 : p % (Memory.align_chunk chunk : Int) = 0 := by omega
    exact Int.dvd_of_emod_eq_zero h2
  have hDFL : ∀ chunk v, store chunk m b p v = some m' →
      (Memory.align_chunk chunk : Int) = init_data_alignment i →
      init_data_alignment i ∣ p := by
    intro chunk v hstore heqal
    have hva := (Memory.Properties.store_valid_access chunk m b p v).mp ⟨m', hstore⟩
    rw [← heqal]
    exact isdvd chunk hva.1
  cases i with
  | Init_int8 n => exact hDFL .Mint8unsigned (.Vint n) h rfl
  | Init_int16 n => exact hDFL .Mint16unsigned (.Vint n) h rfl
  | Init_int32 n => exact hDFL .Mint32 (.Vint n) h rfl
  | Init_int64 n => exact hDFL .Mint64 (.Vlong n) h rfl
  | Init_float32 n => exact hDFL .Mfloat32 (.Vsingle n) h rfl
  | Init_float64 n => exact hDFL .Mfloat64 (.Vfloat n) h rfl
  | Init_space n => show (1:Int) ∣ p; exact one_dvd p
  | Init_addrof symb ofs =>
      unfold store_init_data at h
      simp only at h
      cases hf : find_symbol ge symb with
      | none => rw [hf] at h; simp at h
      | some b' =>
          rw [hf] at h
          have hva := (Memory.Properties.store_valid_access Mptr m b p
            (.Vptr b' (Ptrofs.repr ofs))).mp ⟨m', h⟩
          have hdvd := isdvd Mptr hva.1
          show (if Archi.ptr64 then (8:Int) else 4) ∣ p
          unfold Mptr at hdvd
          by_cases hp : Archi.ptr64
          · rw [if_pos hp] at hdvd ⊢; exact hdvd
          · rw [if_neg hp] at hdvd ⊢; exact hdvd

theorem store_init_data_list_aligned (b : block) (il : List init_data) (m : mem) (p : Int)
    (m' : mem) (h : store_init_data_list ge m b p il = some m') :
    init_data_list_aligned p il := by
  induction il generalizing m p with
  | nil => trivial
  | cons i1 il' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p i1 with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          exact ⟨store_init_data_aligned ge m b p i1 m1 hsi, ih m1 (p + init_data_size i1) h⟩

theorem store_init_data_list_free_idents (b : block) (i : ident) (o : Int) (il : List init_data)
    (m : mem) (p : Int) (m' : mem) (h : store_init_data_list ge m b p il = some m')
    (hin : (.Init_addrof i o) ∈ il) :
    ∃ b', find_symbol ge i = some b' := by
  induction il generalizing m p with
  | nil => cases hin
  | cons i1 il' ih =>
      unfold store_init_data_list at h
      cases hsi : store_init_data ge m b p i1 with
      | none => rw [hsi] at h; simp at h
      | some m1 =>
          rw [hsi] at h
          simp only at h
          rcases List.mem_cons.mp hin with heq | hmem
          · subst heq
            unfold store_init_data at hsi
            simp only at hsi
            cases hf : find_symbol ge i with
            | none => rw [hf] at hsi; simp at hsi
            | some c => exact ⟨c, rfl⟩
          · exact ih m1 (p + init_data_size i1) h hmem

end INITMEM_INVERSION

theorem init_mem_inversion (p : program F V) (m : mem) (id : ident) (v : globvar V)
    (h : init_mem p = some m) (hin : (id, (.Gvar v : globdef F V)) ∈ p.prog_defs) :
    init_data_list_aligned 0 v.gvar_init ∧
    ∀ i o, (.Init_addrof i o) ∈ v.gvar_init → ∃ b, find_symbol (globalenv p) i = some b := by
  unfold init_mem at h
  have key : ∀ (defs : List (ident × globdef F V)) (m0 m' : mem),
      alloc_globals (globalenv p) m0 defs = some m' →
      (id, (.Gvar v : globdef F V)) ∈ defs →
      init_data_list_aligned 0 v.gvar_init ∧
      ∀ i o, (.Init_addrof i o) ∈ v.gvar_init → ∃ b, find_symbol (globalenv p) i = some b := by
    intro defs
    induction defs with
    | nil => intro m0 m' _ hmem; cases hmem
    | cons idg1 defs' ih =>
        intro m0 m' halloc hmem
        unfold alloc_globals at halloc
        cases hag : alloc_global (globalenv p) m0 idg1 with
        | none => rw [hag] at halloc; simp at halloc
        | some m1 =>
            rw [hag] at halloc
            simp only at halloc
            rcases List.mem_cons.mp hmem with heq | hmem'
            · subst heq
              unfold alloc_global at hag
              simp only at hag
              cases hsz : store_zeros (Memory.alloc m0 0 (init_data_list_size v.gvar_init)).2
                  (Memory.alloc m0 0 (init_data_list_size v.gvar_init)).1 0
                  (init_data_list_size v.gvar_init) with
              | none => rw [hsz] at hag; simp at hag
              | some m2 =>
                  rw [hsz] at hag
                  simp only at hag
                  refine ⟨store_init_data_list_aligned (globalenv p) _ v.gvar_init _ _ _ hag, ?_⟩
                  intro i o hmemio
                  exact store_init_data_list_free_idents (globalenv p) _ i o v.gvar_init _ _ _ hag
                    hmemio
            · exact ih m1 m' halloc hmem'
  exact key p.prog_defs Memory.empty m h hin

section INITMEM_EXISTS

variable (ge : t F V)

theorem store_zeros_exists (m : mem) (b : block) (p n : Int)
    (h : ∀ i, p ≤ i → i < p + n → valid_pointer m b i) :
    ∃ m', store_zeros m b p n = some m' := by
  have key : ∀ (k : Nat) (m : mem) (p n : Int), n.toNat = k →
      (∀ i, p ≤ i → i < p + n → valid_pointer m b i) →
      ∃ m', store_zeros m b p n = some m' := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        intro m p n hk hrange
        unfold store_zeros
        split
        · exact ⟨m, rfl⟩
        · rename_i hnle
          have hvalid : valid_pointer m b p = true := hrange p (le_refl p) (by omega)
          have hva : ∃ m1, Memory.store .Mint8unsigned m b p Vzero = some m1 := by
            rw [Memory.Properties.store_valid_access]
            refine ⟨by unfold Memory.is_aligned Memory.align_chunk; simp,
              by unfold Memory.encode_val Vzero; simp [Memory.inj_bytes, Memory.encode_bytes], ?_⟩
            intro i hi
            have hi0 : i = 0 := by
              simp only [Memory.size_chunk] at hi
              omega
            subst hi0
            simpa using hvalid
          obtain ⟨m1, hm1⟩ := hva
          rw [hm1]
          have hknew : (n - 1).toNat = k - 1 := by omega
          have hlt : k - 1 < k := by omega
          have hrange' : ∀ i, p + 1 ≤ i → i < (p + 1) + (n - 1) → valid_pointer m1 b i := by
            intro i hi1 hi2
            rw [← Memory.Properties.valid_pointer_store .Mint8unsigned m b p Vzero m1 b i hm1]
            exact hrange i (by omega) (by omega)
          exact ih (k - 1) hlt m1 (p + 1) (n - 1) hknew hrange'
  exact key n.toNat m p n rfl h

theorem store_init_data_exists (m : mem) (b : block) (p : Int) (i : init_data)
    (h_range : ∀ j, p ≤ j → j < p + init_data_size i → valid_pointer m b j)
    (h_align : init_data_alignment i ∣ p)
    (h_addrof : ∀ id ofs, i = .Init_addrof id ofs → ∃ b', find_symbol ge id = some b') :
    ∃ m', store_init_data ge m b p i = some m' := by
  have hDFL : ∀ chunk v, init_data_size i = (size_chunk chunk : Int) →
      (Memory.align_chunk chunk : Int) = init_data_alignment i →
      Memory.encode_val chunk v ≠ [] →
      ∃ m', store chunk m b p v = some m' := by
    intro chunk v hsz halgn hne
    rw [Memory.Properties.store_valid_access]
    refine ⟨?_, hne, ?_⟩
    · unfold Memory.is_aligned
      simp only [decide_eq_true_eq]
      rw [halgn]
      have := Int.emod_eq_zero_of_dvd h_align
      omega
    · intro j hj
      apply h_range (p + j)
      · omega
      · rw [hsz]
        have : (j : Int) < (size_chunk chunk : Int) := by exact_mod_cast hj
        omega
  cases i with
  | Init_int8 n => exact hDFL .Mint8unsigned (.Vint n) rfl rfl (by simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes])
  | Init_int16 n => exact hDFL .Mint16unsigned (.Vint n) rfl rfl (by simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes])
  | Init_int32 n => exact hDFL .Mint32 (.Vint n) rfl rfl (by simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes])
  | Init_int64 n => exact hDFL .Mint64 (.Vlong n) rfl rfl (by simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes])
  | Init_float32 n => exact hDFL .Mfloat32 (.Vsingle n) rfl rfl (by simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes])
  | Init_float64 n => exact hDFL .Mfloat64 (.Vfloat n) rfl rfl (by simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes])
  | Init_space n => exact ⟨m, rfl⟩
  | Init_addrof symb ofs =>
      obtain ⟨b', hfs⟩ := h_addrof symb ofs rfl
      unfold store_init_data
      simp only
      rw [hfs]
      have hcs : init_data_size (init_data.Init_addrof symb ofs) = (size_chunk Mptr : Int) :=
        init_data_size_addrof symb ofs
      have hal : (Memory.align_chunk Mptr : Int) =
          init_data_alignment (init_data.Init_addrof symb ofs) := by
        unfold Mptr init_data_alignment
        split <;> rfl
      exact hDFL Mptr (.Vptr b' (Ptrofs.repr ofs)) hcs hal (by
         unfold Mptr
         split <;> rename_i hp <;>
           simp [Memory.encode_val, Memory.inj_bytes, Memory.encode_bytes,
             Memory.ptr_quantity, Memory.inj_value, Memory.quantity_size, hp])

theorem store_init_data_list_exists (b : block) (il : List init_data) (m : mem) (p : Int)
    (h_range : ∀ j, p ≤ j → j < p + init_data_list_size il → valid_pointer m b j)
    (h_align : init_data_list_aligned p il)
    (h_addrof : ∀ id ofs, (.Init_addrof id ofs) ∈ il → ∃ b', find_symbol ge id = some b') :
    ∃ m', store_init_data_list ge m b p il = some m' := by
  induction il generalizing m p with
  | nil => exact ⟨m, rfl⟩
  | cons i1 il' ih =>
      have hn1 : init_data_size i1 ≥ 0 := init_data_size_pos i1
      have hn2 : init_data_list_size il' ≥ 0 := init_data_list_size_pos il'
      have hcons : init_data_list_size (i1 :: il') = init_data_size i1 + init_data_list_size il' :=
        rfl
      obtain ⟨halign1, halign2⟩ := h_align
      obtain ⟨m1, hm1⟩ := store_init_data_exists ge m b p i1
        (fun j hj1 hj2 => h_range j hj1 (by rw [hcons]; omega)) halign1
        (fun id ofs heq => h_addrof id ofs (by rw [heq]; exact List.mem_cons_self))
      have h_range' : ∀ j, p + init_data_size i1 ≤ j → j < (p + init_data_size i1) +
          init_data_list_size il' → valid_pointer m1 b j := by
        intro j hj1 hj2
        have hu : unchanged_on (fun _ ofs' => ofs' = j) m m1 :=
          store_init_data_unchanged ge (fun _ ofs' => ofs' = j) b i1 m p m1 hm1
            (fun ofs' _ heq' => by omega)
        rw [← (hu.2 b j rfl).1]
        exact h_range j (by omega) (by rw [hcons]; omega)
      have h_addrof' : ∀ id ofs, (.Init_addrof id ofs) ∈ il' → ∃ b', find_symbol ge id = some b' :=
        fun id ofs hmem => h_addrof id ofs (List.mem_cons_of_mem i1 hmem)
      obtain ⟨m2, hm2⟩ := ih m1 (p + init_data_size i1) h_range' halign2 h_addrof'
      refine ⟨m2, ?_⟩
      unfold store_init_data_list
      rw [hm1]
      exact hm2

theorem alloc_global_exists (m : mem) (idg : ident × globdef F V)
    (h : match idg.2 with
      | .Gfun _ => True
      | .Gvar v =>
          init_data_list_aligned 0 v.gvar_init ∧
          ∀ i o, (.Init_addrof i o) ∈ v.gvar_init → ∃ b, find_symbol ge i = some b) :
    ∃ m', alloc_global ge m idg = some m' := by
  obtain ⟨id, gd⟩ := idg
  cases gd with
  | Gfun f =>
      unfold alloc_global
      simp only
      exact ⟨(Memory.alloc m 0 1).2, rfl⟩
  | Gvar v =>
      simp only at h
      obtain ⟨halign, haddrof⟩ := h
      set sz := init_data_list_size v.gvar_init
      have hn : sz ≥ 0 := init_data_list_size_pos v.gvar_init
      set b0 := (Memory.alloc m 0 sz).1 with hb0
      set m1 := (Memory.alloc m 0 sz).2 with hm1def
      have hbounds : ∀ j, (0:Int) ≤ j → j < 0 + sz → valid_pointer m1 b0 j := by
        intro j hj1 hj2
        rw [hb0, hm1def]
        exact (Memory.Properties.alloc_result_bounds m 0 sz b0 m1 j
          (by rw [hb0, hm1def])).mpr ⟨hj1, by omega⟩
      obtain ⟨m2, hm2⟩ := store_zeros_exists m1 b0 0 sz hbounds
      have hzp : ∀ j, (0:Int) ≤ j → j < sz → valid_pointer m2 b0 j := by
        intro j hj1 hj2
        rw [← store_zeros_valid_pointer m1 b0 0 sz m2 hm2 b0 j]
        exact hbounds j hj1 (by omega)
      obtain ⟨m3, hm3⟩ := store_init_data_list_exists ge b0 v.gvar_init m2 0
        (fun j hj1 hj2 => hzp j (by omega) (by omega)) halign haddrof
      refine ⟨m3, ?_⟩
      unfold alloc_global
      simp only
      rw [← hb0, ← hm1def, hm2]
      exact hm3

end INITMEM_EXISTS

theorem init_mem_exists (p : program F V)
    (h : ∀ id v, (id, (.Gvar v : globdef F V)) ∈ p.prog_defs →
      init_data_list_aligned 0 v.gvar_init ∧
      ∀ i o, (.Init_addrof i o) ∈ v.gvar_init → ∃ b, find_symbol (globalenv p) i = some b) :
    ∃ m, init_mem p = some m := by
  unfold init_mem
  have key : ∀ (defs : List (ident × globdef F V)) (m0 : mem),
      (∀ id v, (id, (.Gvar v : globdef F V)) ∈ defs →
        init_data_list_aligned 0 v.gvar_init ∧
        ∀ i o, (.Init_addrof i o) ∈ v.gvar_init → ∃ b, find_symbol (globalenv p) i = some b) →
      ∃ m', alloc_globals (globalenv p) m0 defs = some m' := by
    intro defs
    induction defs with
    | nil => intro m0 _; exact ⟨m0, rfl⟩
    | cons idg1 defs' ih =>
        intro m0 hh
        obtain ⟨id1, gd1⟩ := idg1
        have hcond : match (id1, gd1).2 with
            | .Gfun _ => True
            | .Gvar v =>
                init_data_list_aligned 0 v.gvar_init ∧
                ∀ i o, (.Init_addrof i o) ∈ v.gvar_init →
                  ∃ b, find_symbol (globalenv p) i = some b := by
          cases gd1 with
          | Gfun f => trivial
          | Gvar v => exact hh id1 v List.mem_cons_self
        obtain ⟨m1, hm1⟩ := alloc_global_exists (globalenv p) m0 (id1, gd1) hcond
        unfold alloc_globals
        rw [hm1]
        simp only
        exact ih m1 (fun id v hmem => hh id v (List.mem_cons_of_mem _ hmem))
  exact key p.prog_defs Memory.empty h

-- Skipped: `MATCH_GENVS`, `MATCH_PROGRAMS`, `TRANSFORM_PARTIAL`, and
-- `TRANSFORM_TOTAL` (CompCert lines 1657-1928). These define simulation
-- relations between *two* programs/genvs (before/after a compiler pass) and
-- lemmas for transporting properties across such transformations. Like
-- `Linking.v` and `INITMEM_INJ`, this is compiler-pass/linking
-- infrastructure, out of scope for single-program Clight verification.

end Genv
