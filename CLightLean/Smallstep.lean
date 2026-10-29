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

import CLightLean.Events

/-!
# Small-step operational semantics

Port of `common/Smallstep.v` from CompCert. Defines generic operations and
theorems over transition relations, the `semantics` record used to package a
language's step relation, and the receptiveness/determinacy classes.

**Skipped**: the forward-simulation (`fsim_properties`, `forward_simulation`,
and the whole `FORWARD_SIMU_DIAGRAMS`/`FORWARD_SIMU_EVENTUALLY` family) and
backward-simulation (`bsim_properties`, `backward_simulation`,
`FORWARD_TO_BACKWARD`, `COMPOSE_BACKWARD_SIMULATIONS`) sections, plus the
`atomic`/`FACTOR_FORWARD_SIMULATION`/`FACTOR_BACKWARD_SIMULATION` semantics
transformers and the `bigstep_semantics`/`bigstep_sound` connection. All of
this is compiler-pass correctness infrastructure (relating the semantics of
*two* languages before/after a compiler transformation) — the same category
of material already skipped throughout `Globalenvs.lean`
(`MATCH_GENVS`/`TRANSFORM_PARTIAL`/`INITMEM_INJ`), and out of scope for
single-program Clight verification.

**Deferred**: the coinductive divergence predicates `forever`, `forever_N`,
`forever_plus`, and `forever_reactive` (Coq `CoInductive`s producing an
infinite trace, via `Eappinf`/`***`). Lean 4 has no native coinductive-type
support; faithfully encoding these needs an "infinite concatenation of
finite chunks" characterization over the `Stream'`-based `traceinf` (see
`Events.traceinf`), which is nontrivial and not needed until a
`Behaviors.v`-style whole-program divergence-classification file, if ever —
`Clight.lean`'s own step relation does not need them. `forever_silent`
(no trace argument, so no such encoding needed) is likewise deferred to keep
this pass focused, since nothing yet consumes it either.

Deviates from CompCert in one place: `semantics`/`receptive`/`determinate`
have no `symbolenv : Senv.t` field, matching the earlier decision (see
`Globalenvs.lean`'s note on `Genv.to_senv`) to skip the `Senv` module
entirely; `Events.match_traces` here is already stated directly over
`Genv.t F V`, reached from a `semantics`'s abstract `genvtype` via its
`to_genv` projection (playing the role Coq's `Genv.to_senv` plays for
`symbolenv`).
-/

namespace Smallstep

open Events (trace E0)

/- `trace`/`event` (from `Events.lean`) are themselves parameterized by an
    `Archi` instance. Without this
    variable in scope, every mention of `trace` below would silently resolve
    to whatever `Archi` instance typeclass search happens to pick, hard-wiring
    this file's `semantics`/`star`/`plus`/etc. to one fixed architecture
    instead of staying generic — which breaks unification against a caller
    (e.g. `Clight.lean`) that is itself generic over `[Archi]`. -/
variable [Archi]

-- ============================================================================
-- * Closures of transition relations
-- ============================================================================

section CLOSURES

variable {genv state : Type}
variable (step : genv → state → trace → state → Prop)

/-- No transitions: stuck state. -/
def nostep (ge : genv) (s : state) : Prop :=
  ∀ t s', ¬ step ge s t s'

-- ** Zero, one or several transitions (Kleene closure). --

/-- Zero, one or several transitions. Also known as Kleene closure, or the
    reflexive transitive closure of `step`. -/
inductive star (ge : genv) : state → trace → state → Prop where
  | star_refl : ∀ s, star ge s E0 s
  | star_step : ∀ s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 → star ge s2 t2 s3 → t = t1 ++ t2 →
      star ge s1 t s3

theorem star_one (ge : genv) (s1 : state) (t : trace) (s2 : state)
    (h : step ge s1 t s2) : star step ge s1 t s2 := by
  rw [show t = t ++ E0 from (List.append_nil t).symm]
  exact .star_step s1 t s2 E0 s2 (t ++ E0) h (.star_refl s2) rfl

theorem star_two (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : step ge s1 t1 s2) (h2 : step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : star step ge s1 t s3 :=
  .star_step s1 t1 s2 t2 s3 t h1 (star_one step ge s2 t2 s3 h2) heq

theorem star_three (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t3 : trace) (s4 : state) (t : trace)
    (h1 : step ge s1 t1 s2) (h2 : step ge s2 t2 s3) (h3 : step ge s3 t3 s4)
    (heq : t = t1 ++ t2 ++ t3) : star step ge s1 t s4 := by
  subst heq
  rw [List.append_assoc]
  exact .star_step s1 t1 s2 (t2 ++ t3) s4 (t1 ++ (t2 ++ t3)) h1
    (star_two step ge s2 t2 s3 t3 s4 (t2 ++ t3) h2 h3 rfl) rfl

theorem star_four (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t3 : trace) (s4 : state) (t4 : trace) (s5 : state) (t : trace)
    (h1 : step ge s1 t1 s2) (h2 : step ge s2 t2 s3) (h3 : step ge s3 t3 s4)
    (h4 : step ge s4 t4 s5) (heq : t = t1 ++ t2 ++ t3 ++ t4) : star step ge s1 t s5 := by
  subst heq
  rw [List.append_assoc, List.append_assoc]
  exact .star_step s1 t1 s2 (t2 ++ (t3 ++ t4)) s5 (t1 ++ (t2 ++ (t3 ++ t4))) h1
    (star_three step ge s2 t2 s3 t3 s4 t4 s5 (t2 ++ (t3 ++ t4)) h2 h3 h4 (by rw [List.append_assoc]))
    rfl

theorem star_trans (ge : genv) (s1 : state) (t1 : trace) (s2 : state)
    (h1 : star step ge s1 t1 s2) (t2 : trace) (s3 : state) (t : trace)
    (h2 : star step ge s2 t2 s3) (heq : t = t1 ++ t2) : star step ge s1 t s3 := by
  subst heq
  induction h1 with
  | star_refl s => simpa using h2
  | star_step sa ta sb tb sc tc hstep hstar heq' ih =>
      subst heq'
      rw [List.append_assoc]
      exact .star_step sa ta sb (tb ++ t2) s3 (ta ++ (tb ++ t2)) hstep (ih h2) rfl

theorem star_left (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : step ge s1 t1 s2) (h2 : star step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : star step ge s1 t s3 :=
  .star_step s1 t1 s2 t2 s3 t h1 h2 heq

theorem star_right (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : star step ge s1 t1 s2) (h2 : step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : star step ge s1 t s3 :=
  star_trans step ge s1 t1 s2 h1 t2 s3 t (star_one step ge s2 t2 s3 h2) heq

theorem star_E0_ind (ge : genv) (P : state → state → Prop)
    (base : ∀ s, P s s)
    (rec_ : ∀ s1 s2 s3, step ge s1 E0 s2 → P s2 s3 → P s1 s3) :
    ∀ s1 s2, star step ge s1 E0 s2 → P s1 s2 := by
  have key : ∀ s1 t s2, star step ge s1 t s2 → t = E0 → P s1 s2 := by
    intro s1 t s2 h
    induction h with
    | star_refl s => intro _; exact base s
    | star_step sa ta sb tb sc tc hstep hstar heq ih =>
        intro heqE0
        have h12 : ta = E0 ∧ tb = E0 := by
          rw [heq] at heqE0
          exact List.append_eq_nil_iff.mp heqE0
        exact rec_ sa sb sc (h12.1 ▸ hstep) (ih h12.2)
  intro s1 s2 h
  exact key s1 E0 s2 h rfl


-- ** One or several transitions (transitive closure). --

/-- One or several transitions. Also known as the transitive closure of
    `step`. -/
inductive plus (ge : genv) : state → trace → state → Prop where
  | plus_left : ∀ s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 → star step ge s2 t2 s3 → t = t1 ++ t2 →
      plus ge s1 t s3

theorem plus_one (ge : genv) (s1 : state) (t : trace) (s2 : state)
    (h : step ge s1 t s2) : plus step ge s1 t s2 := by
  rw [show t = t ++ E0 from (List.append_nil t).symm]
  exact .plus_left s1 t s2 E0 s2 (t ++ E0) h (.star_refl s2) rfl

theorem plus_two (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : step ge s1 t1 s2) (h2 : step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 :=
  .plus_left s1 t1 s2 t2 s3 t h1 (star_one step ge s2 t2 s3 h2) heq

theorem plus_three (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t3 : trace) (s4 : state) (t : trace)
    (h1 : step ge s1 t1 s2) (h2 : step ge s2 t2 s3) (h3 : step ge s3 t3 s4)
    (heq : t = t1 ++ t2 ++ t3) : plus step ge s1 t s4 := by
  subst heq
  rw [List.append_assoc]
  exact .plus_left s1 t1 s2 (t2 ++ t3) s4 (t1 ++ (t2 ++ t3)) h1
    (star_two step ge s2 t2 s3 t3 s4 (t2 ++ t3) h2 h3 rfl) rfl

theorem plus_four (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t3 : trace) (s4 : state) (t4 : trace) (s5 : state) (t : trace)
    (h1 : step ge s1 t1 s2) (h2 : step ge s2 t2 s3) (h3 : step ge s3 t3 s4)
    (h4 : step ge s4 t4 s5) (heq : t = t1 ++ t2 ++ t3 ++ t4) : plus step ge s1 t s5 := by
  subst heq
  rw [List.append_assoc, List.append_assoc]
  exact .plus_left s1 t1 s2 (t2 ++ (t3 ++ t4)) s5 (t1 ++ (t2 ++ (t3 ++ t4))) h1
    (star_three step ge s2 t2 s3 t3 s4 t4 s5 (t2 ++ (t3 ++ t4)) h2 h3 h4 (by rw [List.append_assoc]))
    rfl

theorem plus_star (ge : genv) (s1 : state) (t : trace) (s2 : state)
    (h : plus step ge s1 t s2) : star step ge s1 t s2 := by
  cases h with
  | plus_left =>
      rename_i ta sb tb hstep heq hstar
      exact .star_step s1 ta sb tb s2 t hstep hstar heq

theorem plus_right (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : star step ge s1 t1 s2) (h2 : step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 := by
  cases h1 with
  | star_refl s =>
      rw [heq]
      simpa using plus_one step ge s1 t2 s3 h2
  | star_step =>
      rename_i ta sb tb hstep heq' hstar
      subst heq'
      rw [heq, List.append_assoc]
      exact .plus_left s1 ta sb (tb ++ t2) s3 (ta ++ (tb ++ t2)) hstep
        (star_right step ge sb tb s2 t2 s3 (tb ++ t2) hstar h2 rfl) rfl

theorem plus_left' (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : step ge s1 t1 s2) (h2 : plus step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 :=
  .plus_left s1 t1 s2 t2 s3 t h1 (plus_star step ge s2 t2 s3 h2) heq

theorem plus_right' (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : plus step ge s1 t1 s2) (h2 : step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 :=
  plus_right step ge s1 t1 s2 t2 s3 t (plus_star step ge s1 t1 s2 h1) h2 heq

theorem plus_star_trans (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : plus step ge s1 t1 s2) (h2 : star step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 := by
  cases h1 with
  | plus_left =>
      rename_i ta sb tb hstep heq' hstar
      subst heq'
      exact .plus_left s1 ta sb (tb ++ t2) s3 t hstep
        (star_trans step ge sb tb s2 hstar t2 s3 (tb ++ t2) h2 rfl)
        (by rw [heq, List.append_assoc])

theorem star_plus_trans (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : star step ge s1 t1 s2) (h2 : plus step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 := by
  cases h1 with
  | star_refl s => rw [heq]; simpa using h2
  | star_step =>
      rename_i ta sb tb hstep heq' hstar
      subst heq'
      rw [heq, List.append_assoc]
      exact .plus_left s1 ta sb (tb ++ t2) s3 (ta ++ (tb ++ t2)) hstep
        (star_trans step ge sb tb s2 hstar t2 s3 (tb ++ t2)
          (plus_star step ge s2 t2 s3 h2) rfl) rfl

theorem plus_trans (ge : genv) (s1 : state) (t1 : trace) (s2 : state) (t2 : trace)
    (s3 : state) (t : trace) (h1 : plus step ge s1 t1 s2) (h2 : plus step ge s2 t2 s3)
    (heq : t = t1 ++ t2) : plus step ge s1 t s3 :=
  plus_star_trans step ge s1 t1 s2 t2 s3 t h1 (plus_star step ge s2 t2 s3 h2) heq

theorem plus_inv (ge : genv) (s1 : state) (t : trace) (s2 : state)
    (h : plus step ge s1 t s2) :
    step ge s1 t s2 ∨
      ∃ s' t1 t2, step ge s1 t1 s' ∧ plus step ge s' t2 s2 ∧ t = t1 ++ t2 := by
  cases h with
  | plus_left =>
      rename_i t1 s2' t2 hstep heq hstar
      cases hstar with
      | star_refl s => left; simpa [heq] using hstep
      | star_step =>
          rename_i t2' s3' t2'' hstep' heq' hstar'
          right
          exact ⟨s2', t1, t2' ++ t2'', hstep, .plus_left s2' t2' s3' t2'' s2 (t2' ++ t2'')
            hstep' hstar' rfl, by rw [heq, heq']⟩

theorem star_inv (ge : genv) (s1 : state) (t : trace) (s2 : state)
    (h : star step ge s1 t s2) :
    (s2 = s1 ∧ t = E0) ∨ plus step ge s1 t s2 := by
  cases h with
  | star_refl s => left; exact ⟨rfl, rfl⟩
  | star_step =>
      rename_i ta sb tb hstep heq hstar
      right; exact .plus_left s1 ta sb tb s2 t hstep hstar heq



theorem plus_ind2 (ge : genv) (P : state → trace → state → Prop)
    (base : ∀ s1 t s2, step ge s1 t s2 → P s1 t s2)
    (ind : ∀ s1 t1 s2 t2 s3 t, step ge s1 t1 s2 → plus step ge s2 t2 s3 →
      P s2 t2 s3 → t = t1 ++ t2 → P s1 t s3) :
    ∀ s1 t s2, plus step ge s1 t s2 → P s1 t s2 := by
  have key : ∀ s1 t s2, star step ge s1 t s2 →
      ∀ s0 t0, step ge s0 t0 s1 → P s0 (t0 ++ t) s2 := by
    intro s1 t s2 h
    induction h with
    | star_refl s =>
        intro s0 t0 hstep
        simpa using base s0 t0 s hstep
    | star_step s1 t1 s2' t2 s3 t hstep hstar heq ih =>
        intro s0 t0 hstep0
        subst heq
        exact ind s0 t0 s1 (t1 ++ t2) s3 (t0 ++ (t1 ++ t2)) hstep0
          (.plus_left s1 t1 s2' t2 s3 (t1 ++ t2) hstep hstar rfl) (ih s1 t1 hstep) rfl
  intro s1 t s2 h
  cases h with
  | plus_left =>
      rename_i t1 s2' t2 hstep heq hstar
      subst heq; exact key s2' t2 s2 hstar s1 t1 hstep

theorem plus_E0_ind (ge : genv) (P : state → state → Prop)
    (h : ∀ s1 s2 s3, step ge s1 E0 s2 → star step ge s2 E0 s3 → P s1 s3) :
    ∀ s1 s2, plus step ge s1 E0 s2 → P s1 s2 := by
  intro s1 s2 hp
  cases hp with
  | plus_left =>
      rename_i t1 s2' t2 hstep heq hstar
      have h12 : t1 = E0 ∧ t2 = E0 := List.append_eq_nil_iff.mp heq.symm
      exact h s1 s2' s2 (h12.1 ▸ hstep) (h12.2 ▸ hstar)

-- ** Counted sequences of transitions. --

/-- Exactly `n` transitions. -/
inductive starN (ge : genv) : Nat → state → trace → state → Prop where
  | starN_refl : ∀ s, starN ge 0 s E0 s
  | starN_step : ∀ n s t t1 s' t2 s'',
      step ge s t1 s' → starN ge n s' t2 s'' → t = t1 ++ t2 →
      starN ge (n + 1) s t s''

theorem starN_star (ge : genv) (n : Nat) (s : state) (t : trace) (s' : state)
    (h : starN step ge n s t s') : star step ge s t s' := by
  induction h with
  | starN_refl s => exact .star_refl s
  | starN_step n s t t1 s' t2 s'' hstep hstarN heq ih =>
      exact .star_step s t1 s' t2 s'' t hstep ih heq

theorem star_starN (ge : genv) (s : state) (t : trace) (s' : state)
    (h : star step ge s t s') : ∃ n, starN step ge n s t s' := by
  induction h with
  | star_refl s => exact ⟨0, .starN_refl s⟩
  | star_step s1 t1 s2 t2 s3 t hstep hstar heq ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .starN_step n s1 t t1 s2 t2 s3 hstep hn heq⟩

-- ** Bounded-step-count reachability of a predicate ("eventually"). --

variable (final_state : state → CompCert.Int → Prop)

/-- `eventually n s P`: all transition sequences of length `n` starting from
    `s` either reach a state satisfying `P` (silently), or `s` can still take
    at least one more silent step towards such a state. -/
inductive eventually (ge : genv) : Nat → state → (state → Prop) → Prop where
  | eventually_now : ∀ s (P : state → Prop), P s → eventually ge 0 s P
  | eventually_later : ∀ n s (P : state → Prop),
      (∀ r, ¬ final_state s r) →
      (∀ t s', step ge s t s' → t = E0) →
      (∀ t s', step ge s t s' → eventually ge n s' P) →
      eventually ge (n + 1) s P

theorem eventually_one (ge : genv) (s : state) (P : state → Prop)
    (hfin : ∀ r, ¬ final_state s r)
    (hstep : ∀ t s', step ge s t s' → t = E0 ∧ P s') :
    eventually step final_state ge 1 s P :=
  .eventually_later 0 s P hfin
    (fun t s' hs => (hstep t s' hs).1)
    (fun t s' hs => .eventually_now s' P (hstep t s' hs).2)

theorem eventually_trans (ge : genv) (n1 : Nat) (s1 : state) (P1 : state → Prop)
    (n2 : Nat) (P2 : state → Prop) (h1 : eventually step final_state ge n1 s1 P1)
    (h2 : ∀ s2, P1 s2 → eventually step final_state ge n2 s2 P2) :
    eventually step final_state ge (n1 + n2) s1 P2 := by
  induction h1 with
  | eventually_now s P hP => simpa using h2 s hP
  | eventually_later n s P hfin ht hstep ih =>
      have hidx : n + 1 + n2 = (n + n2) + 1 := by omega
      rw [hidx]
      exact .eventually_later (n + n2) s P2 hfin ht (fun t s' hs => ih t s' hs h2)

theorem eventually_implies (ge : genv) (n : Nat) (s : state) (P1 P2 : state → Prop)
    (h : eventually step final_state ge n s P1) (himp : ∀ s, P1 s → P2 s) :
    eventually step final_state ge n s P2 := by
  have := eventually_trans step final_state ge n s P1 0 P2 h
    (fun s2 hs2 => .eventually_now s2 P2 (himp s2 hs2))
  simpa using this

theorem eventually_and_invariant (ge : genv) (Inv : state → Prop) (n : Nat) (s : state)
    (P : state → Prop) (hinv : ∀ s t s', step ge s t s' → Inv s → Inv s')
    (h : eventually step final_state ge n s P) (hs : Inv s) :
    eventually step final_state ge n s (fun s' => P s' ∧ Inv s') := by
  induction h with
  | eventually_now s P hP => exact .eventually_now s _ ⟨hP, hs⟩
  | eventually_later n s P hfin ht hstep ih =>
      refine .eventually_later n s _ hfin ht ?_
      intro t s' hstep'
      exact ih t s' hstep' (hinv s t s' hstep' hs)

end CLOSURES

-- ============================================================================
-- * Transition semantics
-- ============================================================================

/-- The general form of a transition semantics.

    Deviates from CompCert's `semantics` record: no `symbolenv` field — the
    file-header deviation note explains that we skip the abstract `Senv.t`
    module entirely. We do keep `genvtype` (unlike an earlier version of this
    port, which fixed the global environment to `Genv.t F V` directly): some
    languages' step relations need a global environment that is a wrapper
    around `Genv.t F V` carrying extra data (e.g. Clight's `genv`, which
    bundles a `Genv.t fundef type` with the `composite_env` needed for
    `sizeof`/`field_offset`). The `to_genv` projection recovers the
    `Genv.t F V` needed by `Events.match_traces` in `receptive`/`determinate`
    below, playing the role Coq's `Genv.to_senv` plays for `symbolenv`. -/
structure semantics (F V : Type) where
  state : Type
  genvtype : Type
  step : genvtype → state → trace → state → Prop
  initial_state : state → Prop
  final_state : state → CompCert.Int → Prop
  globalenv : genvtype
  to_genv : genvtype → Genv.t F V

variable {F V : Type}

/-- Handy notations, as plain defs (Lean has no direct analogue of Coq's
    `Notation ... := ...` inside a custom scope for this purpose). -/
def Step (L : semantics F V) : L.state → trace → L.state → Prop :=
  L.step L.globalenv

def Star (L : semantics F V) : L.state → trace → L.state → Prop :=
  star L.step L.globalenv

def Plus (L : semantics F V) : L.state → trace → L.state → Prop :=
  plus L.step L.globalenv

def Nostep (L : semantics F V) : L.state → Prop :=
  nostep L.step L.globalenv

def Eventually (L : semantics F V) : Nat → L.state → (L.state → Prop) → Prop :=
  eventually L.step L.final_state L.globalenv

-- ============================================================================
-- * Receptiveness and determinacy
-- ============================================================================

/-- All transitions of `L` carry at most one event. -/
def single_events (L : semantics F V) : Prop :=
  ∀ s t s', Step L s t s' → t.length ≤ 1

structure receptive (L : semantics F V) : Prop where
  sr_receptive : ∀ s t1 s1 t2,
    Step L s t1 s1 → Events.match_traces (L.to_genv L.globalenv) t1 t2 → ∃ s2, Step L s t2 s2
  sr_traces : single_events L

structure determinate (L : semantics F V) : Prop where
  sd_determ : ∀ s t1 s1 t2 s2,
    Step L s t1 s1 → Step L s t2 s2 →
      Events.match_traces (L.to_genv L.globalenv) t1 t2 ∧ (t1 = t2 → s1 = s2)
  sd_traces : single_events L
  sd_initial_determ : ∀ s1 s2, L.initial_state s1 → L.initial_state s2 → s1 = s2
  sd_final_nostep : ∀ s r, L.final_state s r → Nostep L s
  sd_final_determ : ∀ s r1 r2, L.final_state s r1 → L.final_state s r2 → r1 = r2

section DETERMINACY

theorem sd_determ_1 (L : semantics F V) (DET : determinate L)
    (s : L.state) (t1 : trace) (s1 : L.state) (t2 : trace) (s2 : L.state)
    (h1 : Step L s t1 s1) (h2 : Step L s t2 s2) :
    Events.match_traces (L.to_genv L.globalenv) t1 t2 :=
  (DET.sd_determ s t1 s1 t2 s2 h1 h2).1

theorem sd_determ_2 (L : semantics F V) (DET : determinate L)
    (s : L.state) (t : trace) (s1 s2 : L.state)
    (h1 : Step L s t s1) (h2 : Step L s t s2) : s1 = s2 :=
  (DET.sd_determ s t s1 t s2 h1 h2).2 rfl

theorem sd_determ_3 (L : semantics F V) (DET : determinate L)
    (s : L.state) (t : trace) (s1 s2 : L.state)
    (h1 : Step L s t s1) (h2 : Step L s E0 s2) : t = E0 ∧ s1 = s2 := by
  obtain ⟨hmt, himp⟩ := DET.sd_determ s t s1 E0 s2 h1 h2
  cases hmt with
  | match_traces_E0 => exact ⟨rfl, himp rfl⟩

/-- Two traces related by `match_traces` are either both empty or both
    singleton — the shape fact used by `star_determinacy` to split a
    length-≤-1 event trace equation. -/
private theorem match_traces_shape (ge : Genv.t F V) (t1 t2 : trace)
    (h : Events.match_traces ge t1 t2) : t1 = [] ↔ t2 = [] := by
  cases h <;> simp

theorem star_determinacy (L : semantics F V) (DET : determinate L)
    (s : L.state) (t : trace) (s' : L.state) (h : Star L s t s') :
    ∀ s'', Star L s t s'' → Star L s' E0 s'' ∨ Star L s'' E0 s' := by
  induction h with
  | star_refl s =>
      intro s'' h2
      left; exact h2
  | star_step s1 t1 s2 t2 s3 t hstep hstar heq ih =>
      intro s'' h2
      subst heq
      rcases star_inv L.step L.globalenv s1 (t1 ++ t2) s'' h2 with ⟨heqs, heq0⟩ | hplus
      · right
        rw [heqs, ← heq0]
        exact .star_step s1 t1 s2 t2 s3 (t1 ++ t2) hstep hstar rfl
      · have hex : ∃ t0 s4 t3, Step L s1 t0 s4 ∧ Star L s4 t3 s'' ∧ t1 ++ t2 = t0 ++ t3 := by
          rcases plus_inv L.step L.globalenv s1 (t1 ++ t2) s'' hplus with
            hstep0 | ⟨s4, ta, tb, hstepa, hplusb, heqab⟩
          · exact ⟨t1 ++ t2, s'', E0, hstep0, .star_refl s'', by simp⟩
          · exact ⟨ta, s4, tb, hstepa, plus_star L.step L.globalenv s4 tb s'' hplusb, heqab⟩
        obtain ⟨t0, s4, t3, hstep', hstar', heq'⟩ := hex
        have hlen1 : t1.length ≤ 1 := DET.sd_traces s1 t1 s2 hstep
        have hlen0 : t0.length ≤ 1 := DET.sd_traces s1 t0 s4 hstep'
        have hmt : Events.match_traces (L.to_genv L.globalenv) t1 t0 :=
          sd_determ_1 L DET s1 t1 s2 t0 s4 hstep hstep'
        have hshape : t1 = [] ↔ t0 = [] := match_traces_shape (L.to_genv L.globalenv) t1 t0 hmt
        have hsplit : t1 = t0 ∧ t2 = t3 := by
          by_cases h1 : t1 = []
          · have h0 : t0 = [] := hshape.mp h1
            subst h1; subst h0
            simpa using heq'
          · have h0 : t0 ≠ [] := fun h => h1 (hshape.mpr h)
            obtain ⟨a, as, ha⟩ := List.exists_cons_of_ne_nil h1
            obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil h0
            have has : as = [] := by
              subst ha
              simp only [List.length_cons] at hlen1
              exact List.length_eq_zero_iff.mp (by omega)
            have hbs : bs = [] := by
              subst hb
              simp only [List.length_cons] at hlen0
              exact List.length_eq_zero_iff.mp (by omega)
            subst ha hb has hbs
            simp only [List.cons_append] at heq'
            obtain ⟨hab, ht⟩ := List.cons.injEq .. |>.mp heq'
            subst hab
            exact ⟨rfl, ht⟩
        obtain ⟨ht10, ht23⟩ := hsplit
        subst ht10
        have hs24 : s2 = s4 := sd_determ_2 L DET s1 t1 s2 s4 hstep hstep'
        subst hs24
        subst ht23
        exact ih s'' hstar'

end DETERMINACY

end Smallstep
