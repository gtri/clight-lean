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

import CLightLean.Exec.CSmithRun
import CLightLean.Exec.CSmithRelationSound
import CLightLean.Exec.ProgramSound
import CLightLean.Exec.RunSound

/-!
Correspondence facts for the bounded CSmith-aware runner.

The worker accumulates a trace prefix, whereas `Smallstep.star` describes the
suffix executed from its current state.  The private worker lemmas below make
that split explicit and are specialized to the empty prefix by the public
runner theorems.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A completed worker run has a relational execution for precisely the trace
suffix appended after its input prefix, ending in an authoritative final state.
-/
private theorem runCSmithLoop_completed_sound (ge : genv) (fuel : Nat) :
    ∀ (runtime : Runtime) (tracePrefix : Events.trace) (currentState : state) (initialSteps : Nat)
      (runtime' : Runtime) (outputTrace : Events.trace) (result : CompCert.Int)
      (outputSteps : Nat),
      runCSmithLoop ge fuel runtime tracePrefix currentState initialSteps =
          .completed runtime' outputTrace result outputSteps →
      ∃ finalState suffix,
        outputTrace = tracePrefix ++ suffix ∧
        Smallstep.star csmithStep2 ge currentState suffix finalState ∧
        final_state finalState result := by
  induction fuel with
  | zero =>
      intro runtime tracePrefix currentState initialSteps runtime' outputTrace result outputSteps h
      cases hfinal : finalReturn? currentState with
      | some finalResult =>
          simp only [runCSmithLoop, hfinal] at h
          cases h
          exact ⟨currentState, Events.E0, by simp, .star_refl currentState,
            finalReturn?_sound hfinal⟩
      | none =>
          simp [runCSmithLoop, hfinal] at h
  | succ fuel ih =>
      intro runtime tracePrefix currentState initialSteps runtime' outputTrace result outputSteps h
      cases hfinal : finalReturn? currentState with
      | some finalResult =>
          simp only [runCSmithLoop, hfinal] at h
          cases h
          exact ⟨currentState, Events.E0, by simp, .star_refl currentState,
            finalReturn?_sound hfinal⟩
      | none =>
          cases hstep : stepCSmith ge runtime currentState with
          | error error =>
              cases error <;> simp [runCSmithLoop, hfinal, hstep] at h
          | ok transition =>
              have hrec :
                  runCSmithLoop ge fuel transition.runtime (tracePrefix ++ transition.trace)
                    transition.state (initialSteps + 1) =
                    .completed runtime' outputTrace result outputSteps := by
                simpa [runCSmithLoop, hfinal, hstep] using h
              obtain ⟨finalState, suffix, htrace, hstar, hfinalState⟩ :=
                ih transition.runtime (tracePrefix ++ transition.trace) transition.state
                  (initialSteps + 1) runtime' outputTrace result outputSteps hrec
              refine ⟨finalState, transition.trace ++ suffix, ?_, ?_, hfinalState⟩
              · simpa [List.append_assoc] using htrace
              · exact .star_step currentState transition.trace transition.state suffix finalState
                  (transition.trace ++ suffix)
                  (CLightLean.Exec.stepCSmith_sound ge runtime currentState transition hstep) hstar rfl

/-- A fuel-exhausted worker run has a relational execution for precisely the
trace suffix appended after its input prefix. -/
private theorem runCSmithLoop_fuelExhausted_sound (ge : genv) (fuel : Nat) :
    ∀ (runtime : Runtime) (tracePrefix : Events.trace) (currentState : state) (initialSteps : Nat)
      (runtime' : Runtime) (outputTrace : Events.trace) (exhaustedState : state)
      (outputSteps : Nat),
      runCSmithLoop ge fuel runtime tracePrefix currentState initialSteps =
          .fuelExhausted runtime' outputTrace exhaustedState outputSteps →
      ∃ suffix,
        outputTrace = tracePrefix ++ suffix ∧
        Smallstep.star csmithStep2 ge currentState suffix exhaustedState := by
  induction fuel with
  | zero =>
      intro runtime tracePrefix currentState initialSteps runtime' outputTrace exhaustedState outputSteps h
      cases hfinal : finalReturn? currentState with
      | some finalResult =>
          simp [runCSmithLoop, hfinal] at h
      | none =>
          simp only [runCSmithLoop, hfinal] at h
          cases h
          exact ⟨Events.E0, by simp, .star_refl currentState⟩
  | succ fuel ih =>
      intro runtime tracePrefix currentState initialSteps runtime' outputTrace exhaustedState outputSteps h
      cases hfinal : finalReturn? currentState with
      | some finalResult =>
          simp [runCSmithLoop, hfinal] at h
      | none =>
          cases hstep : stepCSmith ge runtime currentState with
          | error error =>
              cases error <;> simp [runCSmithLoop, hfinal, hstep] at h
          | ok transition =>
              have hrec :
                  runCSmithLoop ge fuel transition.runtime (tracePrefix ++ transition.trace)
                    transition.state (initialSteps + 1) =
                    .fuelExhausted runtime' outputTrace exhaustedState outputSteps := by
                simpa [runCSmithLoop, hfinal, hstep] using h
              obtain ⟨suffix, htrace, hstar⟩ :=
                ih transition.runtime (tracePrefix ++ transition.trace) transition.state
                  (initialSteps + 1) runtime' outputTrace exhaustedState outputSteps hrec
              refine ⟨transition.trace ++ suffix, ?_, ?_⟩
              · simpa [List.append_assoc] using htrace
              · exact .star_step currentState transition.trace transition.state suffix exhaustedState
                  (transition.trace ++ suffix)
                  (CLightLean.Exec.stepCSmith_sound ge runtime currentState transition hstep) hstar rfl

/-- A completed bounded CSmith-aware execution corresponds to a finite
`csmithStep2` execution ending in an authoritative final state. -/
theorem runCSmithFromFuel_completed_sound
    (ge : genv) (fuel : Nat) (runtime : Runtime) (initialState : state)
    (runtime' : Runtime) (trace : Events.trace) (result : CompCert.Int) (steps : Nat)
    (h : runCSmithFromFuel ge fuel runtime initialState =
      .completed runtime' trace result steps) :
    ∃ finalState,
      Smallstep.star csmithStep2 ge initialState trace finalState ∧
      final_state finalState result := by
  change runCSmithLoop ge fuel runtime Events.E0 initialState 0 =
    .completed runtime' trace result steps at h
  obtain ⟨finalState, suffix, htrace, hstar, hfinalState⟩ :=
    runCSmithLoop_completed_sound ge fuel runtime Events.E0 initialState 0
      runtime' trace result steps h
  refine ⟨finalState, ?_, hfinalState⟩
  rw [htrace]
  simpa using hstar

/-- A fuel-exhausted bounded CSmith-aware execution corresponds to a finite
`csmithStep2` execution ending at the reported current state. -/
theorem runCSmithFromFuel_fuelExhausted_sound
    (ge : genv) (fuel : Nat) (runtime : Runtime) (initialState : state)
    (runtime' : Runtime) (trace : Events.trace) (currentState : state) (steps : Nat)
    (h : runCSmithFromFuel ge fuel runtime initialState =
      .fuelExhausted runtime' trace currentState steps) :
    Smallstep.star csmithStep2 ge initialState trace currentState := by
  change runCSmithLoop ge fuel runtime Events.E0 initialState 0 =
    .fuelExhausted runtime' trace currentState steps at h
  obtain ⟨suffix, htrace, hstar⟩ :=
    runCSmithLoop_fuelExhausted_sound ge fuel runtime Events.E0 initialState 0
      runtime' trace currentState steps h
  rw [htrace]
  simpa using hstar

/-- A completed bounded whole-program CSmith-aware execution starts from an
authoritative Clight initial state and corresponds to a finite `csmithStep2`
execution ending in an authoritative final state.  The executable runtime is
intentionally not represented by the relational semantics. -/
theorem runCSmithProgramFuel_completed_sound
    (p : program_type function) (fuel : Nat)
    (runtime : Runtime) (trace : Events.trace) (result : CompCert.Int) (steps : Nat)
    (h : runCSmithProgramFuel p fuel = .ok (.completed runtime trace result steps)) :
    ∃ initialState finalState,
      initial_state p initialState ∧
      Smallstep.star csmithStep2 (globalenv p) initialState trace finalState ∧
      final_state finalState result := by
  unfold runCSmithProgramFuel at h
  cases hinitial : initialState p with
  | error error =>
      simp [hinitial] at h
  | ok initialState =>
      have hrun : runCSmithFromFuel (globalenv p) fuel Runtime.empty initialState =
          .completed runtime trace result steps := by
        simpa [hinitial, runCSmithFuel] using h
      obtain ⟨finalState, hstar, hfinal⟩ :=
        runCSmithFromFuel_completed_sound (globalenv p) fuel Runtime.empty initialState
          runtime trace result steps hrun
      exact ⟨initialState, finalState, initialState_sound p initialState hinitial, hstar, hfinal⟩

/-- A fuel-exhausted bounded whole-program CSmith-aware execution has executed
a finite `csmithStep2` prefix from an authoritative Clight initial state to the
reported current state.  The executable runtime is intentionally not
represented by the relational semantics. -/
theorem runCSmithProgramFuel_fuelExhausted_sound
    (p : program_type function) (fuel : Nat)
    (runtime : Runtime) (trace : Events.trace) (currentState : state) (steps : Nat)
    (h : runCSmithProgramFuel p fuel =
      .ok (.fuelExhausted runtime trace currentState steps)) :
    ∃ initialState,
      initial_state p initialState ∧
      Smallstep.star csmithStep2 (globalenv p) initialState trace currentState := by
  unfold runCSmithProgramFuel at h
  cases hinitial : initialState p with
  | error error =>
      simp [hinitial] at h
  | ok initialState =>
      have hrun : runCSmithFromFuel (globalenv p) fuel Runtime.empty initialState =
          .fuelExhausted runtime trace currentState steps := by
        simpa [hinitial, runCSmithFuel] using h
      exact ⟨initialState, initialState_sound p initialState hinitial,
        runCSmithFromFuel_fuelExhausted_sound (globalenv p) fuel Runtime.empty initialState
          runtime trace currentState steps hrun⟩

end CLightLean.Exec
