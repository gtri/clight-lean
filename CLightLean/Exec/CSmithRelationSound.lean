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

import CLightLean.Exec.CSmithRelation
import CLightLean.Exec.CSmithStepSound
import CLightLean.Exec.StepSound

/-!
Narrow correspondence facts for `csmithStep2`.

These theorems establish only the exact owned checksum external action and
the constructor-level stock embedding, together with the full dispatcher
correspondence theorem.  The executor runtime component remains deliberately
outside the relational statement.
-/

namespace CLightLean.Exec

variable [Archi]

/-- The transition returned by `stepCSmith` for the exact owned helper call is
the corresponding `csmithStep2` transition.  This theorem is intentionally
restricted to the generated helper `Callstate`; it makes no stock `step2`
claim for this external action. -/
theorem stepCSmith_checksumPrint_csmithStep2
    (ge : genv) (runtime : Runtime) (memory : Memory.mem) (checksum : CompCert.Int)
    (k : cont) (transition : CSmithTransition)
    (h : stepCSmith ge runtime
      (.Callstate
        (.External (.EF_external "csmith_checksum_print" csmithChecksumPrintSignature)
          csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
        [.Vint checksum] k memory) = .ok transition) :
    csmithStep2 ge
      (.Callstate
        (.External (.EF_external "csmith_checksum_print" csmithChecksumPrintSignature)
          csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
        [.Vint checksum] k memory)
      transition.trace transition.state := by
  rw [stepCSmith_checksumPrint_exact] at h
  cases h
  exact .checksum_external checksum k memory

/-- The transition returned by `stepCSmith` for the exact owned `fabs` call is
the corresponding CSmith-safe-float transition. -/
theorem stepCSmith_fabs_csmithStep2
    (ge : genv) (runtime : Runtime) (memory : Memory.mem) (value : CompCert.Float64)
    (k : cont) (transition : CSmithTransition)
    (h : stepCSmith ge runtime
      (.Callstate
        (.External (.EF_external "fabs" csmithFabsSignature)
          csmithFabsArgTypes csmithFabsResultType cc_default)
        [.Vfloat value] k memory) = .ok transition) :
    csmithStep2 ge
      (.Callstate
        (.External (.EF_external "fabs" csmithFabsSignature)
          csmithFabsArgTypes csmithFabsResultType cc_default)
        [.Vfloat value] k memory)
      transition.trace transition.state := by
  rw [stepCSmith_fabs_exact] at h
  cases h
  exact .fabs_external value k memory

/-- The transition returned by `stepCSmith` for the exact owned `fabsf` call is
the corresponding CSmith-safe-float transition. -/
theorem stepCSmith_fabsf_csmithStep2
    (ge : genv) (runtime : Runtime) (memory : Memory.mem) (value : CompCert.Float32)
    (k : cont) (transition : CSmithTransition)
    (h : stepCSmith ge runtime
      (.Callstate
        (.External (.EF_external "fabsf" csmithFabsfSignature)
          csmithFabsfArgTypes csmithFabsfResultType cc_default)
        [.Vsingle value] k memory) = .ok transition) :
    csmithStep2 ge
      (.Callstate
        (.External (.EF_external "fabsf" csmithFabsfSignature)
          csmithFabsfArgTypes csmithFabsfResultType cc_default)
        [.Vsingle value] k memory)
      transition.trace transition.state := by
  rw [stepCSmith_fabsf_exact] at h
  cases h
  exact .fabsf_external value k memory

/-- Every successful CSmith-aware executor transition is represented by the
specialized relational step.  The executor runtime component is intentionally
not mentioned: it is not part of `csmithStep2`. -/
theorem stepCSmith_sound
    (ge : genv) (runtime : Runtime) (s : state) (transition : CSmithTransition)
    (h : stepCSmith ge runtime s = .ok transition) :
    csmithStep2 ge s transition.trace transition.state := by
  cases s with
  | State f stmt k e le m =>
      cases hs : stepInternal ge (.State f stmt k e le m) with
      | error err =>
          simp [stepCSmith, hs] at h
      | ok nextState =>
          simp [stepCSmith, hs] at h
          cases h
          exact .base (by simp [isCSmithOwnedExternalState])
            (stepInternal_sound ge _ _ hs)
  | Callstate fd args k m =>
      cases fd with
      | Internal f =>
          cases hs : stepInternal ge (.Callstate (.Internal f) args k m) with
          | error err =>
              simp [stepCSmith, hs] at h
          | ok nextState =>
              simp [stepCSmith, hs] at h
              cases h
              exact .base (by simp [isCSmithOwnedExternalState])
                (stepInternal_sound ge _ _ hs)
      | External ef argTypes resultType cconv =>
          cases ef with
          | EF_external name sig =>
              by_cases hname : name = "csmith_checksum_print"
              · subst name
                by_cases hsig : sig = csmithChecksumPrintSignature
                · subst sig
                  by_cases hargTypes : argTypes = csmithChecksumPrintArgTypes
                  · subst argTypes
                    by_cases hresultType : resultType = csmithChecksumPrintResultType
                    · subst resultType
                      by_cases hcconv : cconv = cc_default
                      · subst cconv
                        cases args with
                        | nil =>
                            simp [stepCSmith, isCSmithChecksumPrintSignature,
                              csmithChecksumPrint] at h
                        | cons arg rest =>
                            cases rest with
                            | nil =>
                                cases arg with
                                | Vint checksum =>
                                    exact stepCSmith_checksumPrint_csmithStep2 ge runtime m
                                      checksum k transition h
                                | _ =>
                                    simp [stepCSmith, isCSmithChecksumPrintSignature,
                                      csmithChecksumPrint] at h
                            | cons arg rest =>
                                simp [stepCSmith, isCSmithChecksumPrintSignature,
                                  csmithChecksumPrint] at h
                      · exfalso
                        have hfalse :
                            isCSmithChecksumPrintSignature csmithChecksumPrintSignature
                              csmithChecksumPrintArgTypes csmithChecksumPrintResultType cconv = false := by
                          simp [isCSmithChecksumPrintSignature, hcconv]
                        simp [stepCSmith, hfalse] at h
                    · exfalso
                      have hfalse :
                          isCSmithChecksumPrintSignature csmithChecksumPrintSignature
                            csmithChecksumPrintArgTypes resultType cconv = false := by
                        simp [isCSmithChecksumPrintSignature, hresultType]
                      simp [stepCSmith, hfalse] at h
                  · exfalso
                    have hfalse :
                        isCSmithChecksumPrintSignature csmithChecksumPrintSignature argTypes
                          resultType cconv = false := by
                      simp [isCSmithChecksumPrintSignature, hargTypes]
                    simp [stepCSmith, hfalse] at h
                · exfalso
                  have hfalse :
                      isCSmithChecksumPrintSignature sig argTypes resultType cconv = false := by
                    simp [isCSmithChecksumPrintSignature, hsig]
                  simp [stepCSmith, hfalse] at h
              · by_cases hfabs : name = "fabs"
                · subst name
                  by_cases hsig : sig = csmithFabsSignature
                  · subst sig
                    by_cases hargTypes : argTypes = csmithFabsArgTypes
                    · subst argTypes
                      by_cases hresultType : resultType = csmithFabsResultType
                      · subst resultType
                        by_cases hcconv : cconv = cc_default
                        · subst cconv
                          cases args with
                          | nil =>
                              simp [stepCSmith, isCSmithFabsSignature, csmithFabs] at h
                          | cons arg rest =>
                              cases rest with
                              | nil =>
                                  cases arg with
                                  | Vfloat value =>
                                      exact stepCSmith_fabs_csmithStep2 ge runtime m
                                        value k transition h
                                  | _ =>
                                      simp [stepCSmith, isCSmithFabsSignature, csmithFabs] at h
                              | cons arg rest =>
                                  simp [stepCSmith, isCSmithFabsSignature, csmithFabs] at h
                        · exfalso
                          have hfalse :
                              isCSmithFabsSignature csmithFabsSignature
                                csmithFabsArgTypes csmithFabsResultType cconv = false := by
                            simp [isCSmithFabsSignature, hcconv]
                          simp [stepCSmith, hfalse] at h
                      · exfalso
                        have hfalse :
                            isCSmithFabsSignature csmithFabsSignature csmithFabsArgTypes
                              resultType cconv = false := by
                          simp [isCSmithFabsSignature, hresultType]
                        simp [stepCSmith, hfalse] at h
                    · exfalso
                      have hfalse :
                          isCSmithFabsSignature csmithFabsSignature argTypes
                            resultType cconv = false := by
                        simp [isCSmithFabsSignature, hargTypes]
                      simp [stepCSmith, hfalse] at h
                  · exfalso
                    have hfalse :
                        isCSmithFabsSignature sig argTypes resultType cconv = false := by
                      simp [isCSmithFabsSignature, hsig]
                    simp [stepCSmith, hfalse] at h
                · by_cases hfabsf : name = "fabsf"
                  · subst name
                    by_cases hsig : sig = csmithFabsfSignature
                    · subst sig
                      by_cases hargTypes : argTypes = csmithFabsfArgTypes
                      · subst argTypes
                        by_cases hresultType : resultType = csmithFabsfResultType
                        · subst resultType
                          by_cases hcconv : cconv = cc_default
                          · subst cconv
                            cases args with
                            | nil =>
                                simp [stepCSmith, isCSmithFabsfSignature, csmithFabsf] at h
                            | cons arg rest =>
                                cases rest with
                                | nil =>
                                    cases arg with
                                    | Vsingle value =>
                                        exact stepCSmith_fabsf_csmithStep2 ge runtime m
                                          value k transition h
                                    | _ =>
                                        simp [stepCSmith, isCSmithFabsfSignature, csmithFabsf] at h
                                | cons arg rest =>
                                    simp [stepCSmith, isCSmithFabsfSignature, csmithFabsf] at h
                          · exfalso
                            have hfalse :
                                isCSmithFabsfSignature csmithFabsfSignature
                                  csmithFabsfArgTypes csmithFabsfResultType cconv = false := by
                              simp [isCSmithFabsfSignature, hcconv]
                            simp [stepCSmith, hfalse] at h
                        · exfalso
                          have hfalse :
                              isCSmithFabsfSignature csmithFabsfSignature csmithFabsfArgTypes
                                resultType cconv = false := by
                            simp [isCSmithFabsfSignature, hresultType]
                          simp [stepCSmith, hfalse] at h
                      · exfalso
                        have hfalse :
                            isCSmithFabsfSignature csmithFabsfSignature argTypes
                              resultType cconv = false := by
                          simp [isCSmithFabsfSignature, hargTypes]
                        simp [stepCSmith, hfalse] at h
                    · exfalso
                      have hfalse :
                          isCSmithFabsfSignature sig argTypes resultType cconv = false := by
                        simp [isCSmithFabsfSignature, hsig]
                      simp [stepCSmith, hfalse] at h
                  · exfalso
                    simp [stepCSmith, hname, hfabs, hfabsf] at h
          | _ =>
              exfalso
              simp [stepCSmith, stepInternal] at h
  | Returnstate value k m =>
      cases hs : stepInternal ge (.Returnstate value k m) with
      | error err =>
          simp [stepCSmith, hs] at h
      | ok nextState =>
          simp [stepCSmith, hs] at h
          cases h
          exact .base (by simp [isCSmithOwnedExternalState])
            (stepInternal_sound ge _ _ hs)

/-- Any stock `step2` transition whose source is outside the owned CSmith
runtime namespace is admitted unchanged by the specialized relation. -/
theorem step2_to_csmithStep2 {ge : genv} {s : state} {t : Events.trace} {s' : state}
    (hnot : ¬ isCSmithOwnedExternalState s) (hstep : step2 ge s t s') :
    csmithStep2 ge s t s' :=
  .base hnot hstep

end CLightLean.Exec
