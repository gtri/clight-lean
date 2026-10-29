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

import CLightLean.Exec.CSmithStep

/-!
Executor-only characterization facts for the owned fixed-signature checksum
helper.

No theorem here claims that the concrete `EF_external` transition is a stock
`step2` transition. `Events.external_functions_sem` is axiomatic, so the stock
semantics does not determine this helper's output, result, or memory behavior.
Establishing relational correspondence requires a future separate CSmith
external-model specialization. Internal branches continue to use the existing
`stepInternal` soundness surface.
-/

namespace CLightLean.Exec

variable [Archi]

/-- The fixed helper has the exact executor-only output, result, and
memory-preservation behavior promised by the owned companion C runtime. -/
theorem csmithChecksumPrint_exact (runtime : Runtime) (memory : Memory.mem)
    (checksum : CompCert.Int) :
    csmithChecksumPrint runtime memory [.Vint checksum] =
      .ok
        { runtime := Runtime.appendStdout runtime (csmithChecksumOutput checksum.unsigned)
          memory := memory
          result := .Vint (CompCert.Int.repr ((csmithChecksumOutput checksum.unsigned).size : Int)) } := by
  rfl

/-- The exact admitted external transition is silent in `Events.trace` while
updating only executor runtime state and the return-state payload. -/
theorem stepCSmith_checksumPrint_exact (ge : genv) (runtime : Runtime)
    (memory : Memory.mem) (checksum : CompCert.Int) (k : cont) :
    stepCSmith ge runtime
        (.Callstate
          (.External (.EF_external "csmith_checksum_print" csmithChecksumPrintSignature)
            csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
          [.Vint checksum] k memory) =
      .ok
        { runtime := Runtime.appendStdout runtime (csmithChecksumOutput checksum.unsigned)
          trace := Events.E0
          state := .Returnstate
            (.Vint (CompCert.Int.repr ((csmithChecksumOutput checksum.unsigned).size : Int)))
            k memory } := by
  rfl

/-- The owned `fabs` action is pure and returns the CompCert-compatible
absolute value of its one double-precision argument. -/
theorem csmithFabs_exact (runtime : Runtime) (memory : Memory.mem)
    (value : CompCert.Float64) :
    csmithFabs runtime memory [.Vfloat value] =
      .ok
        { runtime := runtime
          memory := memory
          result := .Vfloat (CompCert.Float64.abs value) } := by
  rfl

/-- The owned `fabsf` action is pure and returns the CompCert-compatible
absolute value of its one single-precision argument. -/
theorem csmithFabsf_exact (runtime : Runtime) (memory : Memory.mem)
    (value : CompCert.Float32) :
    csmithFabsf runtime memory [.Vsingle value] =
      .ok
        { runtime := runtime
          memory := memory
          result := .Vsingle (CompCert.Float32.abs value) } := by
  rfl

/-- The exact admitted `fabs` call makes a silent, memory-preserving CSmith
transition. -/
theorem stepCSmith_fabs_exact (ge : genv) (runtime : Runtime)
    (memory : Memory.mem) (value : CompCert.Float64) (k : cont) :
    stepCSmith ge runtime
        (.Callstate
          (.External (.EF_external "fabs" csmithFabsSignature)
            csmithFabsArgTypes csmithFabsResultType cc_default)
          [.Vfloat value] k memory) =
      .ok
        { runtime := runtime
          trace := Events.E0
          state := .Returnstate (.Vfloat (CompCert.Float64.abs value)) k memory } := by
  rfl

/-- The exact admitted `fabsf` call makes a silent, memory-preserving CSmith
transition. -/
theorem stepCSmith_fabsf_exact (ge : genv) (runtime : Runtime)
    (memory : Memory.mem) (value : CompCert.Float32) (k : cont) :
    stepCSmith ge runtime
        (.Callstate
          (.External (.EF_external "fabsf" csmithFabsfSignature)
            csmithFabsfArgTypes csmithFabsfResultType cc_default)
          [.Vsingle value] k memory) =
      .ok
        { runtime := runtime
          trace := Events.E0
          state := .Returnstate (.Vsingle (CompCert.Float32.abs value)) k memory } := by
  rfl

end CLightLean.Exec
