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
The explicit relational boundary for owned CSmith runtime helpers.

`step2` remains the authoritative stock relation.  This additive relation
retains each stock transition whose source is not an external call in the
owned CSmith runtime namespace, while supplying the fixed-signature transitions
used by the checksum bootstrap and CSmith safe float wrappers.  In particular,
it does not derive concrete actions from the stock opaque external-call model.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Recognize every external `Callstate` whose name belongs to the owned CSmith
runtime surface.  Signature, Clight type annotations, calling convention,
arguments, continuation, and memory are deliberately ignored: the `base` rule
must exclude malformed helper-named calls as well as the well-formed owned
calls below. -/
def isCSmithOwnedExternalState : state → Prop
  | .Callstate (.External (.EF_external name _) _ _ _) _ _ _ =>
      name = "csmith_checksum_print" ∨ name = "fabs" ∨ name = "fabsf"
  | _ => False

/--
`step2` with the owned CSmith external-call specializations.

The `base` constructor imports stock behavior only from states outside the
owned runtime namespace.  The remaining constructors specify the admitted
fixed ABIs and silent, memory-preserving return transitions.  Formatted
checksum bytes belong to executor runtime state, so every relational
transition's `Events.trace` is `Events.E0`.
-/
inductive csmithStep2 (ge : genv) : state → Events.trace → state → Prop where
  | base {s : state} {t : Events.trace} {s' : state} :
      ¬ isCSmithOwnedExternalState s →
      step2 ge s t s' →
      csmithStep2 ge s t s'
  | checksum_external (checksum : CompCert.Int) (k : cont) (m : Memory.mem) :
      csmithStep2 ge
        (.Callstate
          (.External (.EF_external "csmith_checksum_print" csmithChecksumPrintSignature)
            csmithChecksumPrintArgTypes csmithChecksumPrintResultType cc_default)
          [.Vint checksum] k m)
        Events.E0
        (.Returnstate
          (.Vint (CompCert.Int.repr ((csmithChecksumOutput checksum.unsigned).size : Int)))
          k m)
  | fabs_external (value : CompCert.Float64) (k : cont) (m : Memory.mem) :
      csmithStep2 ge
        (.Callstate
          (.External (.EF_external "fabs" csmithFabsSignature)
            csmithFabsArgTypes csmithFabsResultType cc_default)
          [.Vfloat value] k m)
        Events.E0
        (.Returnstate (.Vfloat (CompCert.Float64.abs value)) k m)
  | fabsf_external (value : CompCert.Float32) (k : cont) (m : Memory.mem) :
      csmithStep2 ge
        (.Callstate
          (.External (.EF_external "fabsf" csmithFabsfSignature)
            csmithFabsfArgTypes csmithFabsfResultType cc_default)
          [.Vsingle value] k m)
        Events.E0
        (.Returnstate (.Vsingle (CompCert.Float32.abs value)) k m)

/-- Package the specialized relation with the unchanged Clight program-entry
and final-state definitions.  Only the owned runtime transitions differ from
the stock `semantics2` package. -/
def csmithSemantics2 (p : program_type function) :
    Smallstep.semantics (fundef_type function) type :=
  let ge := globalenv p
  { state := state
    genvtype := genv
    step := csmithStep2
    initial_state := initial_state p
    final_state := final_state
    globalenv := ge
    to_genv := genv.genv_genv }

end CLightLean.Exec
