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

import CLightLean.Exec.CSmithRuntimeMemory
import CLightLean.Exec.Step

/-!
Additive CSmith-aware single-step execution.

This module preserves `stepInternal` and its internal-only API. It adds the
owned, fixed-signature checksum action `csmith_checksum_print(unsigned int)`,
plus the pure `fabs` and `fabsf` calls required by CSmith's safe floating
wrappers. The checksum action updates executor-only stdout bytes; all admitted
actions deliberately emit `Events.E0`, since modeled stdout is not a CompCert
event trace.

This is not a concrete theorem about the stock `step2` external transition.
For `EF_external`, `Events.external_functions_sem` is axiomatic, so it does
not specify the output, result, or memory behavior of these actions. The
existing checksum relation remains intentionally narrow; the `fabs` and
`fabsf` actions have executor-only specifications in this milestone.
-/

namespace CLightLean.Exec

variable [Archi]

/-- The exact CompCert signature exported by the owned checksum helper. -/
def csmithChecksumPrintSignature : signature :=
  { sig_args := [.Xint]
    sig_res := .Xint
    sig_cc := cc_default }

/-- The Clight fixed argument type exported alongside the helper signature. -/
def csmithChecksumPrintArgTypes : List type :=
  [.Tint .I32 .Unsigned noattr]

/-- The Clight result type exported alongside the helper signature. -/
def csmithChecksumPrintResultType : type := type_int32s

/-- Exact C ABI of CSmith safe-wrapper support function `fabs`. -/
def csmithFabsSignature : signature :=
  { sig_args := [.Xfloat]
    sig_res := .Xfloat
    sig_cc := cc_default }

/-- Exact Clight argument type of `fabs`. -/
def csmithFabsArgTypes : List type :=
  [.Tfloat .F64 noattr]

/-- Exact Clight result type of `fabs`. -/
def csmithFabsResultType : type := .Tfloat .F64 noattr

/-- Exact C ABI of CSmith safe-wrapper support function `fabsf`. -/
def csmithFabsfSignature : signature :=
  { sig_args := [.Xsingle]
    sig_res := .Xsingle
    sig_cc := cc_default }

/-- Exact Clight argument type of `fabsf`. -/
def csmithFabsfArgTypes : List type :=
  [.Tfloat .F32 noattr]

/-- Exact Clight result type of `fabsf`. -/
def csmithFabsfResultType : type := .Tfloat .F32 noattr

/--
Validate every generated fixed-signature field carried by an external fundef.
Matching the helper's string name alone is intentionally insufficient: this
bootstrap path admits only its one `unsigned int -> int`, non-vararg ABI.
-/
def isCSmithChecksumPrintSignature (sig : signature) (argTypes : List type)
    (resultType : type) (cconv : calling_convention) : Bool :=
  sig == csmithChecksumPrintSignature &&
    argTypes == csmithChecksumPrintArgTypes &&
    resultType == csmithChecksumPrintResultType &&
    cconv == cc_default

/-- Validate the fixed non-vararg `double fabs(double)` ABI required by the
CSmith float safe wrappers. -/
def isCSmithFabsSignature (sig : signature) (argTypes : List type)
    (resultType : type) (cconv : calling_convention) : Bool :=
  sig == csmithFabsSignature &&
    argTypes == csmithFabsArgTypes &&
    resultType == csmithFabsResultType &&
    cconv == cc_default

/-- Validate the fixed non-vararg `float fabsf(float)` ABI required by the
CSmith float safe wrappers. -/
def isCSmithFabsfSignature (sig : signature) (argTypes : List type)
    (resultType : type) (cconv : calling_convention) : Bool :=
  sig == csmithFabsfSignature &&
    argTypes == csmithFabsfArgTypes &&
    resultType == csmithFabsfResultType &&
    cconv == cc_default

/-- One successful CSmith-aware transition, including executor-only runtime
state and the exact CompCert trace emitted by the transition. -/
structure CSmithTransition where
  runtime : Runtime
  trace : Events.trace
  state : state

/--
Attempt one transition with the restricted CSmith external surface enabled.

All states outside the exact checksum, `fabs`, and `fabsf` calls are delegated
unchanged to `stepInternal`: their runtime is preserved and their trace is
`Events.E0`. Consequently builtins and all other external calls retain the
existing `unsupportedExternal` outcome. The checksum helper's stdout effect
remains in `Runtime.stdout`, not in `Events.trace`.
-/
def stepCSmith (ge : genv) (runtime : Runtime) : state → Except ExecError CSmithTransition
  | .Callstate (.External (.EF_external name sig) argTypes resultType cconv) args k memory =>
      if name == "csmith_checksum_print" &&
          isCSmithChecksumPrintSignature sig argTypes resultType cconv then
        match csmithChecksumPrint runtime memory args with
        | .error error => .error error
        | .ok action =>
            .ok
              { runtime := action.runtime
                trace := Events.E0
                state := .Returnstate action.result k action.memory }
      else if name == "fabs" && isCSmithFabsSignature sig argTypes resultType cconv then
        match csmithFabs runtime memory args with
        | .error error => .error error
        | .ok action =>
            .ok
              { runtime := action.runtime
                trace := Events.E0
                state := .Returnstate action.result k action.memory }
      else if name == "fabsf" && isCSmithFabsfSignature sig argTypes resultType cconv then
        match csmithFabsf runtime memory args with
        | .error error => .error error
        | .ok action =>
            .ok
              { runtime := action.runtime
                trace := Events.E0
                state := .Returnstate action.result k action.memory }
      else
        .error (.unsupportedExternal "external-call")
  | currentState =>
      match stepInternal ge currentState with
      | .error error => .error error
      | .ok nextState =>
          .ok { runtime := runtime, trace := Events.E0, state := nextState }

end CLightLean.Exec
