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

/-!
Unbounded host-IO execution for the fixed-signature CSmith checksum path.

The loop below calls the same pure `stepCSmith` kernel used by
`runCSmithFromFuel`; it neither invokes the relational semantics nor performs
proof search. It intentionally has no semantic fuel. A nonterminating C
program must instead be stopped by the host process supervisor.

## Result-envelope protocol

`renderCSmithResultEnvelope` emits one ASCII-only line in this fixed key-value
grammar (fields occur once and in this order):

```text
CLIGHT_LEAN_RUNNER_V1 status=<token> steps=<decimal> exit=<signed-decimal-or-> error_code=<token-or-> stdout_hex=<uppercase-hex>
```

For example, a successful program that wrote `checksum = 1A2B\n` begins:

```text
CLIGHT_LEAN_RUNNER_V1 status=completed steps=... exit=0 error_code=- stdout_hex=636865636B73756D203D20314132420A
```

`stdout_hex` is an exact byte encoding, not decoded C stdout. The process
prints only this host protocol line, so modeled program bytes can never
contaminate it. An initialization failure uses the same grammar with
`status=initialization_error`, `steps=0`, `exit=-`, and empty stdout.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Tail-recursive unbounded worker. `steps` counts successful CSmith
transitions already taken and `trace` is their left-to-right append. -/
private partial def runCSmithIOLoop (ge : genv) (runtime : Runtime)
    (trace : Events.trace) (currentState : state) (steps : Nat) : IO RunResult :=
  match finalReturn? currentState with
  | some result =>
      pure (.completed runtime trace result steps)
  | none =>
      match stepCSmith ge runtime currentState with
      | .ok transition =>
          runCSmithIOLoop ge transition.runtime (trace ++ transition.trace)
            transition.state (steps + 1)
      | .error error =>
          match error with
          | .unsupportedExternal _ => pure (.unsupported runtime trace error steps)
          | _ => pure (.stuck runtime trace error steps)

/--
Run the CSmith-aware executor without semantic fuel from an existing runtime
and state. Final states are checked before calling `stepCSmith`; each successful
transition updates the runtime, appends its trace, and increments `steps`.

This is intentionally a `partial def`: an infinite program remains in the tail
loop until its host process timeout terminates it. It does not change Lean's
heartbeat limit or use a heartbeat setting as a timeout mechanism.
-/
partial def runCSmithUntilTerminationFromState (ge : genv) (runtime : Runtime)
    (initialState : state) : IO RunResult :=
  runCSmithIOLoop ge runtime Events.E0 initialState 0

/--
Construct the ordinary whole-program initial state, then execute it through the
unbounded fixed-signature CSmith runner. Initialization errors are returned
separately, exactly as for `runCSmithProgramFuel`.
-/
def runCSmithProgramUntilTermination (p : program_type function) :
    IO (Except ExecError RunResult) := do
  match initialState p with
  | .error error => pure (.error error)
  | .ok initialState =>
      let result ← runCSmithUntilTerminationFromState (globalenv p) Runtime.empty initialState
      pure (.ok result)

/-- Convert one four-bit value to an uppercase ASCII hexadecimal character. -/
private def envelopeHexDigit (digit : Nat) : Char :=
  Char.ofNat (if digit < 10 then 48 + digit else 55 + digit)

/-- Encode raw modeled stdout as two uppercase hexadecimal characters per byte. -/
def stdoutHex (stdout : ByteArray) : String :=
  String.ofList <| stdout.toList.flatMap fun byte =>
    [envelopeHexDigit (byte.toNat / 16), envelopeHexDigit (byte.toNat % 16)]

/-- Render the common fixed-order ASCII-only result-envelope fields. -/
private def renderCSmithEnvelopeFields (status : String) (steps : Nat)
    (exit : Option CompCert.Int) (error : Option ExecError) (stdout : ByteArray) : String :=
  let exitField := match exit with
    | some value => toString value.signed
    | none => "-"
  let errorField := match error with
    | some value => value.code
    | none => "-"
  "CLIGHT_LEAN_RUNNER_V1 status=" ++ status ++
    " steps=" ++ toString steps ++
    " exit=" ++ exitField ++
    " error_code=" ++ errorField ++
    " stdout_hex=" ++ stdoutHex stdout

/-- Render a terminal CSmith execution result in the stable host protocol. -/
def renderCSmithResultEnvelope (result : RunResult) : String :=
  renderCSmithEnvelopeFields result.statusCode result.steps result.exit? result.error?
    result.runtime.stdout

/-- Render an initialization failure in the same stable host protocol. -/
def renderCSmithInitializationErrorEnvelope (error : ExecError) : String :=
  renderCSmithEnvelopeFields "initialization_error" 0 none (some error) ByteArray.empty

/-- Render either a whole-program initialization failure or its terminal
execution result. -/
def renderCSmithProgramEnvelope (result : Except ExecError RunResult) : String :=
  match result with
  | .ok runResult => renderCSmithResultEnvelope runResult
  | .error error => renderCSmithInitializationErrorEnvelope error

end CLightLean.Exec
