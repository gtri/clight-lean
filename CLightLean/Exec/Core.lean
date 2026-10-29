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

/-!
Lightweight executor runtime data shared by the semantic executor and narrow
runtime helpers. This module deliberately has no dependency on Clight values,
memory, or operational semantics.
-/

namespace CLightLean.Exec

/-- Executor-only state. C program stdout is retained as uninterpreted bytes. -/
structure Runtime where
  stdout : ByteArray := .empty

namespace Runtime

/-- A fresh runtime has no modeled program output. -/
def empty : Runtime := {}

/-- Append raw program-output bytes without decoding or normalizing them. -/
def appendStdout (runtime : Runtime) (output : ByteArray) : Runtime :=
  { runtime with stdout := runtime.stdout ++ output }

end Runtime

/-- Failures reported by the functional executor rather than by proof search. -/
inductive ExecError where
  | invalidExpression
  | invalidLvalue
  | invalidAssignment
  | memoryFailure
  | malformedCall
  | unsupportedExternal (name : String)
  | unsupportedPrintfFormat (format : String)
  | invalidCString
  | stuck
deriving DecidableEq, Repr

namespace ExecError

/-- Whether the error denotes an intentionally unsupported executor feature. -/
def isUnsupported : ExecError → Bool
  | .unsupportedExternal _ | .unsupportedPrintfFormat _ => true
  | _ => false

/-- Stable, machine-oriented error code for a later runner envelope. -/
def code : ExecError → String
  | .invalidExpression => "invalid_expression"
  | .invalidLvalue => "invalid_lvalue"
  | .invalidAssignment => "invalid_assignment"
  | .memoryFailure => "memory_failure"
  | .malformedCall => "malformed_call"
  | .unsupportedExternal _ => "unsupported_external"
  | .unsupportedPrintfFormat _ => "unsupported_printf_format"
  | .invalidCString => "invalid_cstring"
  | .stuck => "stuck"

/-- Optional diagnostic detail. An envelope encoder must escape it itself. -/
def detail : ExecError → Option String
  | .unsupportedExternal name => some name
  | .unsupportedPrintfFormat format => some format
  | _ => none

end ExecError

end CLightLean.Exec
