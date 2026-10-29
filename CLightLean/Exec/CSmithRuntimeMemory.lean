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

import CLightLean.Exec.CSmithRuntime
import CLightLean.Memory

/-!
Clight-memory adapter for the lightweight CSmith checksum runtime.

This module is intentionally not re-exported by `CLightLean.Exec`: importing
it brings the full `Values`/`Memory` semantic dependency closure into Lean.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Read a bounded C string from modeled memory through the lightweight core. -/
def readCStringBounded (m : Memory.mem) (pointer : val) (maxScan : Nat) :
    Except ExecError ByteArray :=
  match pointer with
  | .Vptr block offset =>
      readCStringBoundedWith (fun b ofs => Memory.load_byte m b ofs)
        { block := block, offset := Ptrofs.unsigned offset } maxScan
  | _ => .error .invalidCString

/-- Result of the concrete CSmith checksum-print action. -/
structure ChecksumPrintfResult where
  runtime : Runtime
  memory : Memory.mem
  result : val

/-- Result of a CSmith-admitted, memory-preserving floating absolute-value
external.  The CSmith safe floating wrappers use these calls solely to decide
whether an operation would overflow. -/
structure FloatAbsResult where
  runtime : Runtime
  memory : Memory.mem
  result : val

/--
Perform the restricted CSmith checksum print action through `Memory.mem`.

The admitted shape is `[Vptr format, Vint checksum]`. Wrong arity is
`malformedCall`; correctly arity-shaped non-pointer or non-`Vint` arguments are
`invalidExpression`. Successful actions preserve memory and return the C
`printf` byte count as `Vint`.
-/
def checksumPrintf (maxFormatScan : Nat) (runtime : Runtime) (memory : Memory.mem)
    (args : List val) : Except ExecError ChecksumPrintfResult :=
  match args with
  | [format, .Vint checksum] =>
      match format with
      | .Vptr block offset =>
          match checksumPrintfWith (fun b ofs => Memory.load_byte memory b ofs) maxFormatScan runtime
              { block := block, offset := Ptrofs.unsigned offset } checksum.unsigned with
          | .error error => .error error
          | .ok action =>
              .ok
                { runtime := action.runtime
                  memory := memory
                  result := .Vint (CompCert.Int.repr (action.resultByteCount : Int)) }
      | _ => .error .invalidExpression
  | [_format, _checksum] => .error .invalidExpression
  | _ => .error .malformedCall

/--
Perform the bootstrap fixed-signature CSmith checksum action.

Unlike `checksumPrintf`, this action has no format-pointer argument and does
not read modeled memory. Its one and only admitted argument shape is
`[Vint checksum]`, corresponding to the owned companion C runtime function
`csmith_checksum_print(unsigned int)`. It appends the canonical checksum bytes,
preserves memory, and returns the C byte count as an `int` value.
-/
def csmithChecksumPrint (runtime : Runtime) (memory : Memory.mem) (args : List val) :
    Except ExecError ChecksumPrintfResult :=
  match args with
  | [.Vint checksum] =>
      let output := csmithChecksumOutput checksum.unsigned
      .ok
        { runtime := Runtime.appendStdout runtime output
          memory := memory
          result := .Vint (CompCert.Int.repr (output.size : Int)) }
  | [_] => .error .invalidExpression
  | _ => .error .malformedCall

/-- Model the exact unary `double fabs(double)` call emitted by CSmith's
safe floating wrappers.  It is a pure, silent call: only its floating result
changes, so executor runtime and modeled memory are preserved. -/
def csmithFabs (runtime : Runtime) (memory : Memory.mem) (args : List val) :
    Except ExecError FloatAbsResult :=
  match args with
  | [.Vfloat value] =>
      .ok
        { runtime := runtime
          memory := memory
          result := .Vfloat (CompCert.Float64.abs value) }
  | [_] => .error .invalidExpression
  | _ => .error .malformedCall

/-- Model the exact unary `float fabsf(float)` call emitted by CSmith's safe
floating wrappers.  It is a pure, silent call: only its floating result
changes, so executor runtime and modeled memory are preserved. -/
def csmithFabsf (runtime : Runtime) (memory : Memory.mem) (args : List val) :
    Except ExecError FloatAbsResult :=
  match args with
  | [.Vsingle value] =>
      .ok
        { runtime := runtime
          memory := memory
          result := .Vsingle (CompCert.Float32.abs value) }
  | [_] => .error .invalidExpression
  | _ => .error .malformedCall

end CLightLean.Exec
