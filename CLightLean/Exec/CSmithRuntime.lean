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

import CLightLean.Exec.Core

/-!
Lightweight, deliberately restricted CSmith checksum-output primitives.

This module is independent of Clight values and memory. The concrete memory
adapter lives in `CLightLean.Exec.CSmithRuntimeMemory`, so raw-byte unit tests
do not pull the CLight semantic closure into their Lean process.
-/

namespace CLightLean.Exec

/-- Build a byte array from literal byte values without using text decoding. -/
private def byteArrayOf (values : List UInt8) : ByteArray :=
  values.foldl ByteArray.push ByteArray.empty

/-- The exact NUL-free CSmith format accepted by this restricted runtime. -/
def csmithChecksumFormat : ByteArray :=
  byteArrayOf [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x25, 0x58, 0x0a]

/-- Bytes emitted before the uppercase checksum digits. -/
def csmithChecksumOutputPrefix : ByteArray :=
  byteArrayOf [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20]

/-- Bytes emitted after the uppercase checksum digits. -/
def csmithChecksumOutputSuffix : ByteArray := byteArrayOf [0x0a]

/-- Maximum C-memory cells scanned for the checksum format, including its NUL. -/
def csmithChecksumFormatMaxScan : Nat := 64

/-- A fixed safe diagnostic for a readable but noncanonical checksum format. -/
def csmithUnsupportedFormatDiagnostic : String := "noncanonical_csmith_checksum_format"

/-- A read-only byte source indexed by a block number and within-block offset. -/
abbrev CByteLookup := Nat → Int → Option UInt8

/-- A lightweight C pointer used only by the raw-byte checksum runtime. -/
structure CPointer where
  block : Nat
  offset : Int
deriving DecidableEq, Repr

/-- Read at most `remaining` C-memory cells, stopping before a NUL byte. -/
private def readCStringLoopWith (lookup : CByteLookup) (pointer : CPointer) :
    Nat → ByteArray → Except ExecError ByteArray
  | 0, _ => .error .invalidCString
  | remaining + 1, output =>
      match lookup pointer.block pointer.offset with
      | none => .error .invalidCString
      | some byte =>
          if byte = 0 then
            .ok output
          else
            readCStringLoopWith lookup { pointer with offset := pointer.offset + 1 }
              remaining (output.push byte)

/--
Read a NUL-terminated C byte string under a strict scan bound. The bound counts
every examined cell, including a possible NUL. A missing cell or a missing NUL
before the bound is `ExecError.invalidCString`.
-/
def readCStringBoundedWith (lookup : CByteLookup) (pointer : CPointer) (maxScan : Nat) :
    Except ExecError ByteArray :=
  readCStringLoopWith lookup pointer maxScan ByteArray.empty

/-- Convert one hexadecimal nibble to its canonical uppercase ASCII byte. -/
def uppercaseHexDigit (digit : Nat) : UInt8 :=
  if digit < 10 then
    UInt8.ofNat (48 + digit)
  else
    UInt8.ofNat (55 + digit)

/-- The modulus used by C's unsigned 32-bit `%X` checksum representation. -/
def uint32Modulus : Nat := 2 ^ 32

/-- Emit the non-leading-zero portion of the eight nibbles of a uint32 value. -/
private def appendUInt32HexDigits (value : Nat) : Nat → Bool → ByteArray → ByteArray
  | 0, started, output =>
      if started then output else output.push (UInt8.ofNat 48)
  | remaining + 1, started, output =>
      let divisor := 16 ^ remaining
      let digit := (value / divisor) % 16
      if started then
        appendUInt32HexDigits value remaining true (output.push (uppercaseHexDigit digit))
      else if digit = 0 then
        appendUInt32HexDigits value remaining false output
      else
        appendUInt32HexDigits value remaining true (output.push (uppercaseHexDigit digit))

/--
Format a natural number modulo `2^32` exactly as C `%X`: uppercase hexadecimal,
no leading zeroes, and the single byte `"0"` for zero.
-/
def formatUInt32HexUpper (checksum : Nat) : ByteArray :=
  appendUInt32HexDigits (checksum % uint32Modulus) 8 false ByteArray.empty

/-- The exact stdout bytes emitted by the supported CSmith checksum call. -/
def csmithChecksumOutput (checksum : Nat) : ByteArray :=
  csmithChecksumOutputPrefix ++ formatUInt32HexUpper checksum ++ csmithChecksumOutputSuffix

/-- Result of the lightweight restricted checksum-print action. -/
structure ChecksumPrintfActionResult where
  runtime : Runtime
  resultByteCount : Nat

/--
Perform the one supported CSmith checksum print action against a read-only byte
lookup. It accepts a format pointer and unsigned checksum only; argument-list
validation and Clight value conversion belong to the explicit heavy adapter.
-/
def checksumPrintfWith (lookup : CByteLookup) (maxFormatScan : Nat) (runtime : Runtime)
    (formatPointer : CPointer) (checksum : Nat) : Except ExecError ChecksumPrintfActionResult :=
  match readCStringBoundedWith lookup formatPointer maxFormatScan with
  | .error error => .error error
  | .ok formatBytes =>
      if formatBytes = csmithChecksumFormat then
        let output := csmithChecksumOutput checksum
        .ok
          { runtime := Runtime.appendStdout runtime output
            resultByteCount := output.size }
      else
        .error (.unsupportedPrintfFormat csmithUnsupportedFormatDiagnostic)

end CLightLean.Exec
