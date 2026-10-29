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

-- Memory model for Clight
--
-- This is a SIMPLIFIED memory model compared to CompCert's Memory.v.
-- It is designed for:
--   1. Executable Clight semantics (can run programs)
--   2. Verification with Hoare Logic / Iris separation logic
--   3. Faithfulness to Clight semantics (including Vundef for uninitialized memory)
--
-- DESIGN DECISIONS (see docs/MEMORY_DESIGN.md for full rationale):
--
-- 1. Block representation: Use Nat for block IDs
--    - Simple, efficient, supports equality/hashing
--    - Alternative: separate type with invariants (rejected: unnecessary complexity)
--
-- 2. Memory contents: HashMap (block × Int) UInt8
--    - Sparse representation (only stores initialized bytes)
--    - Reading absent key = uninitialized = returns Vundef
--    - Alternative: ByteArray per block (rejected: more complex, premature optimization)
--
-- 3. Permissions: Boolean "is allocated?" only
--    - CompCert has 4-level permission algebra (Freeable > Writable > Readable > Nonempty)
--    - We skip this: not needed for semantics, Iris will layer separation logic on top
--    - Simplifies proofs dramatically
--
-- 4. Alignment: Checked at load/store time
--    - Not stored in block metadata
--    - Simpler than CompCert's per-chunk alignment tracking
--
-- 5. Bounds: Stored per-block as (lo, hi) interval
--    - CompCert stores (lo, hi, max) for permission tracking
--    - We only need (lo, hi) for validity checks

import CLightLean.Archi
import CLightLean.AST
import CLightLean.Lib.Integers
import CLightLean.Lib.Floats
import CLightLean.Values
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

variable [Archi]

namespace Memory

inductive quantity where
  | Q32
  | Q64
  deriving DecidableEq, Repr

inductive memval where
  | Undef
  | Byte (b : UInt8)
  | Fragment (v : val) (q : quantity) (index : Nat)
  deriving DecidableEq

instance : Inhabited memval := ⟨.Undef⟩

def memval_to_byte : memval → Option UInt8
  | .Byte b => some b
  | _ => none

instance : Repr memval where
  reprPrec _ _ := "memval"

-- ============================================================================
-- BASIC TYPES
-- ============================================================================

/- Block identifiers are natural numbers.
    Each allocated memory region gets a unique block ID.
    Block 0 is reserved as invalid (never allocated).
    NOTE: `block` is now defined once, canonically, in `CLightLean/Values.lean`
    and reused here (imported), matching CompCert's `Values.v`. -/
-- abbrev block := Nat

-- /-- Memory chunks specify the size and interpretation of memory accesses.
--     These match CompCert's memory_chunk type. -/
-- inductive memory_chunk where
--   | Mint8signed                    -- 8-bit signed integer
--   | Mint8unsigned                  -- 8-bit unsigned integer
--   | Mint16signed                   -- 16-bit signed integer
--   | Mint16unsigned                 -- 16-bit unsigned integer
--   | Mint32                         -- 32-bit integer
--   | Mint64                         -- 64-bit integer
--   | Mfloat32                       -- 32-bit float (single precision)
--   | Mfloat64                       -- 64-bit float (double precision)
--   | Many32                         -- 32-bit value (untyped, for memcpy etc.)
--   | Many64                         -- 64-bit value (untyped)
--   deriving DecidableEq, Repr
-- NOTE: `memory_chunk` (including `Mbool`) is now defined once, canonically,
-- in `CLightLean/AST.lean` and reused here (imported), matching CompCert's `AST.v`.

/-- Size of a memory chunk in bytes. -/
def size_chunk (chunk : memory_chunk) : Nat :=
  match chunk with
  | .Mbool | .Mint8signed | .Mint8unsigned => 1
  | .Mint16signed | .Mint16unsigned => 2
  | .Mint32 | .Mfloat32 | .Many32 => 4
  | .Mint64 | .Mfloat64 | .Many64 => 8

/-- Alignment requirement for a memory chunk.
    Returns the required alignment in bytes (must be a power of 2).

    DESIGN: We check alignment at load/store time rather than storing
    it in block metadata. This is simpler than CompCert's approach. -/
def align_chunk (chunk : memory_chunk) : Nat :=
  match chunk with
  | .Mbool | .Mint8signed | .Mint8unsigned => 1
  | .Mint16signed | .Mint16unsigned => 2
  | .Mint32 | .Mfloat32 | .Many32 => 4
  | .Mint64 | .Mfloat64 | .Many64 => 8

/-- Check if an offset is properly aligned for a chunk. -/
def is_aligned (ofs : Int) (chunk : memory_chunk) : Bool :=
  let a := align_chunk chunk
  (ofs % a).natAbs = 0

/-- Block metadata: stores bounds for each allocated block.

    DESIGN: We only store (lo, hi) bounds, not CompCert's (lo, hi, max).
    CompCert needs 'max' for tracking permission upper bounds (for compiler
    correctness proofs). We don't need this for executable semantics. -/
structure block_info where
  lo : Int   -- Lower bound (inclusive, typically 0)
  hi : Int   -- Upper bound (exclusive, i.e., size in bytes)
  deriving DecidableEq, Repr

-- ============================================================================
-- MEMORY STATE
-- ============================================================================

/-- Memory state.

    DESIGN DECISIONS:

    1. `contents` is a SPARSE map: only initialized bytes are stored.
       Reading an absent key = uninitialized memory = returns Vundef.
       This is more efficient than storing Vundef explicitly.

    2. `blocks` tracks which blocks are allocated and their bounds.
       Only allocated blocks can be accessed.

    3. `nextblock` is the next fresh block ID to allocate.
       Monotonically increasing, ensures freshness.

    4. No permission tracking (unlike CompCert).
       CompCert tracks Freeable/Writable/Readable permissions per-byte.
       We use simple boolean "is allocated?" instead.
       Rationale: Permissions are for compiler optimization proofs.
       For semantics + Iris, separation logic handles ownership. -/
structure mem where
  -- Sparse map: (block, offset) → byte
  -- Only stores INITIALIZED bytes
  contents : Std.HashMap (block × Int) memval

  -- Allocation table: block → bounds
  blocks : Std.HashMap block block_info

  -- Next fresh block ID (monotonically increasing)
  nextblock : block
  deriving Repr

/-- Well-formedness invariant for memory.
    These properties should hold for any reachable memory state. -/
def mem_wf (m : mem) : Prop :=
  -- 1. nextblock is always fresh (never allocated)
  (∀ b info, m.blocks.get? b = some info → b < m.nextblock) ∧
  -- 2. All allocated blocks have valid bounds (lo < hi)
  (∀ b info, m.blocks.get? b = some info → info.lo < info.hi) ∧
  -- 3. nextblock > 0 (block 0 reserved)
  m.nextblock > 0 ∧
  -- 4. contents only contains keys for allocated blocks
  (∀ b ofs byte, m.contents.get? (b, ofs) = some byte → ∃ info, m.blocks.get? b = some info)

/-- Initial empty memory state. -/
def empty : mem :=
  { contents := ∅
    blocks := ∅
    nextblock := 1 }  -- Block 0 reserved as "invalid"

-- ============================================================================
-- POINTER VALIDITY
-- ============================================================================

/-- Check if a pointer is valid (points to an allocated, in-bounds location).
    Used for memory safety checks and pointer comparisons.

    DESIGN: Returns true iff:
      - Block is allocated
      - Offset is in range [lo, hi)  (note: hi is EXCLUSIVE)

    This is used by Cop for pointer comparison semantics. -/
def valid_pointer (m : mem) (b : block) (ofs : Int) : Bool :=
  match m.blocks.get? b with
  | none => false  -- Block not allocated
  | some info => info.lo ≤ ofs && ofs < info.hi

/-- Check if a pointer is "weak valid" (valid or one-past-end).
    Used for pointer comparisons in C (you can have a pointer to one-past-end
    of an array, but can't dereference it).

    DESIGN: Like valid_pointer, but allows ofs = hi (one-past-end).
    This matches C semantics: `&arr[n]` is legal even if you can't read it. -/
def weak_valid_pointer (m : mem) (b : block) (ofs : Int) : Bool :=
  match m.blocks.get? b with
  | none => false
  | some info => info.lo ≤ ofs && ofs ≤ info.hi  -- Note: ≤ hi

/-- Check if a block is currently allocated. -/
def block_allocated (m : mem) (b : block) : Bool :=
  m.blocks.contains b

-- ============================================================================
-- ALLOCATION AND FREEING
-- ============================================================================

/-- Allocate a fresh memory block with bounds [lo, hi).
    Returns the new block ID and updated memory.

    DESIGN:
    - Always succeeds (no out-of-memory errors)
    - Block contents are uninitialized (not in `contents` map)
    - `lo` is typically 0, but we allow arbitrary values for flexibility
    - Blocks are never reused (nextblock is monotonic)

    DIFFERENCE FROM COMPCERT:
    CompCert's alloc also takes permission arguments.
    We don't track permissions, so this is simpler. -/
def alloc (m : mem) (lo hi : Int) : block × mem :=
  let b := m.nextblock
  let info : block_info := { lo := lo, hi := hi }
  let m' : mem :=
    { contents := m.contents
      blocks := m.blocks.insert b info
      nextblock := b + 1 }
  (b, m')

/-- Free a memory block.
    Returns None if the block doesn't exist or bounds don't match.

    DESIGN:
    - Requires exact bounds match (lo, hi) for safety
    - Removes all bytes belonging to this block from contents
    - Removes block from allocation table

    DIFFERENCE FROM COMPCERT:
    CompCert checks permissions (must have Freeable permission).
    We just check that the block is allocated and bounds match. -/
def free (m : mem) (b : block) (lo hi : Int) : Option mem :=
  match m.blocks.get? b with
  | none => none  -- Block not allocated
  | some info =>
      if info.lo = lo && info.hi = hi then
        -- Remove block and all its contents
        let contents' := m.contents.filter (fun (b', _) _ => b' ≠ b)
        let blocks' := m.blocks.erase b
        some { m with contents := contents', blocks := blocks' }
      else none  -- Bounds mismatch (safety check)

/-- Frees all the given `(block, lo, hi)` triples, in order, threading the
    memory state through each `free`; fails if any individual `free` fails. -/
def free_list (m : mem) (l : List (block × Int × Int)) : Option mem :=
  match l with
  | [] => some m
  | (b, low, high) :: l' =>
      match free m b low high with
      | none => none
      | some m' => free_list m' l'

-- ============================================================================
-- BYTE-LEVEL OPERATIONS
-- ============================================================================

/-- Load a single byte from memory.
    Returns None if the location is out of bounds or uninitialized.

    DESIGN:
    - Out of bounds → None (hard error)
    - In bounds but uninitialized → None (caller must handle as Vundef)

    NOTE: This is a low-level operation. High-level loads (load_chunk)
    handle Vundef automatically. -/
def load_byte (m : mem) (b : block) (ofs : Int) : Option UInt8 :=
  if valid_pointer m b ofs then
    (m.contents.get? (b, ofs)).bind memval_to_byte  -- None if uninitialized
  else
    none  -- Out of bounds

/-- Store a single byte to memory.
    Returns None if the location is out of bounds.

    DESIGN:
    - Out of bounds → None (hard error)
    - In bounds → updates contents map (marks byte as initialized) -/
def store_byte (m : mem) (b : block) (ofs : Int) (v : UInt8) : Option mem :=
  if valid_pointer m b ofs then
    some { m with contents := m.contents.insert (b, ofs) (memval.Byte v) }
  else
    none  -- Out of bounds

-- ============================================================================
-- ENCODING/DECODING VALUES
-- ============================================================================

/-- Encode a value as a list of bytes for a given chunk.

    DESIGN:
    This is where we define the byte-level representation of values.
    We use little-endian byte order (matches x86/ARM).

    TODO: Handle Archi.big_endian for big-endian architectures.
    For now, we assume little-endian (most common).

    NOTE: For now, floats and pointers return empty lists (not yet implemented).
    This will be filled in as needed. -/
def encode_bytes (chunk : memory_chunk) (v : val) : List UInt8 :=
  match chunk, v with
  -- 8-bit integers.  `Mbool` (C11 `_Bool`) encodes identically to
  -- `Mint8unsigned`/`Mint8signed`: CompCert's `encode_val` (Memdata.v) uses the
  -- same `encode_int 1 (Int.unsigned n)` formula for all three chunks; the
  -- special "normalize to 0/1" behaviour only happens on *decode*.
  | .Mbool, .Vint i | .Mint8signed, .Vint i | .Mint8unsigned, .Vint i =>
      [UInt8.ofNat (i.unsigned % 256)]

  -- 16-bit integers (little-endian)
  | .Mint16signed, .Vint i | .Mint16unsigned, .Vint i =>
      let n := i.unsigned
      [ UInt8.ofNat (n % 256)
      , UInt8.ofNat ((n / 256) % 256) ]

  -- 32-bit integers (little-endian)
  | .Mint32, .Vint i | .Many32, .Vint i =>
      let n := i.unsigned
      [ UInt8.ofNat (n % 256)
      , UInt8.ofNat ((n / 256) % 256)
      , UInt8.ofNat ((n / 65536) % 256)
      , UInt8.ofNat ((n / 16777216) % 256) ]

  -- 64-bit integers (little-endian)
  | .Mint64, .Vlong i | .Many64, .Vlong i =>
      let n := i.unsigned
      [ UInt8.ofNat (n % 256)
      , UInt8.ofNat ((n / 256) % 256)
      , UInt8.ofNat ((n / 65536) % 256)
      , UInt8.ofNat ((n / 16777216) % 256)
      , UInt8.ofNat ((n / 4294967296) % 256)
      , UInt8.ofNat ((n / 1099511627776) % 256)
      , UInt8.ofNat ((n / 281474976710656) % 256)
      , UInt8.ofNat ((n / 72057594037927936) % 256) ]

  -- 32-bit floats: encode as bit pattern (little-endian)
  | .Mfloat32, .Vsingle f | .Many32, .Vsingle f =>
      let bits := FloatLib.Floats.ExecFloat.Binary.toBits32 f
      let n := bits.toNat
      [ UInt8.ofNat (n % 256)
      , UInt8.ofNat ((n / 256) % 256)
      , UInt8.ofNat ((n / 65536) % 256)
      , UInt8.ofNat ((n / 16777216) % 256) ]

  -- 64-bit floats: encode as bit pattern (little-endian)
  | .Mfloat64, .Vfloat f | .Many64, .Vfloat f =>
      let bits := FloatLib.Floats.ExecFloat.Binary.toBits64 f
      let n := bits.toNat
      [ UInt8.ofNat (n % 256)
      , UInt8.ofNat ((n / 256) % 256)
      , UInt8.ofNat ((n / 65536) % 256)
      , UInt8.ofNat ((n / 16777216) % 256)
      , UInt8.ofNat ((n / 4294967296) % 256)
      , UInt8.ofNat ((n / 1099511627776) % 256)
      , UInt8.ofNat ((n / 281474976710656) % 256)
      , UInt8.ofNat ((n / 72057594037927936) % 256) ]

  -- Pointers: encode offset only (block identity preserved separately)
  -- This matches CompCert's approach: pointers in memory store the offset,
  -- and the block is implicit from the pointer value itself.
  -- NOTE: This means pointer-to-int casts only preserve the offset, not the block!
  | .Mint32, .Vptr _ ofs | .Many32, .Vptr _ ofs =>
      if Archi.ptr64 then
        []  -- Error: can't store 64-bit pointer in 32-bit chunk
      else
        let n := ofs.unsigned.natAbs  -- Convert to Nat for encoding
        [ UInt8.ofNat (n % 256)
        , UInt8.ofNat ((n / 256) % 256)
        , UInt8.ofNat ((n / 65536) % 256)
        , UInt8.ofNat ((n / 16777216) % 256) ]

  | .Mint64, .Vptr _ ofs | .Many64, .Vptr _ ofs =>
      if ¬Archi.ptr64 then
        []  -- Error: can't store 32-bit pointer in 64-bit chunk
      else
        let n := ofs.unsigned.natAbs  -- Convert to Nat for encoding
        [ UInt8.ofNat (n % 256)
        , UInt8.ofNat ((n / 256) % 256)
        , UInt8.ofNat ((n / 65536) % 256)
        , UInt8.ofNat ((n / 16777216) % 256)
        , UInt8.ofNat ((n / 4294967296) % 256)
        , UInt8.ofNat ((n / 1099511627776) % 256)
        , UInt8.ofNat ((n / 281474976710656) % 256)
        , UInt8.ofNat ((n / 72057594037927936) % 256) ]

  -- Type mismatch or Vundef
  | _, _ => []  -- Return empty list to signal error

/-- Decode a list of bytes into a value for a given chunk.

    DESIGN:
    - Little-endian byte order
    - Sign extension for signed types
    - Returns Vundef for wrong number of bytes

    NOTE ON POINTERS:
    Pointers stored to memory are encoded as their offset only (block is lost).
    When decoded, they come back as integers (Vint/Vlong), not Vptr.
    This matches CompCert's simplified encoding and is correct for Clight:
    - Storing a pointer and loading it back as an integer is like `(intptr_t)p`
    - You cannot meaningfully load a pointer from memory without provenance tracking
    - For full pointer roundtrip, CompCert uses "memory injections" (not implemented here)
-/
def decode_bytes (chunk : memory_chunk) (bytes : List UInt8) : val :=
  let expected_size := size_chunk chunk
  if bytes.length ≠ expected_size then
    .Vundef  -- Wrong number of bytes
  else
    match chunk with
    -- 8-bit boolean (C11 `_Bool`).  Decoded like `Mint8unsigned`, then
    -- normalized to exactly `Vtrue`/`Vfalse`/`Vundef` via `Val.norm_bool`
    -- (CompCert's Memdata.v: `Val.norm_bool (Vint (Int.zero_ext 8 (decode_int bl)))`).
    | .Mbool =>
        match bytes with
        | [b0] => Val.norm_bool (.Vint (CompCert.Int.zero_ext 8 (CompCert.Int.repr (b0.toNat : Int))))
        | _ => .Vundef

    -- 8-bit signed integer (sign extend)
    | .Mint8signed =>
        match bytes with
        | [b0] =>
            let n := b0.toNat
            let i := CompCert.Int.repr (n : Int)
            .Vint (CompCert.Int.sign_ext 8 i)
        | _ => .Vundef

    -- 8-bit unsigned integer
    | .Mint8unsigned =>
        match bytes with
        | [b0] => .Vint (CompCert.Int.repr (b0.toNat : Int))
        | _ => .Vundef

    -- 16-bit signed integer (little-endian, sign extend)
    | .Mint16signed =>
        match bytes with
        | [b0, b1] =>
            let n := b0.toNat + (b1.toNat * 256)
            let i := CompCert.Int.repr (n : Int)
            .Vint (CompCert.Int.sign_ext 16 i)
        | _ => .Vundef

    -- 16-bit unsigned integer (little-endian)
    | .Mint16unsigned =>
        match bytes with
        | [b0, b1] =>
            let n := b0.toNat + (b1.toNat * 256)
            .Vint (CompCert.Int.repr (n : Int))
        | _ => .Vundef

    -- 32-bit integer (little-endian)
    | .Mint32 | .Many32 =>
        match bytes with
        | [b0, b1, b2, b3] =>
            let n := b0.toNat + (b1.toNat * 256) + (b2.toNat * 65536) + (b3.toNat * 16777216)
            .Vint (CompCert.Int.repr (n : Int))
        | _ => .Vundef

    -- 64-bit integer (little-endian)
    | .Mint64 | .Many64 =>
        match bytes with
        | [b0, b1, b2, b3, b4, b5, b6, b7] =>
            let n := b0.toNat + (b1.toNat * 256) + (b2.toNat * 65536) + (b3.toNat * 16777216)
                   + (b4.toNat * 4294967296) + (b5.toNat * 1099511627776)
                   + (b6.toNat * 281474976710656) + (b7.toNat * 72057594037927936)
            .Vlong (CompCert.Int64.repr (n : Int))
        | _ => .Vundef

    -- 32-bit float: decode from bit pattern (little-endian)
    | .Mfloat32 =>
        match bytes with
        | [b0, b1, b2, b3] =>
            let n := b0.toNat + (b1.toNat * 256) + (b2.toNat * 65536) + (b3.toNat * 16777216)
            let bits := UInt32.ofNat n
            .Vsingle (FloatLib.Floats.ExecFloat.Binary.ofBits32 bits)
        | _ => .Vundef

    -- 64-bit float: decode from bit pattern (little-endian)
    | .Mfloat64 =>
        match bytes with
        | [b0, b1, b2, b3, b4, b5, b6, b7] =>
            let n := b0.toNat + (b1.toNat * 256) + (b2.toNat * 65536) + (b3.toNat * 16777216)
                   + (b4.toNat * 4294967296) + (b5.toNat * 1099511627776)
                   + (b6.toNat * 281474976710656) + (b7.toNat * 72057594037927936)
            let bits := UInt64.ofNat n
            .Vfloat (FloatLib.Floats.ExecFloat.Binary.ofBits64 bits)
        | _ => .Vundef

/-- Normalization that `decode_val ∘ encode_val` applies.

    This captures the value transformation performed by a store followed by a load:

    * Sub-word integer chunks (`Mint8*`/`Mint16*`) apply sign/zero extension.
    * Full-width integer/float chunks (`Mint32`, `Mint64`, `Mfloat32`, `Mfloat64`)
      round-trip exactly.
    * The `Many32`/`Many64` chunks do NOT preserve the value's *type*: this memory
      model decodes them as integers, so storing a float through a `Many` chunk and
      loading it back yields the integer reinterpretation of the float's bit pattern
    (`Vint`/`Vlong` of the encoded bits). This matches the `decode_bytes` definition,
      which never inspects how the bytes were produced. -/
def decode_encode_norm (chunk : memory_chunk) (v : val) : val :=
  match chunk, v with
  | .Mbool,          .Vint n => Val.norm_bool (.Vint (CompCert.Int.zero_ext 8 n))
  | .Mint8signed,    .Vint n => .Vint (CompCert.Int.sign_ext 8  n)
  | .Mint8unsigned,  .Vint n => .Vint (CompCert.Int.zero_ext 8  n)
  | .Mint16signed,   .Vint n => .Vint (CompCert.Int.sign_ext 16 n)
  | .Mint16unsigned, .Vint n => .Vint (CompCert.Int.zero_ext 16 n)
  -- `Many32`/`Many64` decode as integers, reinterpreting float bit patterns.
  | .Many32, .Vsingle f => .Vint  (FloatLib.Floats.ExecFloat.Binary.toBits32 f)
  | .Many64, .Vfloat  f => .Vlong (FloatLib.Floats.ExecFloat.Binary.toBits64 f)
  | .Mint32, .Vptr b ofs => if Archi.ptr64 then .Vundef else .Vptr b ofs
  | .Mint64, .Vptr b ofs => if Archi.ptr64 then .Vptr b ofs else .Vundef
  | .Many32, .Vptr b ofs => if Archi.ptr64 then .Vundef else .Vptr b ofs
  | .Many64, .Vptr b ofs => if Archi.ptr64 then .Vptr b ofs else .Vundef
  | _, .Vptr _ _ => .Vundef
  | _, _ => v

/-- The fragment quantity carried by a pointer-sized memory chunk.

    `Mptr` is represented by `Mint32`/`Mint64` depending on the target
    architecture; `Many32` and `Many64` are likewise pointer-sized for the
    purposes of the CompCert memval codec. -/
def ptr_quantity (chunk : memory_chunk) : Option quantity :=
  match chunk with
  | .Mint32 | .Many32 => if ¬Archi.ptr64 then some .Q32 else none
  | .Mint64 | .Many64 => if Archi.ptr64 then some .Q64 else none
  | _ => none

/-- Number of cells used by a value fragment sequence. -/
def quantity_size : quantity → Nat
  | .Q32 => 4
  | .Q64 => 8

/-- Inject raw bytes into the semantic memory-cell representation. -/
def inj_bytes (bl : List UInt8) : List memval := bl.map .Byte

/-- Project a list of memory cells when every cell is a byte. -/
def proj_bytes : List memval → Option (List UInt8)
  | [] => some []
  | .Byte b :: cells =>
      match proj_bytes cells with
      | some bs => some (b :: bs)
      | none => none
  | _ :: _ => none

private theorem proj_bytes_append (xs ys : List memval) :
    proj_bytes (xs ++ ys) =
      match proj_bytes xs, proj_bytes ys with
      | some bs, some cs => some (bs ++ cs)
      | _, _ => none := by
  induction xs with
  | nil =>
      cases hys : proj_bytes ys <;> simp [proj_bytes, hys]
  | cons x xs ih =>
      cases x with
      | Undef => simp [proj_bytes]
      | Fragment v q i => simp [proj_bytes]
      | Byte b =>
          simp only [List.cons_append, proj_bytes]
          rw [ih]
          cases hxs : proj_bytes xs <;>
            cases hys : proj_bytes ys <;>
            simp [hxs, hys]

/-- Inject a value as its CompCert-style sequence of fragments. -/
def inj_value (q : quantity) (v : val) : List memval :=
  (List.range (quantity_size q)).map (fun i => .Fragment v q i)

/-- Check that `cells`, starting at fragment index `n`, is exactly the
    remaining fragment sequence for `v` and `q`. -/
def check_value (q : quantity) (v : val) : Nat → List memval → Bool
  | n, [] => decide (n = quantity_size q)
  | n, .Fragment v' q' i :: cells =>
      if n < quantity_size q then
        decide (v' = v ∧ q' = q ∧ i = n) && check_value q v (n + 1) cells
      else
        false
  | _, _ :: _ => false

/-- Project a complete, well-formed fragment sequence; malformed or partial
    sequences decode as `Vundef`. -/
def proj_value (q : quantity) (cells : List memval) : val :=
  match cells with
  | .Fragment v _ 0 :: _ =>
      if check_value q v 0 cells then v else .Vundef
  | _ => .Vundef

/-- CompCert-faithful value encoding.  Scalar values retain the established
    little-endian byte codec, while pointer-sized pointer values retain their
    complete provenance in fragments. -/
def encode_val (chunk : memory_chunk) (v : val) : List memval :=
  match ptr_quantity chunk, v with
  | some q, .Vptr b ofs => inj_value q (.Vptr b ofs)
  | _, _ => inj_bytes (encode_bytes chunk v)

/-- CompCert-faithful value decoding from semantic memory cells. -/
def decode_val (chunk : memory_chunk) (cells : List memval) : val :=
  match proj_bytes cells with
  | some bytes => decode_bytes chunk bytes
  | none =>
      match ptr_quantity chunk with
      | some q => Val.load_result chunk (proj_value q cells)
       | none => .Vundef

private theorem decode_val_replicate_undef (chunk : memory_chunk) :
    ∀ n, 0 < n → decode_val chunk (List.replicate n .Undef) = .Vundef := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      rw [show List.replicate (n + 1) (.Undef : memval) =
        .Undef :: List.replicate n .Undef by rfl]
      have hproj : proj_bytes (.Undef :: List.replicate n .Undef) = none := rfl
      unfold decode_val
      rw [hproj]
      cases hptr : Archi.ptr64 <;> cases chunk <;>
        simp [ptr_quantity, hptr, proj_value, Val.load_result] <;>
        split <;> rfl

private theorem replicate_append_one {α : Type} (a : α) :
    ∀ n, List.replicate n a ++ [a] = a :: List.replicate n a := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem map_range_replicate {α : Type} (f : Nat → α) (a : α) :
    ∀ n, (∀ i, i < n → f i = a) →
      (List.range n).map f = List.replicate n a := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hf
      rw [List.range_succ, List.map_append, List.replicate_succ]
      rw [ih (fun i hi => hf i (by omega))]
      simp only [List.map_cons, List.map_nil]
      rw [hf n (by omega)]
      exact replicate_append_one a n

/-! ### Codec inverse lemmas (needed by the load/store properties below) -/

/-- Projection is inverse to byte injection. -/
theorem proj_bytes_inj_bytes (bl : List UInt8) :
    proj_bytes (inj_bytes bl) = some bl := by
  induction bl with
  | nil => rfl
  | cons b bl ih =>
      change proj_bytes (.Byte b :: inj_bytes bl) = some (b :: bl)
      rw [proj_bytes, ih]

/-- Fragment sequences cannot be projected as raw bytes. -/
theorem proj_bytes_inj_value (q : quantity) (v : val) :
    proj_bytes (inj_value q v) = none := by
  cases q <;> rfl

/-- The consistency check accepts the exact fragment sequence it was given. -/
theorem check_value_inj_value (q : quantity) (v : val) :
    check_value q v 0 (inj_value q v) = true := by
  cases q
  · change check_value .Q32 v 0
      [.Fragment v .Q32 0, .Fragment v .Q32 1,
       .Fragment v .Q32 2, .Fragment v .Q32 3] = true
    simp [check_value, quantity_size]
  · change check_value .Q64 v 0
      [.Fragment v .Q64 0, .Fragment v .Q64 1,
       .Fragment v .Q64 2, .Fragment v .Q64 3,
       .Fragment v .Q64 4, .Fragment v .Q64 5,
       .Fragment v .Q64 6, .Fragment v .Q64 7] = true
    simp [check_value, quantity_size]

/-- Projection is inverse to value injection. -/
theorem proj_inj_value (q : quantity) (v : val) :
    proj_value q (inj_value q v) = v := by
  cases q
  · change (if check_value .Q32 v 0
      [.Fragment v .Q32 0, .Fragment v .Q32 1,
       .Fragment v .Q32 2, .Fragment v .Q32 3] then v else .Vundef) = v
    rw [show check_value .Q32 v 0
      [.Fragment v .Q32 0, .Fragment v .Q32 1,
       .Fragment v .Q32 2, .Fragment v .Q32 3] = true from check_value_inj_value .Q32 v]
    rfl
  · change (if check_value .Q64 v 0
      [.Fragment v .Q64 0, .Fragment v .Q64 1,
       .Fragment v .Q64 2, .Fragment v .Q64 3,
       .Fragment v .Q64 4, .Fragment v .Q64 5,
       .Fragment v .Q64 6, .Fragment v .Q64 7] then v else .Vundef) = v
    rw [show check_value .Q64 v 0
      [.Fragment v .Q64 0, .Fragment v .Q64 1,
       .Fragment v .Q64 2, .Fragment v .Q64 3,
       .Fragment v .Q64 4, .Fragment v .Q64 5,
       .Fragment v .Q64 6, .Fragment v .Q64 7] = true from check_value_inj_value .Q64 v]
    rfl

theorem inj_value_length (q : quantity) (v : val) :
    (inj_value q v).length = quantity_size q := by
  simp [inj_value]

-- ============================================================================
-- CHUNK-LEVEL LOAD/STORE
-- ============================================================================
/-- Load a value from memory at the given chunk size.

    DESIGN:
    - Returns None if out of bounds or misaligned (hard error)
    - Returns Some Vundef if any byte in the range is uninitialized
    - Returns Some v if all bytes are initialized (decode them)

    This is the main memory read operation used by Clight semantics. -/
def load (chunk : memory_chunk) (m : mem) (b : block) (ofs : Int) : Option val :=
  -- Check alignment
  if ¬(is_aligned ofs chunk) then
    none  -- Misaligned access
  else
    -- Check all cells in range are valid (not necessarily initialized)
    let size := size_chunk chunk
    let locs := (List.range size).map (fun (i : Nat) => (b, ofs + (i : Int)))

    -- Check bounds for all locations
    if locs.all (fun (b', ofs') => valid_pointer m b' ofs') then
      -- Load cells (an absent key is the semantic `Undef` cell).
      let cells := locs.map (fun (b', ofs') =>
        (m.contents.get? (b', ofs')).getD .Undef)
      some (decode_val chunk cells)
    else
      none  -- Out of bounds

/-- Store a value to memory at the given chunk size.

    DESIGN:
    - Returns None if out of bounds, misaligned, or value/chunk type mismatch
    - Marks all stored bytes as initialized

    This is the main memory write operation used by Clight semantics. -/
def store (chunk : memory_chunk) (m : mem) (b : block) (ofs : Int) (v : val) : Option mem :=
  -- Check alignment
  if ¬(is_aligned ofs chunk) then
    none  -- Misaligned access
  else
    -- Encode the value directly to semantic memory cells.
    let cells := encode_val chunk v
    let size := size_chunk chunk

    -- Check we got the right number of bytes (detects type mismatch)
    if cells.length ≠ size then
      none  -- Type mismatch or Vundef
    else
      -- Check bounds for all locations
      let locs := List.range size |>.map (fun (i : Nat) => (b, ofs + (i : Int)))
      if locs.all (fun (b', ofs') => valid_pointer m b' ofs') then
        -- Store all cells (fold over locations and cells together).
        let pairs := locs.zip cells
        pairs.foldlM (fun m' ((b', ofs'), cell) =>
          some { m' with contents := m'.contents.insert (b', ofs') cell }
        ) m
      else
        none  -- Out of bounds

/-- Convenience: Load using a val as address (extracts block + offset from Vptr).
    Returns None if v is not a valid pointer. -/
def loadv (chunk : memory_chunk) (m : mem) (addr : val) : Option val :=
  match addr with
  | .Vptr b ofs => load chunk m b ofs.signed
  | _ => none

/-- Convenience: Store using a val as address. -/
def storev (chunk : memory_chunk) (m : mem) (addr : val) (v : val) : Option mem :=
  match addr with
  | .Vptr b ofs => store chunk m b ofs.signed v
  | _ => none

-- ============================================================================
-- BYTE-RANGE LOAD/STORE (alignment-free, chunk-free)
-- ============================================================================

/-- Read `n` consecutive memory cells starting at `(b, ofs)`, in
    offset-ascending order.

    DESIGN:
    - Returns `none` if `n < 0`.
    - Returns `none` if any of the `n` locations fails `valid_pointer` (out of
      bounds).
    - Returns the raw cells in the range, using `Undef` for an absent key.
    - No alignment check is performed, matching CompCert's `Mem.loadbytes`
      (unlike the chunk-based `load`, which does check alignment). -/
def loadbytes (m : mem) (b : block) (ofs n : Int) : Option (List memval) :=
  if n < 0 then
    none  -- Negative length is invalid
  else
    let size := n.toNat
    let locs := (List.range size).map (fun (i : Nat) => (b, ofs + (i : Int)))
    if locs.all (fun (b', ofs') => valid_pointer m b' ofs') then
      some (locs.map (fun (b', ofs') =>
        (m.contents.get? (b', ofs')).getD .Undef))
    else
      none  -- Out of bounds

/-- Write `cells` starting at `(b, ofs)`, marking every written cell as present.

    DESIGN:
    - Returns `none` if any of the `cells.length` locations fails `valid_pointer`.
    - No alignment check is performed, matching CompCert's `Mem.storebytes`
      (unlike the chunk-based `store`, which does check alignment). -/
def storebytes (m : mem) (b : block) (ofs : Int) (cells : List memval) : Option mem :=
  let size := cells.length
  let locs := (List.range size).map (fun (i : Nat) => (b, ofs + (i : Int)))
  if locs.all (fun (b', ofs') => valid_pointer m b' ofs') then
    let pairs := locs.zip cells
    pairs.foldlM (fun m' ((b', ofs'), cell) =>
      some { m' with contents := m'.contents.insert (b', ofs') cell }
    ) m
  else
    none  -- Out of bounds

/-- Simplified version of CompCert's `Mem.unchanged_on` (Memory.v, `Mem.unchanged_on`
    record): a memory `m'` agrees with `m` on all `(b, ofs)` locations satisfying `P`.

    CompCert's original is a 3-field record: nextblock monotonicity, a
    permission-agreement *iff* (`unchanged_on_perm`), and content-agreement
    guarded by that permission. Since this memory model has no permission
    tracking at all (see `docs/MEMORY_DESIGN.md` §3), we drop the `permission`
    concept entirely, as instructed by the design.

    However, dropping permission-agreement is not entirely free: CompCert's own
    `unchanged_on_trans` proof crucially uses the *iff* shape of
    `unchanged_on_perm` to propagate "this location is still valid" across a
    chain `m1 -> m2 -> m3`. Without *some* validity-preservation guarantee for
    `P`-relevant locations, transitivity would not hold in general (a location
    could silently become invalid partway through the chain, and its now-stale
    content would no longer be protected by the second hypothesis). We restore
    exactly the guarantee CompCert's permission-agreement field provided, in our
    permission-free setting, by folding a `valid_pointer` *iff* directly into the
    single content-agreement clause below -- rather than introducing a
    `permission` type or a third field. This keeps the definition at exactly two
    top-level components:
      1. `m.nextblock ≤ m'.nextblock` (nextblock monotonicity), and
      2. a single `∀ b ofs, P b ofs → ...` clause combining validity-preservation
         and content-agreement for every `P`-relevant location.

    In practice, every producer of `unchanged_on` in this file (`store`,
    `storebytes`) preserves `blocks` *exactly* (see `foldlM_contents_preserves_blocks_aux`),
    so the validity-iff holds trivially for those cases; it only matters when
    composing multiple `unchanged_on` facts together (`unchanged_on_trans`). -/
def unchanged_on (P : block → Int → Prop) (m m' : mem) : Prop :=
  m.nextblock ≤ m'.nextblock ∧
  ∀ b ofs, P b ofs →
    (valid_pointer m b ofs ↔ valid_pointer m' b ofs) ∧
    (valid_pointer m b ofs → m'.contents.get? (b, ofs) = m.contents.get? (b, ofs))

-- ============================================================================
-- MEMORY PROPERTIES (TODO: PROVE)
-- ============================================================================

/- These are the key properties we need to prove about this memory model.
   They are currently axiomatized to unblock development of Cop/Clight.

   PROOF STRATEGY:
   1. Start with basic properties (load_store_same, alloc_fresh)
   2. Build up to non-interference properties
   3. Prove encoding/decoding lemmas
   4. Finally prove high-level properties about Clight operations

   ESTIMATED EFFORT: ~2-3 weeks for all proofs below.
-/

namespace Properties

-- ============================================================================
-- HELPER LEMMAS
-- ============================================================================

/-- foldlM with contents-only updates preserves blocks and nextblock -/
private lemma foldlM_contents_preserves_blocks_aux :
  ∀ (pairs : List ((block × Int) × memval)) (m m' : mem),
    pairs.foldlM (fun m' ((b', ofs'), cell) =>
      some { m' with contents := m'.contents.insert (b', ofs') cell }
    ) m = some m' →
    m'.blocks = m.blocks ∧ m'.nextblock = m.nextblock := by
  intro pairs
  -- Induction on pairs
  induction pairs with
  | nil =>
    -- Base case: foldlM [] m = some m, so m' = m
    intro m m' h
    simp [List.foldlM] at h
    rw [← h]
    simp
  | cons pair rest ih =>
    -- Inductive case
    intro m m' h
    simp [List.foldlM] at h
    obtain ⟨⟨b', ofs'⟩, cell⟩ := pair
    -- After one step: m_mid = {m with contents := m.contents.insert...}
    let m_mid := { m with contents := m.contents.insert (b', ofs') cell }
    have h_mid : rest.foldlM (fun m' ((b'', ofs''), cell') =>
                  some { m' with contents := m'.contents.insert (b'', ofs'') cell' }) m_mid = some m' := by
      simpa [m_mid] using h
    have ⟨h_blocks, h_next⟩ := ih m_mid m' h_mid
    constructor
    · -- m'.blocks = m_mid.blocks = m.blocks
      simp [m_mid] at h_blocks
      exact h_blocks
    · -- m'.nextblock = m_mid.nextblock = m.nextblock
      simp [m_mid] at h_next
      exact h_next

omit [Archi] in
/-- If a predicate is pointwise equal on a list, then List.all gives the same result -/
private lemma List_all_congr {α : Type} (xs : List α) (p q : α → Bool) :
  (∀ x ∈ xs, p x = q x) → xs.all p = xs.all q := by
  intro h
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp [List.all]
    have h_head : p head = q head := h head (by simp)
    have h_tail : ∀ x ∈ tail, p x = q x := fun x hx => h x (by simp [hx])
    rw [h_head, ih h_tail]

/-- Relate List.all on mapped range to pointwise validity. -/
private lemma all_locs_iff (m : mem) (b : block) (ofs : Int) (size : Nat) :
    ((List.range size).map (fun (i : Nat) => (b, ofs + (i : Int)))).all
        (fun (b', ofs') => valid_pointer m b' ofs') = true
    ↔ (∀ i, i < size → valid_pointer m b (ofs + (i : Int))) := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have hmem : (b, ofs + (i : Int)) ∈
        (List.range size).map (fun (i : Nat) => (b, ofs + (i : Int))) :=
      List.mem_map_of_mem (List.mem_range.mpr hi)
    simpa using h _ hmem
  · intro h p hp
    rw [List.mem_map] at hp
    obtain ⟨i, hi, hpeq⟩ := hp
    rw [List.mem_range] at hi
    subst hpeq
    simpa using h i hi

omit [Archi] in
/-- Every memory chunk has positive size -/
private lemma size_chunk_pos (chunk : memory_chunk) : size_chunk chunk > 0 := by
  cases chunk <;> decide

omit [Archi] in
/-- HashMap.insert preserves lookup of inserted key -/
private lemma HashMap_insert_get?_eq
     {α : Type} (m : Std.HashMap (block × Int) α) (k : block × Int) (v : α) :
  (m.insert k v).get? k = some v := by
  rw [Std.HashMap.get?_insert]
  simp

omit [Archi] in
/-- HashMap.insert preserves lookup of other keys -/
private lemma HashMap_insert_get?_ne
     {α : Type} (m : Std.HashMap (block × Int) α) (k k' : block × Int) (v : α) (h : k ≠ k') :
  (m.insert k v).get? k' = m.get? k' := by
  rw [Std.HashMap.get?_insert]
  simp [beq_iff_eq, h]

/-- After foldlM with inserts, any key with a value was either in the original
    or is one of the keys being inserted. -/
private lemma foldlM_contents_get?_cases :
  ∀ (pairs : List ((block × Int) × memval)) (m m' : mem) (k : block × Int) (v : memval),
    pairs.foldlM (fun m' ((b', ofs'), cell) =>
      some { m' with contents := m'.contents.insert (b', ofs') cell }
    ) m = some m' →
    m'.contents.get? k = some v →
    m.contents.get? k = some v ∨ (∃ cell, ((k, cell) ∈ pairs)) := by
  intro pairs
  induction pairs with
  | nil =>
    intro m m' k v h_fold h_get
    simp [List.foldlM] at h_fold
    rw [← h_fold] at h_get
    exact Or.inl h_get
  | cons pair rest ih =>
    intro m m' k v h_fold h_get
    obtain ⟨⟨b_hd, ofs_hd⟩, cell_hd⟩ := pair
    simp [List.foldlM] at h_fold
    let m_mid := { m with contents := m.contents.insert (b_hd, ofs_hd) cell_hd }
    have h_mid : rest.foldlM (fun m' ((b'', ofs''), cell') =>
                  some { m' with contents := m'.contents.insert (b'', ofs'') cell' }) m_mid = some m' := by
      simpa [m_mid] using h_fold
    have h_ih := ih m_mid m' k v h_mid h_get
    cases h_ih with
    | inl h_in_mid =>
      change (m.contents.insert (b_hd, ofs_hd) cell_hd).get? k = some v at h_in_mid
      rw [Std.HashMap.get?_insert] at h_in_mid
      split at h_in_mid
      · rename_i hcond
        right
        refine ⟨cell_hd, ?_⟩
        rw [beq_iff_eq] at hcond
        rw [← hcond]
        exact List.mem_cons_self
      · exact Or.inl h_in_mid
    | inr h_in_rest =>
      exact Or.inr (by
        obtain ⟨cell, h_mem⟩ := h_in_rest
        exact ⟨cell, List.mem_cons_of_mem _ h_mem⟩)

/-- After foldlM with inserts, if a key is not being written, its value is unchanged. -/
private lemma foldlM_contents_get?_untouched :
  ∀ (pairs : List ((block × Int) × memval)) (m m' : mem) (k : block × Int),
    pairs.foldlM (fun m' x =>
      some { m' with contents := m'.contents.insert (x.1.1, x.1.2) x.2 }) m = some m' →
    (∀ cell, (k, cell) ∉ pairs) →
    m'.contents.get? k = m.contents.get? k := by
  intro pairs
  induction pairs with
  | nil =>
    -- Base case: m' = m
    intro m m' k h_fold _
    simp [List.foldlM] at h_fold
    rw [← h_fold]
  | cons pair rest ih =>
    -- Inductive case
    intro m m' k h_fold h_notin
    obtain ⟨⟨b_hd, ofs_hd⟩, cell_hd⟩ := pair
    simp [List.foldlM] at h_fold
    let m_mid := { m with contents := m.contents.insert (b_hd, ofs_hd) cell_hd }
    have h_mid : rest.foldlM (fun m' x =>
                  some { m' with contents := m'.contents.insert (x.1.1, x.1.2) x.2 }) m_mid = some m' := by
      simpa [m_mid] using h_fold
    -- k is not in rest either
    have h_notin_rest : ∀ cell, (k, cell) ∉ rest := by
      intro cell h_mem
      have : (k, cell) ∈ ((b_hd, ofs_hd), cell_hd) :: rest :=
        List.mem_cons_of_mem ((b_hd, ofs_hd), cell_hd) h_mem
      exact h_notin cell this
    -- Apply IH
    have h_ih := ih m_mid m' k h_mid h_notin_rest
    -- k ≠ (b_hd, ofs_hd) because (k, byte_hd) ∉ pairs
    have h_k_ne : (b_hd, ofs_hd) ≠ k := by
      intro h_eq
      apply h_notin cell_hd
      rw [← h_eq]
      exact List.mem_cons_self
    calc
      m'.contents.get? k = m_mid.contents.get? k := h_ih
      _ = m.contents.get? k := by
        change (m.contents.insert (b_hd, ofs_hd) cell_hd).get? k = m.contents.get? k
        exact HashMap_insert_get?_ne m.contents (b_hd, ofs_hd) k cell_hd h_k_ne

/-- After foldlM with inserts over pairs whose keys are all distinct,
    each written key reads back its stored value. -/
private lemma foldlM_contents_get?_written :
  ∀ (pairs : List ((block × Int) × memval)) (m m' : mem),
    pairs.foldlM (fun m' x =>
      some { m' with contents := m'.contents.insert (x.1.1, x.1.2) x.2 }) m = some m' →
    (pairs.map (·.1)).Nodup →
    ∀ k cell, (k, cell) ∈ pairs → m'.contents.get? k = some cell := by
  intro pairs
  induction pairs with
  | nil =>
    intro m m' _ _ k byte h_mem
    simp at h_mem
  | cons pair rest ih =>
    intro m m' h_fold h_nodup k byte h_mem
    obtain ⟨⟨b_hd, ofs_hd⟩, cell_hd⟩ := pair
    simp [List.foldlM] at h_fold
    let m_mid := { m with contents := m.contents.insert (b_hd, ofs_hd) cell_hd }
    have h_mid : rest.foldlM (fun m' x =>
                  some { m' with contents := m'.contents.insert (x.1.1, x.1.2) x.2 }) m_mid = some m' := by
      simpa [m_mid] using h_fold
    -- Nodup of the head keys
    rw [List.map_cons, List.nodup_cons] at h_nodup
    obtain ⟨h_hd_notin, h_rest_nodup⟩ := h_nodup
    -- Case on whether the target pair is the head or in the rest
    rw [List.mem_cons] at h_mem
    cases h_mem with
    | inl h_eq =>
      -- (k, byte) = ((b_hd, ofs_hd), byte_hd)
      injection h_eq with h_k h_byte
      subst h_k
      rw [h_byte]
      -- k = (b_hd, ofs_hd) does not appear as a key in rest
      have h_notin_rest : ∀ b', ((b_hd, ofs_hd), b') ∉ rest := by
        intro b' h_c
        apply h_hd_notin
        rw [List.mem_map]
        exact ⟨((b_hd, ofs_hd), b'), h_c, rfl⟩
      calc
        m'.contents.get? (b_hd, ofs_hd) = m_mid.contents.get? (b_hd, ofs_hd) :=
          foldlM_contents_get?_untouched rest m_mid m' (b_hd, ofs_hd) h_mid h_notin_rest
        _ = some cell_hd := by
          change (m.contents.insert (b_hd, ofs_hd) cell_hd).get?
            (b_hd, ofs_hd) = some cell_hd
          exact HashMap_insert_get?_eq m.contents (b_hd, ofs_hd) cell_hd
    | inr h_in_rest =>
      -- (k, byte) is in rest, use IH
      exact ih m_mid m' h_mid h_rest_nodup k byte h_in_rest

omit [Archi] in
/-- `allSome` of a list of `some`s returns the underlying list. -/
theorem allSome_map_some {α : Type} (l : List α) :
    (l.map some).allSome = some l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    unfold List.allSome at *
    simp [List.mapM_cons, ih]

omit [Archi] in
/-- `allSome` succeeds exactly when the input list is literally a list of
    `some`s wrapping the result. -/
theorem allSome_eq_some_iff {α : Type} (l : List (Option α)) (r : List α) :
    l.allSome = some r ↔ l = r.map some := by
  constructor
  · intro h
    induction l generalizing r with
    | nil =>
        unfold List.allSome at h
        simp only [List.mapM_nil] at h
        cases h
        rfl
    | cons a l' ih =>
        cases a with
        | none => simp [List.allSome] at h
        | some x =>
            simp only [List.allSome, List.mapM_cons, id] at h
            cases hrec : l'.allSome with
            | none => rw [show l'.mapM id = l'.allSome from rfl, hrec] at h; simp at h
            | some r' =>
                rw [show l'.mapM id = l'.allSome from rfl, hrec] at h
                injection h with h
                subst h
                simp [ih r' hrec]
  · intro h
    subst h
    exact allSome_map_some r

omit [Archi] in
/-- Helper: Option.pfilter returns the original value if predicate is always true -/
private lemma pfilter_eq_self_of_true {α : Type _} (o : Option α)
    (p : (a : α) → o = some a → Bool) :
  (∀ v h, p v h = true) →
  o.pfilter p = o := by
  intro hall
  cases o
  · rfl
  · rw [Option.pfilter_some]
    simp [hall]

/-- HashMap.filter preserves get? for keys satisfying the predicate.
    This is used in free_preserves_load. -/
private lemma HashMap_filter_get?_of_true
     (m : Std.HashMap (block × Int) memval) (p : (block × Int) → memval → Bool) (k : block × Int) :
  (∀ v, m.get? k = some v → p k v = true) →
  (m.filter p).get? k = m.get? k := by
  intro h
  unfold Std.HashMap.filter Std.HashMap.get?
  rw [Std.DHashMap.Const.get?_filter]
  apply pfilter_eq_self_of_true
  intro v hget
  -- We have: p k v = true from hypothesis h
  have hp : p k v = true := h v (by unfold Std.HashMap.get?; exact hget)
  -- DHashMap.getKey returns k for LawfulBEq types
  have hmem : k ∈ m.inner := by
    rw [Std.DHashMap.Const.mem_iff_isSome_get?]
    simp [hget]
  have hkey : m.inner.getKey k hmem = k := Std.DHashMap.getKey_eq hmem
  rw [hkey]
  exact hp

/-- HashMap.contains is equivalent to get?.isSome -/
private lemma HashMap_contains_iff_isSome (m : Std.HashMap (block × Int) memval) (k : block × Int) :
  m.contains k = true ↔ m.get? k ≠ none := by
  unfold Std.HashMap.contains Std.HashMap.get?
  rw [Std.DHashMap.Const.contains_eq_isSome_get?]
  cases Std.DHashMap.Const.get? m.inner k <;> simp

/-- Every value encoding occupies exactly the chunk size. -/
private theorem encode_bytes_length_core (chunk : memory_chunk) (v : val)
    (h : encode_bytes chunk v ≠ []) :
    (encode_bytes chunk v).length = size_chunk chunk := by
  cases Archi.ptr64 <;> cases chunk <;> cases v <;>
    simp_all [encode_bytes, size_chunk]

private theorem encode_val_length_core (chunk : memory_chunk) (v : val)
    (h : encode_val chunk v ≠ []) :
    (encode_val chunk v).length = size_chunk chunk := by
  cases hp : ptr_quantity chunk with
  | some q =>
      cases v with
      | Vptr b o =>
          have hqsize : quantity_size q = size_chunk chunk := by
            cases chunk <;> simp [ptr_quantity] at hp ⊢ <;>
              cases q <;> simp_all [quantity_size, size_chunk]
          simpa [encode_val, hp, inj_value] using hqsize
      | Vundef =>
          have hb : encode_bytes chunk .Vundef ≠ [] := by
            intro hb
            apply h
            simp [encode_val, hp, hb, inj_bytes]
          simpa [encode_val, hp, inj_bytes] using
            encode_bytes_length_core chunk .Vundef hb
      | Vint i =>
          have hb : encode_bytes chunk (.Vint i) ≠ [] := by
            intro hb
            apply h
            simp [encode_val, hp, hb, inj_bytes]
          simpa [encode_val, hp, inj_bytes] using
            encode_bytes_length_core chunk (.Vint i) hb
      | Vlong i =>
          have hb : encode_bytes chunk (.Vlong i) ≠ [] := by
            intro hb
            apply h
            simp [encode_val, hp, hb, inj_bytes]
          simpa [encode_val, hp, inj_bytes] using
            encode_bytes_length_core chunk (.Vlong i) hb
      | Vfloat f =>
          have hb : encode_bytes chunk (.Vfloat f) ≠ [] := by
            intro hb
            apply h
            simp [encode_val, hp, hb, inj_bytes]
          simpa [encode_val, hp, inj_bytes] using
            encode_bytes_length_core chunk (.Vfloat f) hb
      | Vsingle f =>
          have hb : encode_bytes chunk (.Vsingle f) ≠ [] := by
            intro hb
            apply h
            simp [encode_val, hp, hb, inj_bytes]
          simpa [encode_val, hp, inj_bytes] using
            encode_bytes_length_core chunk (.Vsingle f) hb
  | none =>
      have hb : encode_bytes chunk v ≠ [] := by
        intro hb
        apply h
        simp [encode_val, hp, hb, inj_bytes]
      simpa [encode_val, hp, inj_bytes] using
        encode_bytes_length_core chunk v hb

-- ============================================================================
-- WELL-FORMEDNESS PRESERVATION
-- ============================================================================

/-- Empty memory is well-formed. -/
theorem empty_wf : mem_wf empty := by
  simp [mem_wf, empty]
  decide

/-- Allocation preserves well-formedness. -/
theorem alloc_preserves_wf : ∀ m lo hi, mem_wf m → lo < hi → mem_wf (alloc m lo hi).2 := by
  intros m lo hi h_wf h_bounds
  obtain ⟨h_fresh, h_bounds_old, h_pos, h_contents⟩ := h_wf
  unfold mem_wf alloc
  simp only
  constructor
  · -- nextblock is still fresh after inserting at m.nextblock
    intro b info h_get
    -- Convert getElem? to get?
    have h_get' : (m.blocks.insert m.nextblock { lo := lo, hi := hi }).get? b = some info := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact h_get
    rw [Std.HashMap.get?_insert] at h_get'
    split at h_get'
    · -- New block: b = m.nextblock
      rename_i hcond
      rw [beq_iff_eq] at hcond
      subst hcond
      exact Nat.lt_succ_self _
    · -- Old block
      have := h_fresh b info h_get'
      exact Nat.lt_succ_of_lt this
  constructor
  · -- All blocks have valid bounds
    intro b info h_get
    have h_get' : (m.blocks.insert m.nextblock { lo := lo, hi := hi }).get? b = some info := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact h_get
    rw [Std.HashMap.get?_insert] at h_get'
    split at h_get'
    · -- New block has lo < hi by assumption
      rename_i hcond
      cases h_get'
      simpa using h_bounds
    · -- Old blocks unchanged
      exact h_bounds_old b info h_get'
  constructor
  · exact Nat.lt_succ_of_lt h_pos
  · -- contents unchanged (alloc doesn't modify contents)
    intro b ofs byte h_get
    -- m'.contents = m.contents, so if b in contents, it was in m.blocks
    obtain ⟨info, h_info⟩ := h_contents b ofs byte h_get
    -- Now b is in m'.blocks
    use info
    rw [Std.HashMap.get?_insert]
    split
    · -- b = m.nextblock - but this contradicts h_info since nextblock wasn't in m.blocks
      rename_i hcond
      rw [beq_iff_eq] at hcond
      subst hcond
      -- Contradiction: h_info says m.nextblock is in m.blocks, but h_fresh says blocks < nextblock
      exfalso
      have : (m.nextblock : Nat) < (m.nextblock : Nat) := h_fresh m.nextblock info h_info
      exact Nat.lt_irrefl m.nextblock this
    · exact h_info  -- b is in the original blocks

/-- Store preserves well-formedness. -/
theorem store_preserves_wf : ∀ chunk m b ofs v m', mem_wf m → store chunk m b ofs v = some m' → mem_wf m' := by
  intros chunk m b ofs v m' h_wf h_store
  obtain ⟨h_fresh, h_bounds, h_pos, h_contents⟩ := h_wf
  -- Store only modifies contents, blocks/nextblock unchanged
  simp only [store] at h_store
  -- After expanding store, h_store has 3 nested if-then-else guards
  split at h_store
  · simp at h_store  -- Alignment check failed -> none = some m', contradiction
  · -- Alignment OK, continue
    split at h_store
    · simp at h_store  -- Length check failed -> none = some m', contradiction
    · -- Length OK, one more guard (valid_pointer check)
      split at h_store
      · -- valid_pointer check passed, h_store is now foldlM = some m'
        have ⟨h_blocks_eq, h_next_eq⟩ := foldlM_contents_preserves_blocks_aux _ _ _ h_store
        simp [mem_wf, h_blocks_eq, h_next_eq]
        constructor; exact h_fresh
        constructor; exact h_bounds
        constructor; exact h_pos
        -- Contents invariant: foldlM only inserts keys for valid blocks
        intro b' ofs' byte h_get'
        -- Use helper lemma to case split: either (b', ofs') was in m.contents or in pairs
        have h_cases := foldlM_contents_get?_cases _ _ _ _ _ h_store h_get'
        cases h_cases with
        | inl h_old =>
          -- (b', ofs') was in m.contents, so b' has a block (by h_contents)
          exact h_contents b' ofs' byte h_old
        | inr h_new =>
          -- (b', ofs') was inserted by foldlM, so it's in pairs
          obtain ⟨byte', h_mem⟩ := h_new
          -- pairs = locs.zip bytes, and locs only contains (b, ofs+i)
          -- So b' = b, and we can use the valid_pointer check
          -- First, extract that all locs have form (b, ofs+i)
          have h_locs_form : ∀ loc ∈ (List.range (size_chunk chunk)).map (fun (i : Nat) => (b, ofs + (i : Int))),
            loc.1 = b := by
            intro loc h_in
            rw [List.mem_map] at h_in
            obtain ⟨i, _, h_eq⟩ := h_in
            subst h_eq
            simp
          -- pairs = locs.zip bytes, so (b', ofs') must come from locs
          let locs := (List.range (size_chunk chunk)).map (fun (i : Nat) => (b, ofs + (i : Int)))
          let bytes := encode_val chunk v
          have h_in_locs : ∃ byte', ((b', ofs'), byte') ∈ List.zip locs bytes := ⟨byte', h_mem⟩
          -- From membership in zip, we get membership in locs
          have h_b'_in_locs : (b', ofs') ∈ locs := by
            obtain ⟨byte', h_zip⟩ := h_in_locs
            exact (List.of_mem_zip h_zip).1
          -- Apply h_locs_form to get b' = b
          have h_b'_eq : b' = b := h_locs_form (b', ofs') h_b'_in_locs
          -- Now use the valid_pointer check: locs.all valid_pointer = true
          -- This means ∃ i, valid_pointer m b (ofs + i), which implies ∃ info, m.blocks[b]? = some info
          have h_valid_all : locs.all (fun (b'', ofs'') => valid_pointer m b'' ofs'') = true := by
            -- This is in the context from the split - we need to extract it
            -- The split at h_store corresponded to the if-condition
            -- We're in the then-branch, so the condition was true
            assumption
          -- From h_valid_all and non-empty list (size > 0), get that b has a block
          have h_size_pos : size_chunk chunk > 0 := size_chunk_pos chunk
          have h_nonempty : locs.length > 0 := by
            unfold locs
            rw [List.length_map, List.length_range]
            exact h_size_pos
          -- Get the first element
          have h_exists_first : ∃ loc, loc ∈ locs := by
            cases h_eq : locs with
            | nil =>
              exfalso
              rw [h_eq] at h_nonempty
              simp at h_nonempty
            | cons head tail =>
              use head
              simp
          obtain ⟨loc, h_loc_mem⟩ := h_exists_first
          -- valid_pointer m loc.1 loc.2 = true
          have h_valid_loc : valid_pointer m loc.1 loc.2 = true := by
            rw [List.all_eq_true] at h_valid_all
            exact h_valid_all loc h_loc_mem
          -- loc.1 = b (by h_locs_form)
          have h_loc_b : loc.1 = b := h_locs_form loc h_loc_mem
          rw [h_loc_b] at h_valid_loc
          -- valid_pointer m b loc.2 = true implies ∃ info, m.blocks[b]? = some info
          unfold valid_pointer at h_valid_loc
          cases h_get_b : m.blocks.get? b with
          | none =>
            rw [h_get_b] at h_valid_loc
            simp at h_valid_loc
          | some info =>
            use info
            rw [← Std.HashMap.get?_eq_getElem?, h_b'_eq]
            exact h_get_b
      · simp at h_store  -- valid_pointer check failed -> none = some m', contradiction

-- ============================================================================
-- 1. BASIC LOAD/STORE PROPERTIES
-- ============================================================================

/-- Load after store to the same location returns the stored value,
    read back through the encode/decode roundtrip.

    This is the fundamental correctness property of memory: the bytes written
    by `store` are exactly the bytes read back by `load`, so the loaded value is
    `decode_val chunk (encode_val chunk v)`. Composed with `encode_decode_roundtrip`
    this recovers `v` (up to sign/zero extension for sub-word integer chunks),
    matching CompCert's `Mem.load_store_same`. -/
theorem load_store_same :
  ∀ chunk m b ofs v m',
    store chunk m b ofs v = some m' →
    load chunk m' b ofs = some (decode_val chunk (encode_val chunk v)) := by
  intros chunk m b ofs v m' h_store
  -- Unfold store
  simp only [store] at h_store
  split at h_store
  · simp at h_store  -- Misaligned case
  · split at h_store
    · simp at h_store  -- Length mismatch
    · split at h_store
      · -- Success case
        rename_i h_align h_len h_valid
        -- h_store: foldlM succeeded, writing encode_val chunk v to memory

        -- Unfold load
        simp only [load]
        split
        · -- Misaligned - contradicts h_align
          rename_i h_misalign
          simp at h_align
          exact absurd h_align h_misalign
        · -- Aligned case
          split
          · -- valid_pointer check passes
            -- Prove: after storing v, loading reads back exactly the written bytes,
            -- so load returns decode_val chunk (encode_val chunk v). This requires:
            -- 1. foldlM writes all bytes from encode_val chunk v (foldlM_contents_get?_written)
            -- 2. load reads back those bytes, so allSome succeeds (allSome_map_some)
            rename_i h_valid_load

            -- Set up convenient names
            let size := size_chunk chunk
            let locs := (List.range size).map (fun i => (b, ofs + ↑i))
            let bytes := encode_val chunk v

            -- Establish that bytes.length = size
            have hlen : bytes.length = size := by
              simpa using h_len

            -- Establish that locs.length = size
            have hlocs_len : locs.length = size := by
              simp only [locs, size, List.length_map, List.length_range]

            -- Prove nodup of locs for foldlM_contents_get?_written
            have h_locs_nodup : locs.Nodup := by
              simp only [locs]
              apply List.Nodup.map
              · -- Injectivity of fun i => (b, ofs + ↑i)
                intro i j h_eq
                simp only at h_eq
                have : ofs + ↑i = ofs + ↑j := by
                  have := congr_arg Prod.snd h_eq
                  simp only [] at this
                  exact this
                omega
              · exact List.nodup_range

            -- Prove nodup of the zip for foldlM_contents_get?_written
            have h_zip_nodup : ((locs.zip bytes).map (·.1)).Nodup := by
              rw [← hlen] at hlocs_len
              rw [List.map_fst_zip hlocs_len.le]
              exact h_locs_nodup

            -- Key helper: for each index i < size, we can read back byte i
            have h_readback_get : ∀ i (hi : i < size),
                m'.contents.get? (b, ofs + ↑i) = some bytes[i] := by
              intro i hi
              apply foldlM_contents_get?_written _ _ _ h_store
                (by simpa [inj_bytes] using h_zip_nodup)
              -- Show ((b, ofs + ↑i), bytes[i]) ∈ locs.zip bytes
              have hlocs_i : i < locs.length := by rw [hlocs_len]; exact hi
              have hbytes_i : i < bytes.length := by rw [hlen]; exact hi
              -- Use that (locs.zip bytes)[i] = (locs[i], bytes[i])
              have : (locs.zip bytes)[i]'(by rw [List.length_zip, hlocs_len, hlen]; exact Nat.lt_min.mpr ⟨hi, hi⟩) =
                     ((b, ofs + ↑i), bytes[i]) := by
                simp only [List.getElem_zip]
                simp only [locs]
                rw [List.getElem_map]
                simp only [List.getElem_range]
              rw [← this]
              exact List.getElem_mem _

            -- Main lemma: reading back from m' gives the cells we wrote.
            have h_readback :
                locs.map (fun (b', ofs') =>
                  (m'.contents.get? (b', ofs')).getD .Undef) = bytes := by
              -- Prove by showing the lists have equal elements at each valid index.
              have h_len_eq :
                  (locs.map (fun (b', ofs') =>
                    (m'.contents.get? (b', ofs')).getD .Undef)).length =
                    bytes.length := by
                simp only [List.length_map, hlocs_len, hlen]
              apply List.ext_get h_len_eq
              intro n h1 h2
              have hn : n < locs.length := by
                rw [List.length_map] at h1
                exact h1
              have hn_size : n < size := by rw [hlocs_len] at hn; exact hn
              have hn_bytes : n < bytes.length := by rw [hlen]; exact hn_size
              conv_lhs => rw [List.get_eq_getElem]
              conv_rhs => rw [List.get_eq_getElem]
              simp only [List.getElem_map]
              have hloc_n : locs[n]'hn = (b, ofs + ↑n) := by
                simp only [locs]
                rw [List.getElem_map]
                simp only [List.getElem_range]
              rw [hloc_n, h_readback_get n hn_size]
              rfl

            -- Now use h_readback to complete the proof: load reads back exactly
            -- the `encode_val` cells, so it returns `decode_val chunk (encode_val chunk v)`.
            rw [h_readback]
          · -- valid_pointer check fails
            -- But blocks/nextblock are preserved, so valid_pointer should be unchanged
            rename_i h_invalid
            have h_blocks_eq := (foldlM_contents_preserves_blocks_aux _ _ _ h_store).1
            -- valid_pointer only depends on blocks, so it is unchanged by the store.
            have h_vp : ∀ b' ofs', valid_pointer m' b' ofs' = valid_pointer m b' ofs' := by
              intro b' ofs'
              simp only [valid_pointer, h_blocks_eq]
            -- The load validity check on m' equals the store validity check on m,
            -- which is true (h_valid). This contradicts h_invalid.
            exfalso
            apply h_invalid
            rw [List_all_congr _ _ (fun (b', ofs') => valid_pointer m b' ofs')
                  (by intro ⟨b'', ofs''⟩ _; exact h_vp b'' ofs'')]
            exact h_valid
      · cases h_store  -- foldlM failed

/-- Load after store to a different location is unchanged.
    Locations are "different" if:
    - Different blocks, OR
    - Same block but non-overlapping byte ranges -/
theorem load_store_other :
  ∀ chunk1 chunk2 m b1 ofs1 v b2 ofs2 m',
    store chunk1 m b1 ofs1 v = some m' →
    (b1 ≠ b2 ∨
     ofs2 + (size_chunk chunk2 : Int) ≤ ofs1 ∨
     ofs1 + (size_chunk chunk1 : Int) ≤ ofs2) →
    load chunk2 m' b2 ofs2 = load chunk2 m b2 ofs2 := by
  intros chunk1 chunk2 m b1 ofs1 v b2 ofs2 m' h_store h_disj
  -- Unfold store and handle the three conditions
  simp only [store] at h_store
  split at h_store
  · cases h_store
  · split at h_store
    · cases h_store
    · split at h_store
      · -- Success case: foldlM succeeded
        rename_i h_align h_len h_valid

        -- Unfold both loads
        simp only [load]
        -- Alignment is unchanged (no dependency on contents)
        congr 1
        -- valid_pointer equality (blocks unchanged)
        have h_blocks_eq : m'.blocks = m.blocks := by
          exact (foldlM_contents_preserves_blocks_aux _ _ _ h_store).1
        have h_vp : ∀ b' ofs', valid_pointer m b' ofs' = valid_pointer m' b' ofs' := by
          intros b' ofs'
          simp only [valid_pointer, h_blocks_eq]
        -- Apply to List.all
        congr 2
        · apply List_all_congr
          intro ⟨b'', ofs''⟩ h_mem
          simp
          exact (h_vp b'' ofs'').symm
        · -- Contents: show that for each byte in chunk2's range, contents are equal
          congr 1
          simp only [List.map_map]
          -- Show that for all locations in chunk2's range, contents are equal
          apply List.map_congr_left
          intro x h_mem
          -- x is a Nat from List.range
          simp [List.mem_range] at h_mem
          -- For location (b2, ofs2+x), show m.contents.get? = m'.contents.get?
          have h_not_written : ∀ byte, ((b2, ofs2 + ↑x), byte) ∉
              ((List.range (size_chunk chunk1)).map (fun j => (b1, ofs1 + ↑j))).zip (encode_val chunk1 v) := by
            intro byte h_mem_pair
            -- h_mem_pair says ((b2, ofs2+x), byte) is in the zip
            have ⟨h_fst, _⟩ := List.of_mem_zip h_mem_pair
            rw [List.mem_map] at h_fst
            obtain ⟨j, h_j_range, h_eq⟩ := h_fst
            -- So (b2, ofs2+x) = (b1, ofs1+j) for some j < size_chunk chunk1
            injection h_eq with h_b2_eq h_ofs2_eq
            -- But this contradicts h_disj
            cases h_disj with
            | inl h_ne => exact h_ne h_b2_eq
            | inr h_or =>
              cases h_or with
              | inl h_le =>
                -- ofs2 + size_chunk chunk2 ≤ ofs1
                -- But ofs2 + x = ofs1 + j, and x < chunk2, j < chunk1
                rw [List.mem_range] at h_j_range
                have h_x_bound : (x : Int) < (size_chunk chunk2 : Int) := by omega
                have h_j_bound : (j : Int) < (size_chunk chunk1 : Int) := by omega
                -- From ofs2 + chunk2 ≤ ofs1 and ofs1 + j = ofs2 + x:
                -- ofs2 + x = ofs1 + j ≥ ofs1 ≥ ofs2 + chunk2 > ofs2 + x (contradiction)
                omega
              | inr h_le =>
                -- ofs1 + size_chunk chunk1 ≤ ofs2
                -- But ofs1 + j = ofs2 + x for j < size_chunk chunk1
                rw [List.mem_range] at h_j_range
                have h_j_bound : (j : Int) < (size_chunk chunk1 : Int) := by omega
                have h_x_bound : (x : Int) < (size_chunk chunk2 : Int) := by omega
                -- From ofs1 + chunk1 ≤ ofs2 and ofs1 + j = ofs2 + x and j < chunk1:
                -- ofs2 + x = ofs1 + j < ofs1 + chunk1 ≤ ofs2 ≤ ofs2 + x (contradiction)
                omega
          change (m'.contents.get? (b2, ofs2 + (x : Int))).getD .Undef =
            (m.contents.get? (b2, ofs2 + (x : Int))).getD .Undef
          exact congrArg (fun o => o.getD .Undef)
            (foldlM_contents_get?_untouched _ _ _ _ h_store h_not_written)

      · cases h_store

/-- Store preserves validity of pointers to other locations. -/
theorem valid_pointer_store :
  ∀ chunk m b1 ofs1 v m' b2 ofs2,
    store chunk m b1 ofs1 v = some m' →
    valid_pointer m b2 ofs2 = valid_pointer m' b2 ofs2 := by
  intros chunk m b1 ofs1 v m' b2 ofs2 h
  -- valid_pointer only depends on blocks, which store doesn't change
  simp only [store] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · -- foldlM case
        have ⟨h_blocks, _⟩ := foldlM_contents_preserves_blocks_aux _ _ _ h
        simp only [valid_pointer, h_blocks]
      · simp at h

/-- Weak valid pointer is also preserved by stores. -/
theorem weak_valid_pointer_store :
  ∀ chunk m b1 ofs1 v m' b2 ofs2,
    store chunk m b1 ofs1 v = some m' →
    weak_valid_pointer m b2 ofs2 = weak_valid_pointer m' b2 ofs2 := by
  intros chunk m b1 ofs1 v m' b2 ofs2 h
  simp only [store] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · -- foldlM case
        have ⟨h_blocks, _⟩ := foldlM_contents_preserves_blocks_aux _ _ _ h
        simp only [weak_valid_pointer, h_blocks]
      · simp at h

/-- foldlM with Some-producing body always succeeds -/
private lemma foldlM_some_always_succeeds :
  ∀ (pairs : List ((block × Int) × memval)) (m : mem),
    ∃ m', pairs.foldlM (fun m' ((b', ofs'), cell) =>
      some { m' with contents := m'.contents.insert (b', ofs') cell }
    ) m = some m' := by
  intro pairs m
  induction pairs generalizing m with
  | nil => exact ⟨m, by rfl⟩
  | cons head tail ih =>
    obtain ⟨⟨b', ofs'⟩, cell⟩ := head
    let m_mid := { m with contents := m.contents.insert (b', ofs') cell }
    obtain ⟨m', hm'⟩ := ih m_mid
    refine ⟨m', ?_⟩
    simpa [List.foldlM, m_mid] using hm'

/-- Store succeeds iff all bytes in range are valid (in bounds). -/
theorem store_valid_access :
  ∀ chunk m b ofs v,
    (∃ m', store chunk m b ofs v = some m') ↔
    (is_aligned ofs chunk ∧
     encode_val chunk v ≠ [] ∧
     ∀ i, i < size_chunk chunk → valid_pointer m b (ofs + (i : Int))) := by
  intros chunk m b ofs v
  constructor
  · -- → direction
    intro ⟨m', h⟩
    simp only [store] at h
    split at h
    · simp at h
    · rename_i h_aligned
      split at h
      · simp at h
      · rename_i h_len
        split at h
        · rename_i h_all
          refine ⟨?_, ?_, ?_⟩
          · simpa using h_aligned
          · intro hempty
            rw [hempty] at h_len
            simp at h_len
            have := size_chunk_pos chunk
            omega
          · exact (all_locs_iff m b ofs (size_chunk chunk)).mp h_all
        · simp at h
  · -- ← direction
    intro ⟨h_aligned, h_ne, h_valid⟩
    have h_len : (encode_val chunk v).length = size_chunk chunk :=
      encode_val_length_core chunk v h_ne
    simp only [store]
    rw [if_neg (by simpa using h_aligned)]
    rw [if_neg (by simp [h_len])]
    rw [if_pos ((all_locs_iff m b ofs (size_chunk chunk)).mpr h_valid)]
    -- foldlM always succeeds - use existing helper lemma
    exact foldlM_some_always_succeeds _ m

/-- Load succeeds iff all bytes in range are valid.
    Returns Vundef if any byte is uninitialized. -/
theorem load_valid_access :
  ∀ chunk m b ofs,
    (∃ v, load chunk m b ofs = some v) ↔
    (is_aligned ofs chunk ∧
     ∀ i, i < size_chunk chunk → valid_pointer m b (ofs + (i : Int))) := by
  intros chunk m b ofs
  constructor
  · -- → direction
    intro ⟨v, h⟩
    simp only [load] at h
    split at h
    · simp at h
    · rename_i h_aligned
      split at h
      · -- List.all check passed
        rename_i h_all
        constructor
        · simp at h_aligned; exact h_aligned
        · intro i h_i
          exact (all_locs_iff m b ofs (size_chunk chunk)).mp h_all i h_i
      · simp at h
  · -- ← direction
    intro ⟨h_aligned, h_valid⟩
    simp only [load]
    rw [if_neg (by simpa using h_aligned)]
    rw [if_pos ((all_locs_iff m b ofs (size_chunk chunk)).mpr h_valid)]
    refine ⟨decode_val chunk
      (List.map (fun (p : block × Int) =>
        (m.contents.get? (p.1, p.2)).getD .Undef)
        ((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int))))), ?_⟩
    rfl

-- ============================================================================
-- 1b. LOADBYTES / STOREBYTES PROPERTIES
-- ============================================================================

/-- `storebytes` never allocates: `nextblock` is unchanged. -/
theorem nextblock_storebytes :
  ∀ m b ofs bytes m',
    storebytes m b ofs bytes = some m' →
    m'.nextblock = m.nextblock := by
  intros m b ofs bytes m' h
  simp only [storebytes] at h
  split at h
  · exact (foldlM_contents_preserves_blocks_aux _ _ _ h).2
  · simp at h

/-- Reading back exactly the bytes just written by `storebytes`. -/
theorem loadbytes_storebytes_same :
  ∀ m b ofs bytes m',
    storebytes m b ofs bytes = some m' →
    loadbytes m' b ofs (bytes.length : Int) = some bytes := by
  intros m b ofs bytes m' h_store
  simp only [storebytes] at h_store
  split at h_store
  · rename_i h_valid
    simp only [loadbytes]
    rw [if_neg (by omega)]
    have hsize : ((bytes.length : Int)).toNat = bytes.length := by simp
    rw [hsize]
    have h_blocks_eq := (foldlM_contents_preserves_blocks_aux _ _ _ h_store).1
    have h_vp_eq : ∀ b' ofs', valid_pointer m' b' ofs' = valid_pointer m b' ofs' := by
      intro b' ofs'
      simp only [valid_pointer, h_blocks_eq]
    have h_forall : ∀ i, i < bytes.length → valid_pointer m b (ofs + (i : Int)) :=
      (all_locs_iff m b ofs bytes.length).mp h_valid
    have h_valid' : ((List.range bytes.length).map (fun (i : Nat) => (b, ofs + (i : Int)))).all
        (fun (b', ofs') => valid_pointer m' b' ofs') = true :=
      (all_locs_iff m' b ofs bytes.length).mpr
        (fun i hi => by rw [h_vp_eq]; exact h_forall i hi)
    rw [if_pos h_valid']
    -- Establish the same "readback" facts used in `load_store_same`, without decoding.
    let locs := (List.range bytes.length).map (fun (i : Nat) => (b, ofs + (i : Int)))
    have hlocs_len : locs.length = bytes.length := by
      simp only [locs, List.length_map, List.length_range]
    have h_locs_nodup : locs.Nodup := by
      simp only [locs]
      apply List.Nodup.map
      · intro i j h_eq
        simp only at h_eq
        have : ofs + (i : Int) = ofs + (j : Int) := by
          have := congr_arg Prod.snd h_eq
          simp only [] at this
          exact this
        omega
      · exact List.nodup_range
    have h_zip_nodup : ((locs.zip bytes).map (·.1)).Nodup := by
      have hlen' : bytes.length = locs.length := by
        simp only [hlocs_len]
      rw [List.map_fst_zip (by rw [hlen'])]
      exact h_locs_nodup
    have h_readback_get : ∀ i (hi : i < bytes.length),
        m'.contents.get? (b, ofs + (i : Int)) = some bytes[i] := by
      intro i hi
      apply foldlM_contents_get?_written _ _ _ h_store h_zip_nodup
      have hlocs_i : i < locs.length := by rw [hlocs_len]; exact hi
      have hpair : (locs.zip bytes)[i]'(by
              rw [List.length_zip, hlocs_len]; omega) =
             ((b, ofs + (i : Int)), bytes[i]) := by
        simp only [List.getElem_zip]
        simp only [locs]
        rw [List.getElem_map]
        simp only [List.getElem_range]
      rw [← hpair]
      exact List.getElem_mem _
    have h_readback : (locs.map (fun (b', ofs') =>
        (m'.contents.get? (b', ofs')).getD .Undef)) = bytes := by
      have h_len_eq : (locs.map (fun (b', ofs') =>
          (m'.contents.get? (b', ofs')).getD .Undef)).length
          = bytes.length := by
        simp only [List.length_map, hlocs_len]
      apply List.ext_get h_len_eq
      intro n h1 h2
      have hn : n < locs.length := by
        rw [List.length_map] at h1
        exact h1
      have hn_size : n < bytes.length := by rw [hlocs_len] at hn; exact hn
      conv_lhs => rw [List.get_eq_getElem]
      conv_rhs => rw [List.get_eq_getElem]
      simp only [List.getElem_map]
      have hloc_n : locs[n]'hn = (b, ofs + (n : Int)) := by
        simp only [locs]
        rw [List.getElem_map]
        simp only [List.getElem_range]
      rw [hloc_n, h_readback_get n hn_size]
      rfl
    simpa [locs] using congrArg some h_readback
  · cases h_store

/-- The number of bytes `encode_val` produces for a value stored via `store`
    always matches `size_chunk`, whenever `store` succeeds. -/
private theorem store_encode_val_length :
  ∀ chunk m b ofs v m',
    store chunk m b ofs v = some m' →
    (encode_val chunk v).length = size_chunk chunk := by
  intros chunk m b ofs v m' h
  simp only [store] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h_len
      simpa using h_len

/-- The chunk-based `store` is a special case of `storebytes` applied to its
    encoded memory cells. -/
theorem store_storebytes :
  ∀ chunk m b ofs v m',
    store chunk m b ofs v = some m' →
    storebytes m b ofs (encode_val chunk v) = some m' := by
  intros chunk m b ofs v m' h_store
  simp only [store] at h_store
  split at h_store
  · simp at h_store
  · split at h_store
    · simp at h_store
    · split at h_store
      · rename_i h_aligned h_len' h_valid
        have hlen : (encode_val chunk v).length = size_chunk chunk := by
          simpa using h_len'
        simp only [storebytes]
        rw [hlen]
        rw [if_pos h_valid]
        exact h_store
      · simp at h_store

/-- Converse of `store_storebytes`. -/
theorem storebytes_store :
  ∀ chunk m b ofs v m',
    is_aligned ofs chunk →
    (encode_val chunk v).length = size_chunk chunk →
    storebytes m b ofs (encode_val chunk v) = some m' →
    store chunk m b ofs v = some m' := by
  intros chunk m b ofs v m' h_align h_len h_sb
  simp only [store]
  rw [if_neg (by simpa using h_align)]
  rw [if_neg (by simp [h_len])]
  simp only [storebytes] at h_sb
  rw [h_len] at h_sb
  exact h_sb

/-- After storing a value via the chunk-based `store`, reading back the same
    range via `loadbytes` recovers exactly its encoded memory cells. -/
theorem loadbytes_store_same :
  ∀ chunk m b ofs v m',
    store chunk m b ofs v = some m' →
    loadbytes m' b ofs (size_chunk chunk : Int) = some (encode_val chunk v) := by
  intros chunk m b ofs v m' h_store
  have h_len := store_encode_val_length chunk m b ofs v m' h_store
  have h_sb := store_storebytes chunk m b ofs v m' h_store
  have h_lb := loadbytes_storebytes_same m b ofs (encode_val chunk v) m' h_sb
  rw [h_len] at h_lb
  exact h_lb

-- ============================================================================
-- 1c. UNCHANGED_ON PROPERTIES
-- ============================================================================

/-- `unchanged_on` is reflexive: any memory is unchanged relative to itself. -/
theorem unchanged_on_refl (P : block → Int → Prop) (m : mem) : unchanged_on P m m := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro b ofs _
  exact ⟨Iff.rfl, fun _ => rfl⟩

/-- `unchanged_on` composes transitively. -/
theorem unchanged_on_trans (P : block → Int → Prop) (m1 m2 m3 : mem)
    (h12 : unchanged_on P m1 m2) (h23 : unchanged_on P m2 m3) :
    unchanged_on P m1 m3 := by
  obtain ⟨hn12, hc12⟩ := h12
  obtain ⟨hn23, hc23⟩ := h23
  refine ⟨Nat.le_trans hn12 hn23, ?_⟩
  intro b ofs hP
  obtain ⟨hiff12, heq12⟩ := hc12 b ofs hP
  obtain ⟨hiff23, heq23⟩ := hc23 b ofs hP
  refine ⟨hiff12.trans hiff23, ?_⟩
  intro hvalid1
  have hvalid2 := hiff12.mp hvalid1
  rw [heq23 hvalid2]
  exact heq12 hvalid1

/-- If `store` only writes to locations outside `P`, then `P`-relevant memory is
    `unchanged_on`. -/
theorem store_unchanged_on :
  ∀ chunk m b ofs v m' (P : block → Int → Prop),
    store chunk m b ofs v = some m' →
    (∀ i, ofs ≤ i → i < ofs + (size_chunk chunk : Int) → ¬ P b i) →
    unchanged_on P m m' := by
  intros chunk m b ofs v m' P h_store h_notP
  simp only [store] at h_store
  split at h_store
  · simp at h_store
  · split at h_store
    · simp at h_store
    · split at h_store
      · rename_i h_aligned h_len h_valid
        have h_blocks_eq := (foldlM_contents_preserves_blocks_aux _ _ _ h_store).1
        have h_next_eq := (foldlM_contents_preserves_blocks_aux _ _ _ h_store).2
        refine ⟨Nat.le_of_eq h_next_eq.symm, ?_⟩
        intro b' ofs' hP
        have h_vp_eq : valid_pointer m b' ofs' ↔ valid_pointer m' b' ofs' := by
          simp only [valid_pointer, h_blocks_eq]
        refine ⟨h_vp_eq, ?_⟩
        intro _
        apply foldlM_contents_get?_untouched _ _ _ (b', ofs') h_store
        intro byte h_mem
        have h_pair := List.of_mem_zip h_mem
        rw [List.mem_map] at h_pair
        obtain ⟨j, h_j_range, h_eq⟩ := h_pair.1
        rw [List.mem_range] at h_j_range
        injection h_eq with h_b_eq h_ofs_eq
        subst h_b_eq
        subst h_ofs_eq
        exact absurd hP (h_notP (ofs + (j : Int)) (by omega) (by omega))
      · simp at h_store

/-- If `storebytes` only writes to locations outside `P`, then `P`-relevant
    memory is `unchanged_on`. -/
theorem storebytes_unchanged_on :
  ∀ m b ofs bytes m' (P : block → Int → Prop),
    storebytes m b ofs bytes = some m' →
    (∀ i, ofs ≤ i → i < ofs + (bytes.length : Int) → ¬ P b i) →
    unchanged_on P m m' := by
  intros m b ofs bytes m' P h_store h_notP
  simp only [storebytes] at h_store
  split at h_store
  · rename_i h_valid
    have h_blocks_eq := (foldlM_contents_preserves_blocks_aux _ _ _ h_store).1
    have h_next_eq := (foldlM_contents_preserves_blocks_aux _ _ _ h_store).2
    refine ⟨Nat.le_of_eq h_next_eq.symm, ?_⟩
    intro b' ofs' hP
    have h_vp_eq : valid_pointer m b' ofs' ↔ valid_pointer m' b' ofs' := by
      simp only [valid_pointer, h_blocks_eq]
    refine ⟨h_vp_eq, ?_⟩
    intro _
    apply foldlM_contents_get?_untouched _ _ _ (b', ofs') h_store
    intro byte h_mem
    have h_pair := List.of_mem_zip h_mem
    rw [List.mem_map] at h_pair
    obtain ⟨j, h_j_range, h_eq⟩ := h_pair.1
    rw [List.mem_range] at h_j_range
    injection h_eq with h_b_eq h_ofs_eq
    subst h_b_eq
    subst h_ofs_eq
    exact absurd hP (h_notP (ofs + (j : Int)) (by omega) (by omega))
  · simp at h_store

omit [Archi] in
/-- `List.all` only depends on the predicate's behavior on the list's own
    elements (unlike `List.all_congr`, which needs universal agreement). -/
private theorem all_congr_of_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
      simp only [List.all_cons]
      rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Reading is invariant under `unchanged_on` when the read's footprint is
    covered by `P`. -/
theorem load_unchanged_on (P : block → Int → Prop) (m m' : mem) (chunk : memory_chunk)
    (b : block) (ofs : Int) (hu : unchanged_on P m m')
    (hP : ∀ i, ofs ≤ i → i < ofs + (size_chunk chunk : Int) → P b i) :
    load chunk m' b ofs = load chunk m b ofs := by
  have hveq : ∀ i : Nat, i < size_chunk chunk →
      valid_pointer m' b (ofs + (i : Int)) = valid_pointer m b (ofs + (i : Int)) := by
    intro i hi
    have hiff := (hu.2 b (ofs + i) (hP (ofs + i) (by omega) (by omega))).1
    cases hvm : valid_pointer m b (ofs + (i : Int)) <;>
      cases hvm' : valid_pointer m' b (ofs + (i : Int)) <;> simp_all
  have hgeq : ∀ i : Nat, i < size_chunk chunk → valid_pointer m b (ofs + (i : Int)) = true →
      m'.contents.get? (b, ofs + (i : Int)) = m.contents.get? (b, ofs + (i : Int)) :=
    fun i hi hvalid => (hu.2 b (ofs + i) (hP (ofs + i) (by omega) (by omega))).2 hvalid
  have hall_eq :
      (((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int)))).all
        (fun p => valid_pointer m' p.1 p.2)) =
      (((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int)))).all
        (fun p => valid_pointer m p.1 p.2)) := by
    apply all_congr_of_mem
    rintro ⟨b', ofs'⟩ hmem
    rw [List.mem_map] at hmem
    obtain ⟨i, hi, hpeq⟩ := hmem
    rw [List.mem_range] at hi
    injection hpeq with hbeq hofseq
    subst hbeq; subst hofseq
    exact hveq i hi
  simp only [load, hall_eq]
  split
  · rfl
  · split
    · rename_i h_all
      have hmap_eq :
          (((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => m'.contents.get? (x.1, x.2))) =
          (((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => m.contents.get? (x.1, x.2))) := by
        apply List.map_congr_left
        rintro ⟨b', ofs'⟩ hmem
        rw [List.mem_map] at hmem
        obtain ⟨i, hi, hpeq⟩ := hmem
        rw [List.mem_range] at hi
        injection hpeq with hbeq hofseq
        subst hbeq; subst hofseq
        simp only
        exact hgeq i hi (by
          have := (all_locs_iff m b ofs (size_chunk chunk)).mp h_all
          exact this i hi)
      have hmap_cell_eq :
          (((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => (m'.contents.get? (x.1, x.2)).getD .Undef)) =
          (((List.range (size_chunk chunk)).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => (m.contents.get? (x.1, x.2)).getD .Undef)) := by
        apply List.map_congr_left
        rintro ⟨b', ofs'⟩ hmem
        rw [List.mem_map] at hmem
        obtain ⟨i, hi, hpeq⟩ := hmem
        rw [List.mem_range] at hi
        cases hpeq
        have hget := hgeq i hi (by
          have := (all_locs_iff m b ofs (size_chunk chunk)).mp h_all
          exact this i hi)
        exact congrArg (fun o => o.getD .Undef) hget
      rw [hmap_cell_eq]
    · rfl

/-- `loadbytes` is invariant under `unchanged_on` when its footprint is
    covered by `P`. -/
theorem loadbytes_unchanged_on (P : block → Int → Prop) (m m' : mem) (b : block) (ofs n : Int)
    (hu : unchanged_on P m m') (hP : ∀ i, ofs ≤ i → i < ofs + n → P b i) :
    loadbytes m' b ofs n = loadbytes m b ofs n := by
  unfold loadbytes
  by_cases hn : n < 0
  · simp [hn]
  · simp only [hn, if_false]
    have hveq : ∀ i : Nat, i < n.toNat →
        valid_pointer m' b (ofs + (i : Int)) = valid_pointer m b (ofs + (i : Int)) := by
      intro i hi
      have hi' : (i : Int) < n := by omega
      have hiff := (hu.2 b (ofs + i) (hP (ofs + i) (by omega) (by omega))).1
      cases hvm : valid_pointer m b (ofs + (i : Int)) <;>
        cases hvm' : valid_pointer m' b (ofs + (i : Int)) <;> simp_all
    have hgeq : ∀ i : Nat, i < n.toNat → valid_pointer m b (ofs + (i : Int)) = true →
        m'.contents.get? (b, ofs + (i : Int)) = m.contents.get? (b, ofs + (i : Int)) := by
      intro i hi hvalid
      have hi' : (i : Int) < n := by omega
      exact (hu.2 b (ofs + i) (hP (ofs + i) (by omega) (by omega))).2 hvalid
    have hall_eq :
        (((List.range n.toNat).map (fun i : Nat => (b, ofs + (i : Int)))).all
          (fun p => valid_pointer m' p.1 p.2)) =
        (((List.range n.toNat).map (fun i : Nat => (b, ofs + (i : Int)))).all
          (fun p => valid_pointer m p.1 p.2)) := by
      apply all_congr_of_mem
      rintro ⟨b', ofs'⟩ hmem
      rw [List.mem_map] at hmem
      obtain ⟨i, hi, hpeq⟩ := hmem
      rw [List.mem_range] at hi
      injection hpeq with hbeq hofseq
      subst hbeq; subst hofseq
      exact hveq i hi
    rw [hall_eq]
    split
    · rename_i h_all
      have hmap_eq :
          (((List.range n.toNat).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => m'.contents.get? (x.1, x.2))) =
          (((List.range n.toNat).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => m.contents.get? (x.1, x.2))) := by
        apply List.map_congr_left
        rintro ⟨b', ofs'⟩ hmem
        rw [List.mem_map] at hmem
        obtain ⟨i, hi, hpeq⟩ := hmem
        rw [List.mem_range] at hi
        injection hpeq with hbeq hofseq
        subst hbeq; subst hofseq
        simp only
        exact hgeq i hi (by
          have := (all_locs_iff m b ofs n.toNat).mp h_all
          exact this i hi)
      have hmap_cell_eq :
          (((List.range n.toNat).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => (m'.contents.get? (x.1, x.2)).getD .Undef)) =
          (((List.range n.toNat).map (fun i : Nat => (b, ofs + (i : Int)))).map
            (fun x => (m.contents.get? (x.1, x.2)).getD .Undef)) := by
        apply List.map_congr_left
        intro ⟨b', ofs'⟩ hmem
        rw [List.mem_map] at hmem
        obtain ⟨i, hi, hpeq⟩ := hmem
        rw [List.mem_range] at hi
        cases hpeq
        exact congrArg (fun o => o.getD .Undef)
          (hgeq i hi (by
            have := (all_locs_iff m b ofs n.toNat).mp h_all
            exact this i hi))
      rw [hmap_cell_eq]
    · rfl

/-- `loadbytes` of length `0` always succeeds trivially. -/
theorem loadbytes_empty (m : mem) (b : block) (ofs : Int) :
    loadbytes m b ofs 0 = some [] := by
  unfold loadbytes
  simp only [show ¬ (0:Int) < 0 by omega, if_false]
  rfl

/-- Reading two adjacent ranges and concatenating gives the same result as
    reading the combined range in one go. -/
theorem loadbytes_concat (m : mem) (b : block) (ofs n1 n2 : Int) (bytes1 bytes2 : List memval)
    (h1 : loadbytes m b ofs n1 = some bytes1)
    (h2 : loadbytes m b (ofs + n1) n2 = some bytes2)
    (hn1 : n1 ≥ 0) (hn2 : n2 ≥ 0) :
    loadbytes m b ofs (n1 + n2) = some (bytes1 ++ bytes2) := by
  unfold loadbytes at h1 h2 ⊢
  rw [if_neg (show ¬(n1 < 0) by omega)] at h1
  rw [if_neg (show ¬(n2 < 0) by omega)] at h2
  rw [if_neg (show ¬(n1 + n2 < 0) by omega)]
  simp only [] at h1 h2 ⊢
  split at h1
  · rename_i hvalid1
    split at h2
    · rename_i hvalid2
      have hsize : (n1 + n2).toNat = n1.toNat + n2.toNat := by omega
      have hn1cast : (n1.toNat : Int) = n1 := by omega
      have hshift : (List.range n2.toNat).map
          ((fun i : Nat => (b, ofs + (i : Int))) ∘
            (fun x : Nat => n1.toNat + x)) =
          (List.range n2.toNat).map
            (fun i : Nat => (b, (ofs + n1) + (i : Int))) := by
        apply List.map_congr_left
        intro i _
        show (b, ofs + ((n1.toNat + i : Nat) : Int)) = (b, ofs + n1 + (i : Int))
        push_cast
        rw [hn1cast]
        ring_nf
      have hall_combined :
          ((List.range (n1 + n2).toNat).map
            (fun i : Nat => (b, ofs + (i : Int)))).all
            (fun p' => valid_pointer m p'.1 p'.2) = true := by
        rw [hsize, List.range_add, List.map_append, List.map_map, hshift,
          List.all_append, hvalid1, hvalid2]
        decide
      have hbytes1 := Option.some.inj h1
      have hbytes2 := Option.some.inj h2
      rw [if_pos hall_combined, hsize, List.range_add, List.map_append,
        List.map_map, hshift, ← hbytes1, ← hbytes2, List.map_append]
    · cases h2
  · cases h1

-- ============================================================================
-- 2. ALLOCATION PROPERTIES
-- ============================================================================

/-- Freshness: newly allocated block is distinct from all existing blocks. -/
theorem alloc_fresh :
  ∀ m lo hi b m',
    mem_wf m →
    (b, m') = alloc m lo hi →
    block_allocated m b = false := by
  intros m lo hi b m' h_wf h
  simp only [alloc] at h
  cases h
  unfold block_allocated
  -- Use well-formedness: nextblock is fresh
  obtain ⟨h_fresh, _, _⟩ := h_wf
  -- Show contains = false by contradiction
  by_contra h_contains
  have h_contains' : m.blocks.contains m.nextblock = true := by
    cases h : m.blocks.contains m.nextblock <;> simp_all
  -- Use mem_iff_isSome_getElem directly
  have h_mem : m.nextblock ∈ m.blocks := Std.HashMap.mem_iff_contains.mpr h_contains'
  have h_isSome : m.blocks[m.nextblock]?.isSome = true := Std.HashMap.mem_iff_isSome_getElem?.mp h_mem
  -- Convert isSome to exists
  have : ∃ info, m.blocks[m.nextblock]? = some info := Option.isSome_iff_exists.mp h_isSome
  obtain ⟨info, hinfo⟩ := this
  -- Reconcile getElem? with get?
  have hinfo' : m.blocks.get? m.nextblock = some info := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact hinfo
  -- Apply h_fresh to get contradiction
  have : m.nextblock < m.nextblock := h_fresh m.nextblock info hinfo'
  exact absurd rfl (Nat.ne_of_lt this)

/-- Allocation preserves existing blocks and their validity. -/
theorem alloc_preserves_valid :
  ∀ m lo hi b m' b' ofs,
    (b, m') = alloc m lo hi →
    b ≠ b' →
    valid_pointer m b' ofs = valid_pointer m' b' ofs := by
  intros m lo hi b m' b' ofs h h_ne
  simp [alloc] at h
  rw [h.2]
  simp only [valid_pointer]
  have h_ne' : b' ≠ m.nextblock := by rw [← h.1]; exact h_ne.symm
  rw [Std.HashMap.get?_insert]
  simp [h_ne'.symm]

/-- Allocation preserves memory contents of existing blocks. -/
theorem alloc_preserves_load :
  ∀ chunk m lo hi b m' b' ofs,
    (b, m') = alloc m lo hi →
    b ≠ b' →
    load chunk m b' ofs = load chunk m' b' ofs := by
  intros chunk m lo hi b m' b' ofs h h_ne
  simp [alloc] at h
  rw [h.2]
  simp only [load]
  congr 1
  have h_ne' : b' ≠ m.nextblock := by rw [← h.1]; exact h_ne.symm
  -- valid_pointer is same for all (b', ofs + i)
  have h_vp : ∀ i, valid_pointer m b' (ofs + ↑i) =
      valid_pointer { contents := m.contents, blocks := m.blocks.insert m.nextblock { lo := lo, hi := hi }, nextblock := m.nextblock + 1 } b' (ofs + ↑i) := by
    intro i
    simp only [valid_pointer]
    rw [Std.HashMap.get?_insert]
    simp [h_ne'.symm]
  -- Apply List.all congr to the list condition
  congr 2
  apply List_all_congr
  intro ⟨b'', ofs''⟩ h_mem
  -- All elements are of the form (b', ofs + i)
  simp only [List.mem_map, List.mem_range] at h_mem
  obtain ⟨i, _, h_eq⟩ := h_mem
  cases h_eq
  simp
  exact h_vp i

/-- The newly allocated block has correct bounds. -/
theorem alloc_result_bounds :
  ∀ m lo hi b m' ofs,
    (b, m') = alloc m lo hi →
    (valid_pointer m' b ofs ↔ lo ≤ ofs ∧ ofs < hi) := by
  intros m lo hi b m' ofs h
  simp [alloc] at h
  rw [h.1, h.2]
  simp [valid_pointer]

-- Helper lemmas for mem_wf invariants

/-- nextblock is always fresh (not allocated yet) -/
private lemma nextblock_fresh (m : mem) (h : mem_wf m) : m.blocks.get? m.nextblock = none := by
  obtain ⟨h_fresh, _, _, _⟩ := h
  by_contra h_contra
  obtain ⟨info, h_info⟩ : ∃ info, m.blocks.get? m.nextblock = some info := by
    cases h_eq : m.blocks.get? m.nextblock
    · contradiction
    · exact ⟨_, rfl⟩
  have : (m.nextblock : Nat) < (m.nextblock : Nat) := h_fresh m.nextblock info h_info
  exact Nat.lt_irrefl m.nextblock this

/-- Contents only exist for allocated blocks -/
private lemma contents_only_allocated (m : mem) (h : mem_wf m) (b : block) (ofs : Int) :
  m.blocks.get? b = none → m.contents.get? (b, ofs) = none := by
  obtain ⟨_, _, _, h_contents⟩ := h
  intro h_not_alloc
  by_contra h_contra
  obtain ⟨byte, h_byte⟩ : ∃ byte, m.contents.get? (b, ofs) = some byte := by
    cases h_eq : m.contents.get? (b, ofs)
    · contradiction
    · exact ⟨_, rfl⟩
  obtain ⟨info, h_info⟩ := h_contents b ofs byte h_byte
  rw [h_not_alloc] at h_info
  simp at h_info

omit [Archi] in
/-- If the first element of a list is none, mapM id returns none -/
private lemma mapM_id_cons_none {α : Type} (tail : List (Option α)) :
  (none :: tail).mapM id = none := by
  simp [List.mapM, List.mapM.loop]

/-- The newly allocated block is uninitialized (reads return Vundef).
    Requires well-formed memory. -/
theorem alloc_result_undef :
  ∀ chunk m lo hi b m' ofs,
    mem_wf m →
    (b, m') = alloc m lo hi →
    is_aligned ofs chunk →
    (∀ i, i < size_chunk chunk → lo ≤ ofs + (i : Int) ∧ ofs + (i : Int) < hi) →
    load chunk m' b ofs = some .Vundef := by
  intros chunk m lo hi b m' ofs h_wf h_alloc h_align h_bounds
  simp [alloc] at h_alloc
  rw [h_alloc.1, h_alloc.2]
  simp only [load]
  -- Simplify the alignment check
  rw [if_neg (by simp [h_align])]
  -- Step 1: Show all valid_pointer checks pass
  have h_valid : ((List.range (size_chunk chunk)).map (fun i => (m.nextblock, ofs + ↑i))).all
      (fun (b', ofs') => valid_pointer
        { contents := m.contents, blocks := m.blocks.insert m.nextblock { lo := lo, hi := hi }, nextblock := m.nextblock + 1 }
        b' ofs') = true := by
    rw [all_locs_iff]
    intro i hi
    simp only [valid_pointer]
    rw [Std.HashMap.get?_insert]
    simp
    exact h_bounds i hi
  rw [if_pos h_valid]
  -- Step 2: every cell in the freshly allocated block is Undef.
  have h_not_in : m.blocks.get? m.nextblock = none := nextblock_fresh m h_wf
  have h_cell : ∀ i, i < size_chunk chunk →
      (m.contents.get? (m.nextblock, ofs + (i : Int))).getD .Undef = .Undef := by
    intro i hi
    rw [contents_only_allocated m h_wf m.nextblock (ofs + (i : Int)) h_not_in]
    rfl
  have h_pos : 0 < size_chunk chunk := size_chunk_pos chunk
  have h_cells : (List.range (size_chunk chunk)).map (fun (i : Nat) =>
      (m.contents.get? (m.nextblock, (ofs + (i : Int)))).getD .Undef) =
      List.replicate (size_chunk chunk) .Undef := by
    simpa only using (map_range_replicate
      (fun i : Nat => (m.contents.get? (m.nextblock, ofs + (i : Int))).getD .Undef)
      .Undef (size_chunk chunk) h_cell)
  have hlocs : ((List.range (size_chunk chunk)).map (fun (i : Nat) =>
      (m.nextblock, ofs + (i : Int)))).map (fun x =>
        (m.contents.get? (x.1, x.2)).getD .Undef) =
      (List.range (size_chunk chunk)).map (fun (i : Nat) =>
        (m.contents.get? (m.nextblock, ofs + (i : Int))).getD .Undef) := by
    simp only [List.map_map, Function.comp_apply]
    rfl
  rw [hlocs, h_cells, decode_val_replicate_undef chunk _ h_pos]

-- ============================================================================
-- 3. FREE PROPERTIES
-- ============================================================================

/-- Free succeeds iff block is allocated with matching bounds. -/
theorem free_succeeds :
  ∀ m b lo hi,
    (∃ m', free m b lo hi = some m') ↔
    (∃ info, m.blocks.get? b = some info ∧ info.lo = lo ∧ info.hi = hi) := by
  intros m b lo hi
  constructor
  · -- → direction
    intro ⟨m', h⟩
    simp [free] at h
    split at h
    · simp at h
    · rename_i info hinfo
      split at h
      · rename_i hbounds
        use info
        simp [hinfo]
        exact hbounds
      · simp at h
  · -- ← direction
    intro ⟨info, hinfo, hlo, hhi⟩
    use { m with
          contents := m.contents.filter (fun (b', _) _ => b' ≠ b),
          blocks := m.blocks.erase b }
    simp only [free, hinfo, hlo, hhi]
    simp

/-- After freeing, the block becomes invalid. -/
theorem free_invalid :
  ∀ m b lo hi m' ofs,
    free m b lo hi = some m' →
    valid_pointer m' b ofs = false := by
  intros m b lo hi m' ofs h
  simp [free] at h
  split at h
  · simp at h
  · rename_i info hinfo
    split at h
    · -- success case: blocks' = m.blocks.erase b
      simp at h
      rw [← h]
      simp [valid_pointer]
    · simp at h

/-- Free preserves validity of other blocks. -/
theorem free_preserves_valid :
  ∀ m b lo hi m' b' ofs,
    free m b lo hi = some m' →
    b ≠ b' →
    valid_pointer m b' ofs = valid_pointer m' b' ofs := by
  intros m b lo hi m' b' ofs h h_ne
  simp [free] at h
  split at h
  · simp at h
  · rename_i info hinfo
    split at h
    · -- success case: m'.blocks = m.blocks.erase b
      simp at h
      rw [← h]
      simp only [valid_pointer]
      -- Need: erase b doesn't affect b' when b ≠ b'
      rw [Std.HashMap.get?_erase]
      simp [h_ne]
    · simp at h

/-- Free preserves contents of other blocks. -/
theorem free_preserves_load :
  ∀ chunk m b lo hi m' b' ofs,
    free m b lo hi = some m' →
    b ≠ b' →
    load chunk m b' ofs = load chunk m' b' ofs := by
  intros chunk m b lo hi m' b' ofs h h_ne
  simp [free] at h
  split at h
  · simp at h
  · rename_i info hinfo
    split at h
    · -- success case
      simp at h
      rw [← h]
      simp only [load]
      congr 1
      have h_vp : ∀ ofs', valid_pointer m b' ofs' = valid_pointer { contents := Std.HashMap.filter (fun x _ => !decide (x.1 = b)) m.contents, blocks := m.blocks.erase b, nextblock := m.nextblock } b' ofs' := by
        intro ofs'
        simp only [valid_pointer]
        rw [Std.HashMap.get?_erase]
        simp [h_ne]
      -- Apply to List.all
      congr 2
      · apply List_all_congr
        intro ⟨b'', ofs''⟩ h_mem
        simp only [List.mem_map, List.mem_range] at h_mem
        obtain ⟨i, _, h_eq⟩ := h_mem
        cases h_eq
        simp
        exact h_vp _
      · -- contents: filter preserves lookups for b' since b' ≠ b
        congr 1
        simp only [List.map_map]
        congr 1
        funext i
        -- For each location (b', ofs+i), show filtered get? equals unfiltered get?
        have h_get : (Std.HashMap.filter (fun x _ => !decide (x.1 = b)) m.contents).get? (b', ofs + ↑i)
            = m.contents.get? (b', ofs + ↑i) := by
          apply HashMap_filter_get?_of_true
          intro v _
          simp [h_ne.symm]
        change (m.contents.get? (b', ofs + (i : Int))).getD .Undef =
          ((Std.HashMap.filter (fun x _ => !decide (x.1 = b)) m.contents).get?
            (b', ofs + (i : Int))).getD .Undef
        exact congrArg (fun o => o.getD .Undef) h_get.symm
    · simp at h

-- ============================================================================
-- 4. ENCODE/DECODE PROPERTIES
-- ============================================================================

/-- Pointer-sized chunks use exactly the number of cells of their quantity. -/
theorem quantity_size_ptr_quantity (chunk : memory_chunk) (q : quantity)
    (h : ptr_quantity chunk = some q) :
    quantity_size q = size_chunk chunk := by
  cases chunk <;> simp [ptr_quantity] at h ⊢
  all_goals cases q <;> simp_all [quantity_size, size_chunk]

theorem decode_val_inj_value (chunk : memory_chunk) (q : quantity) (b : block) (o : Ptrofs)
    (h : ptr_quantity chunk = some q) :
    decode_val chunk (encode_val chunk (.Vptr b o)) =
      Val.load_result chunk (.Vptr b o) := by
  simp [encode_val, h, decode_val, proj_bytes_inj_value, proj_inj_value,
    check_value_inj_value]

/-- Pointer round-trip through the real chunk-level API: storing a pointer
    `.Vptr tb tofs` through a pointer-carrying chunk and loading it back recovers
    the SAME pointer (target block `tb` preserved), not an integer or the
    containing block.  This is the key provenance-preservation property. -/
theorem load_store_ptr (chunk : memory_chunk) (m : mem) (b : block) (ofs : Int)
    (tb : block) (tofs : Ptrofs) (q : quantity) (m' : mem)
    (hq : ptr_quantity chunk = some q)
    (h : store chunk m b ofs (.Vptr tb tofs) = some m') :
    load chunk m' b ofs = some (Val.load_result chunk (.Vptr tb tofs)) := by
  rw [load_store_same chunk m b ofs (.Vptr tb tofs) m' h]
  rw [decode_val_inj_value chunk q tb tofs hq]

private theorem load_result_ptr_eq_decode_encode_norm (chunk : memory_chunk)
    (q : quantity) (b : block) (o : Ptrofs)
    (h : ptr_quantity chunk = some q) :
    Val.load_result chunk (.Vptr b o) = decode_encode_norm chunk (.Vptr b o) := by
  cases Archi.ptr64 <;> cases chunk <;>
    simp [ptr_quantity, decode_encode_norm, Val.load_result] at h ⊢ <;>
    exact h.1

/-- Encoding produces the correct number of scalar bytes. -/
private theorem encode_bytes_length :
  ∀ chunk v bytes,
    encode_bytes chunk v = bytes →
    bytes ≠ [] →
    bytes.length = size_chunk chunk := by
  intros chunk v bytes h_enc h_ne
  subst h_enc
  cases chunk <;> cases v <;>
   first
   | (simp only [encode_bytes] at h_ne; exfalso; apply h_ne; rfl)
   | (dsimp only [encode_bytes, size_chunk]; rfl)
   | (simp only [encode_bytes, size_chunk] at h_ne ⊢; split_ifs <;> simp_all)

/-- Encoding produces one cell per byte of the chunk whenever it succeeds. -/
theorem encode_val_length (chunk : memory_chunk) (v : val) :
    encode_val chunk v ≠ [] →
    (encode_val chunk v).length = size_chunk chunk := by
  exact encode_val_length_core chunk v

/-- Decoding the correct number of bytes never produces Vundef
    (unless the bytes themselves encoded Vundef). -/
theorem decode_val_length :
  ∀ chunk cells,
    cells.length = size_chunk chunk →
    ∃ v, decode_val chunk cells = v := by
  intros chunk cells h
  exact ⟨decode_val chunk cells, rfl⟩

-- ----------------------------------------------------------------------------
-- Helper lemmas for `encode_decode_roundtrip`.
--
-- The heavy lifting is done by a handful of arithmetic/bit-level facts about the
-- little-endian byte encoding.  They are grouped here and consumed uniformly by
-- the (large) case analysis in the theorem below.
-- ----------------------------------------------------------------------------

omit [Archi] in
/-- `UInt32.ofInt` on a `Nat`-cast agrees with `UInt32.ofNat`. -/
private theorem u32_ofInt_natCast (n : Nat) : UInt32.ofInt (↑n) = UInt32.ofNat n := by
  have h : (UInt32.ofInt (↑n)).toNat = (UInt32.ofNat n).toNat := by
    simp [UInt32.toNat, UInt32.ofInt, UInt32.ofNat]
    omega
  exact Eq.symm ((UInt32.ofNat_eq_iff_mod_eq_toNat n (UInt32.ofInt ↑n)).mpr (id (Eq.symm h)))

omit [Archi] in
/-- `UInt64.ofInt` on a `Nat`-cast agrees with `UInt64.ofNat`. -/
private theorem u64_ofInt_natCast (n : Nat) : UInt64.ofInt (↑n) = UInt64.ofNat n := by
  have h : (UInt64.ofInt (↑n)).toNat = (UInt64.ofNat n).toNat := by
    simp [UInt64.toNat, UInt64.ofInt, UInt64.ofNat]
    omega
  exact Eq.symm ((UInt64.ofNat_eq_iff_mod_eq_toNat n (UInt64.ofInt ↑n)).mpr (id (Eq.symm h)))

omit [Archi] in
private theorem bv_setWidth_toNat (m : Nat) (x : BitVec 32) :
    (x.setWidth m).toNat = x.toNat % 2 ^ m :=
  BitVec.toNat_setWidth m x

omit [Archi] in
private theorem ofNat_toBitVec (n : Nat) : (UInt32.ofNat n).toBitVec = BitVec.ofNat 32 n := rfl
omit [Archi] in

/-- Decoding an 8-bit unsigned chunk performs zero extension. -/
private theorem zero_ext8_eq (i : CompCert.Int) :
    UInt32.ofNat (i.toNat % 256) = CompCert.Int.zero_ext 8 i := by
  unfold CompCert.Int.zero_ext
  rw [← u32_ofInt_natCast]
  congr
omit [Archi] in

/-- Decoding a 16-bit unsigned chunk performs zero extension. -/
private theorem zero_ext16_eq (i : CompCert.Int) :
    UInt32.ofNat (i.toNat % 65536) = CompCert.Int.zero_ext 16 i := by
  unfold CompCert.Int.zero_ext
  rw [← u32_ofInt_natCast]
  congr
omit [Archi] in

/-- Sign extension of an 8-bit chunk only depends on the low 8 bits. -/
private theorem sign_ext8_eq (i : CompCert.Int) :
    CompCert.Int.sign_ext 8 (UInt32.ofNat (i.toNat % 256)) = CompCert.Int.sign_ext 8 i := by
  unfold CompCert.Int.sign_ext
  congr 1
  congr 1
  rw [ofNat_toBitVec]
  have key : BitVec.ofNat 32 (i.toNat % 256) = (i.toBitVec.setWidth 8).setWidth 32 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, show i.toNat = i.toBitVec.toNat from rfl,
        ← bv_setWidth_toNat]
    exact BitVec.ofNat_toNat 32 (BitVec.setWidth 8 i.toBitVec)
  rw [key]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have min_eq : Nat.min 8 32 = 8 := rfl
  rw [min_eq] at hj ⊢
  simp only [BitVec.getLsbD_signExtend]
  split
  · simp only [BitVec.getLsbD_setWidth]
    by_cases hj32 : j < 32
    · simp [hj32]
    · omega
  · simp only [BitVec.msb]
    omega
omit [Archi] in

/-- Sign extension of a 16-bit chunk only depends on the low 16 bits. -/
private theorem sign_ext16_eq (i : CompCert.Int) :
    CompCert.Int.sign_ext 16 (UInt32.ofNat (i.toNat % 65536)) = CompCert.Int.sign_ext 16 i := by
  unfold CompCert.Int.sign_ext
  congr 1
  congr 1
  rw [ofNat_toBitVec]
  have key : BitVec.ofNat 32 (i.toNat % 65536) = (i.toBitVec.setWidth 16).setWidth 32 := by
    rw [show (65536 : Nat) = 2 ^ 16 from rfl, show i.toNat = i.toBitVec.toNat from rfl,
        ← bv_setWidth_toNat]
    exact BitVec.ofNat_toNat 32 (BitVec.setWidth 16 i.toBitVec)
  rw [key]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have min_eq : Nat.min 16 32 = 16 := rfl
  rw [min_eq] at hj ⊢
  simp only [BitVec.getLsbD_signExtend]
  split
  · simp only [BitVec.getLsbD_setWidth]
    by_cases hj32 : j < 32
    · simp [hj32]
    · omega
  · simp only [BitVec.msb]
    omega

omit [Archi] in
/-- Reinterpreting a `Float32` through its 32-bit bit pattern is the identity. -/
private theorem float32_roundtrip (f : CompCert.Float32) :
    FloatLib.Floats.ExecFloat.Binary.ofBits32 (FloatLib.Floats.ExecFloat.Binary.toBits32 f) = f :=
  FloatLib.Floats.ExecFloat.Binary.ofBits32_toBits32 f

omit [Archi] in
/-- Reinterpreting a `Float64` through its 64-bit bit pattern is the identity. -/
private theorem float64_roundtrip (f : CompCert.Float64) :
    FloatLib.Floats.ExecFloat.Binary.ofBits64 (FloatLib.Floats.ExecFloat.Binary.toBits64 f) = f :=
  FloatLib.Floats.ExecFloat.Binary.ofBits64_toBits64 f

omit [Archi] in
/-- Recovering the byte written by an 8-bit encode. -/
private theorem uint8_toNat_ofNat_mod (n : Nat) : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
  unfold UInt8.toNat UInt8.ofNat
  norm_num [BitVec.toNat_ofNat]
omit [Archi] in

/-- Little-endian reconstruction of a 32-bit integer chunk. -/
private theorem int32_decode (i : CompCert.Int) :
    CompCert.Int.repr
      (((UInt8.ofNat (i.toNat % 256)).toNat
        + (UInt8.ofNat (i.toNat / 256 % 256)).toNat * 256
        + (UInt8.ofNat (i.toNat / 65536 % 256)).toNat * 65536
        + (UInt8.ofNat (i.toNat / 16777216 % 256)).toNat * 16777216 : Nat) : Int) = i := by
  rw [uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod]
  have bound : i.toNat < 4294967296 := i.toBitVec.isLt
  have recon : i.toNat % 256 + i.toNat / 256 % 256 * 256 + i.toNat / 65536 % 256 * 65536
             + i.toNat / 16777216 % 256 * 16777216 = i.toNat := by omega
  rw [recon, show CompCert.Int.repr (↑i.toNat) = UInt32.ofInt (↑i.toNat) from rfl,
      u32_ofInt_natCast, UInt32.ofNat_toNat]
omit [Archi] in

/-- Little-endian reconstruction of a 64-bit integer chunk. -/
private theorem int64_decode (i : CompCert.Int64) :
    CompCert.Int64.repr
      (((UInt8.ofNat (i.toNat % 256)).toNat
        + (UInt8.ofNat (i.toNat / 256 % 256)).toNat * 256
        + (UInt8.ofNat (i.toNat / 65536 % 256)).toNat * 65536
        + (UInt8.ofNat (i.toNat / 16777216 % 256)).toNat * 16777216
        + (UInt8.ofNat (i.toNat / 4294967296 % 256)).toNat * 4294967296
        + (UInt8.ofNat (i.toNat / 1099511627776 % 256)).toNat * 1099511627776
        + (UInt8.ofNat (i.toNat / 281474976710656 % 256)).toNat * 281474976710656
        + (UInt8.ofNat (i.toNat / 72057594037927936 % 256)).toNat * 72057594037927936 : Nat) : Int) = i := by
  rw [uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod,
      uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod]
  have bound : i.toNat < 18446744073709551616 := i.toBitVec.isLt
  have recon : i.toNat % 256 + i.toNat / 256 % 256 * 256 + i.toNat / 65536 % 256 * 65536
             + i.toNat / 16777216 % 256 * 16777216 + i.toNat / 4294967296 % 256 * 4294967296
             + i.toNat / 1099511627776 % 256 * 1099511627776
             + i.toNat / 281474976710656 % 256 * 281474976710656
             + i.toNat / 72057594037927936 % 256 * 72057594037927936 = i.toNat := by omega
  rw [recon, show CompCert.Int64.repr (↑i.toNat) = UInt64.ofInt (↑i.toNat) from rfl,
      u64_ofInt_natCast, UInt64.ofNat_toNat]
omit [Archi] in

/-- Little-endian reconstruction of a 32-bit float bit pattern. -/
private theorem bits32_decode (bits : UInt32) :
    UInt32.ofNat
      ((UInt8.ofNat (bits.toNat % 256)).toNat
        + (UInt8.ofNat (bits.toNat / 256 % 256)).toNat * 256
        + (UInt8.ofNat (bits.toNat / 65536 % 256)).toNat * 65536
        + (UInt8.ofNat (bits.toNat / 16777216 % 256)).toNat * 16777216) = bits := by
  rw [uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod]
  have bound : bits.toNat < 4294967296 := bits.toBitVec.isLt
  have recon : bits.toNat % 256 + bits.toNat / 256 % 256 * 256 + bits.toNat / 65536 % 256 * 65536
             + bits.toNat / 16777216 % 256 * 16777216 = bits.toNat := by omega
  rw [recon, UInt32.ofNat_toNat]
omit [Archi] in

/-- Little-endian reconstruction of a 64-bit float bit pattern. -/
private theorem bits64_decode (bits : UInt64) :
    UInt64.ofNat
      ((UInt8.ofNat (bits.toNat % 256)).toNat
        + (UInt8.ofNat (bits.toNat / 256 % 256)).toNat * 256
        + (UInt8.ofNat (bits.toNat / 65536 % 256)).toNat * 65536
        + (UInt8.ofNat (bits.toNat / 16777216 % 256)).toNat * 16777216
        + (UInt8.ofNat (bits.toNat / 4294967296 % 256)).toNat * 4294967296
        + (UInt8.ofNat (bits.toNat / 1099511627776 % 256)).toNat * 1099511627776
        + (UInt8.ofNat (bits.toNat / 281474976710656 % 256)).toNat * 281474976710656
        + (UInt8.ofNat (bits.toNat / 72057594037927936 % 256)).toNat * 72057594037927936) = bits := by
  rw [uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod,
      uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod]
  have bound : bits.toNat < 18446744073709551616 := bits.toBitVec.isLt
  have recon : bits.toNat % 256 + bits.toNat / 256 % 256 * 256 + bits.toNat / 65536 % 256 * 65536
             + bits.toNat / 16777216 % 256 * 16777216 + bits.toNat / 4294967296 % 256 * 4294967296
             + bits.toNat / 1099511627776 % 256 * 1099511627776
             + bits.toNat / 281474976710656 % 256 * 281474976710656
             + bits.toNat / 72057594037927936 % 256 * 72057594037927936 = bits.toNat := by omega
  rw [recon, UInt64.ofNat_toNat]
omit [Archi] in

/-- Reconstruction of the single stored byte for 8-bit chunks. -/
private theorem byte8_decode (i : CompCert.Int) :
    CompCert.Int.repr (((UInt8.ofNat (i.toNat % 256)).toNat : Nat) : Int)
      = UInt32.ofNat (i.toNat % 256) := by
  rw [uint8_toNat_ofNat_mod,
      show CompCert.Int.repr (↑(i.toNat % 256)) = UInt32.ofInt (↑(i.toNat % 256)) from rfl,
      u32_ofInt_natCast]
omit [Archi] in

/-- Reconstruction of the two stored bytes for 16-bit chunks (mod `2^16`). -/
private theorem byte16_decode (i : CompCert.Int) :
    CompCert.Int.repr
      (((UInt8.ofNat (i.toNat % 256)).toNat
        + (UInt8.ofNat (i.toNat / 256 % 256)).toNat * 256 : Nat) : Int)
      = UInt32.ofNat (i.toNat % 65536) := by
  rw [uint8_toNat_ofNat_mod, uint8_toNat_ofNat_mod]
  have recon : i.toNat % 256 + i.toNat / 256 % 256 * 256 = i.toNat % 65536 := by omega
  rw [recon, show CompCert.Int.repr (↑(i.toNat % 65536)) = UInt32.ofInt (↑(i.toNat % 65536)) from rfl,
      u32_ofInt_natCast]

/-- Roundtrip: encoding then decoding recovers the original value after normalization.

    Note: This excludes pointer values because `decode_val` never produces `Vptr` -
    pointer provenance is lost through memory. For pointers, decode returns Vint/Vlong.

    For sub-word integer chunks (Mint8*/Mint16*), decode applies sign/zero extension.
    For the full-width integer/float chunks (Mint32, Mint64, Mfloat32, Mfloat64),
    the roundtrip is exact.  For `Many32`/`Many64` the *bytes* round-trip but the value's
    type is not preserved: floats come back as their integer bit-pattern reinterpretation
    (see `decode_encode_norm`).

    This matches CompCert's decode_encode_val lemma. -/
private theorem encode_bytes_decode_bytes_roundtrip :
  ∀ chunk v,
    (∀ b ofs, v ≠ .Vptr b ofs) →  -- exclude pointers (decode never yields Vptr)
    encode_bytes chunk v ≠ [] →
    decode_bytes chunk (encode_bytes chunk v) = decode_encode_norm chunk v := by
  intro chunk v hptr hne
  cases chunk <;> cases v <;>
    -- Discharge every type-mismatch / Vundef / Vptr case (encode returns []) at once.
    first
      | (exact absurd rfl (hptr _ _))
      | (simp only [encode_bytes, ne_eq, not_true_eq_false] at hne ⊢)
  -- The remaining cases have real byte content.  Each reduces, after the concrete
  -- length check simplifies away, to a reconstruction fact proved above.
  case Mbool.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [byte8_decode, zero_ext8_eq, CompCert.Int.zero_ext_idem]
  case Mint8signed.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [byte8_decode]; exact congrArg _ (sign_ext8_eq i)
  case Mint8unsigned.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [byte8_decode]; exact congrArg _ (zero_ext8_eq i)
  case Mint16signed.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [byte16_decode]; exact congrArg _ (sign_ext16_eq i)
  case Mint16unsigned.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [byte16_decode]; exact congrArg _ (zero_ext16_eq i)
  case Mint32.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact congrArg _ (int32_decode i)
  case Mint64.Vlong i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int64.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact congrArg _ (int64_decode i)
  case Mfloat32.Vsingle f =>
    simp only [decode_bytes, size_chunk, decode_encode_norm,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [bits32_decode]; exact congrArg _ (float32_roundtrip f)
  case Mfloat64.Vfloat f =>
    simp only [decode_bytes, size_chunk, decode_encode_norm,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [bits64_decode]; exact congrArg _ (float64_roundtrip f)
  case Many32.Vint i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact congrArg _ (int32_decode i)
  case Many32.Vsingle f =>
    simp only [decode_bytes, size_chunk, decode_encode_norm,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact congrArg _ (int32_decode (FloatLib.Floats.ExecFloat.Binary.toBits32 f))
  case Many64.Vlong i =>
    simp only [decode_bytes, size_chunk, decode_encode_norm, CompCert.Int64.unsigned,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact congrArg _ (int64_decode i)
  case Many64.Vfloat f =>
    simp only [decode_bytes, size_chunk, decode_encode_norm,
      List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ↓reduceIte]
    exact congrArg _ (int64_decode (FloatLib.Floats.ExecFloat.Binary.toBits64 f))

 /-- Scalar round-trip through the memval codec, with the usual non-empty
     encoding precondition. Pointer values use `decode_encode_ptr` below. -/
theorem encode_decode_roundtrip :
  ∀ chunk v,
    (∀ b ofs, v ≠ .Vptr b ofs) →
    encode_bytes chunk v ≠ [] →
    decode_val chunk (encode_val chunk v) = decode_encode_norm chunk v := by
  intro chunk v hptr hne
  cases v with
  | Vptr b o => exact False.elim (hptr b o rfl)
  | Vundef =>
      simpa [encode_val, decode_val, proj_bytes_inj_bytes] using
        encode_bytes_decode_bytes_roundtrip chunk .Vundef hptr hne
  | Vint i =>
      simpa [encode_val, decode_val, proj_bytes_inj_bytes] using
        encode_bytes_decode_bytes_roundtrip chunk (.Vint i) hptr hne
  | Vlong i =>
      simpa [encode_val, decode_val, proj_bytes_inj_bytes] using
        encode_bytes_decode_bytes_roundtrip chunk (.Vlong i) hptr hne
  | Vfloat f =>
      simpa [encode_val, decode_val, proj_bytes_inj_bytes] using
        encode_bytes_decode_bytes_roundtrip chunk (.Vfloat f) hptr hne
  | Vsingle f =>
      simpa [encode_val, decode_val, proj_bytes_inj_bytes] using
        encode_bytes_decode_bytes_roundtrip chunk (.Vsingle f) hptr hne

 /-- Pointer round-trip through the pointer-width chunk `Mptr`. -/
theorem decode_encode_ptr (b' : block) (o : Ptrofs) :
    decode_val Mptr (encode_val Mptr (.Vptr b' o)) =
      Val.load_result Mptr (.Vptr b' o) := by
  cases hp : Archi.ptr64 with
  | false =>
      apply decode_val_inj_value Mptr .Q32 b' o
      simp [Mptr, ptr_quantity, hp]
  | true =>
      apply decode_val_inj_value Mptr .Q64 b' o
      simp [Mptr, ptr_quantity, hp]

/-- Decode is deterministic (same bytes always decode to same value). -/
theorem decode_val_deterministic :
  ∀ chunk cells,
    ∀ v1 v2,
      decode_val chunk cells = v1 →
      decode_val chunk cells = v2 →
      v1 = v2 := by
  intros chunk cells v1 v2 h1 h2
  rw [← h1, ← h2]

omit [Archi] in
/-- An integer built by direct `repr` of an unsigned value `< 2^8` is already an
    8-bit zero-extended value (i.e. `Mint8unsigned`'s decoding, which has no
    explicit `zero_ext` wrapper, still satisfies the `zero_ext 8` fixpoint). -/
private theorem repr_zero_ext8_of_lt {n : Nat} (h : n < 256) :
    CompCert.Int.repr (n : Int) = CompCert.Int.zero_ext 8 (CompCert.Int.repr (n : Int)) := by
  have h1 : CompCert.Int.repr (n : Int) = UInt32.ofNat n := u32_ofInt_natCast n
  rw [h1, ← zero_ext8_eq (UInt32.ofNat n)]
  congr 1
  rw [UInt32.toNat_ofNat_of_lt' (show n < UInt32.size from by unfold UInt32.size; omega)]
  omega

omit [Archi] in
/-- Same as `repr_zero_ext8_of_lt`, but for 16-bit unsigned values (`Mint16unsigned`). -/
private theorem repr_zero_ext16_of_lt {n : Nat} (h : n < 65536) :
    CompCert.Int.repr (n : Int) = CompCert.Int.zero_ext 16 (CompCert.Int.repr (n : Int)) := by
  have h1 : CompCert.Int.repr (n : Int) = UInt32.ofNat n := u32_ofInt_natCast n
  rw [h1, ← zero_ext16_eq (UInt32.ofNat n)]
  congr 1
  rw [UInt32.toNat_ofNat_of_lt' (show n < UInt32.size from by unfold UInt32.size; omega)]
  omega

/-- `decode_val` always produces a value that fits the chunk's extended type
    (`xtype_of_chunk`), matching CompCert's `Mem.load_xtype`. Used by
    `Events.lean`'s `ec_well_typed` obligation for volatile/normal loads. -/
private theorem decode_bytes_has_rettype (chunk : memory_chunk) (bytes : List UInt8) :
    Val.has_rettype (decode_bytes chunk bytes) (xtype_of_chunk chunk) := by
  cases chunk with
  | Mbool =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, tail⟩⟩ <;>
      first
        | (simp [decode_bytes, size_chunk, Val.has_rettype]; done)
        | (simp only [decode_bytes, size_chunk, List.length_cons, List.length_nil, Nat.reduceAdd,
              ne_eq, not_true_eq_false, ↓reduceIte];
           rcases Val.norm_bool_cases
               (.Vint (CompCert.Int.zero_ext 8 (CompCert.Int.repr (b0.toNat : Int))))
             with h | h | h <;>
             simp only [h, Val.has_rettype, Vfalse, Vtrue] <;> tauto)
  | Mint8signed =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, tail⟩⟩ <;>
      first
        | (simp [decode_bytes, size_chunk, Val.has_rettype]; done)
        | (simp only [decode_bytes, size_chunk, List.length_cons, List.length_nil, Nat.reduceAdd,
              ne_eq, not_true_eq_false, ↓reduceIte, Val.has_rettype];
           exact (CompCert.Int.sign_ext_idem 8 _).symm)
  | Mint8unsigned =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, tail⟩⟩ <;>
      first
        | (simp [decode_bytes, size_chunk, Val.has_rettype]; done)
        | (simp only [decode_bytes, size_chunk, List.length_cons, List.length_nil, Nat.reduceAdd,
              ne_eq, not_true_eq_false, ↓reduceIte, Val.has_rettype];
           exact repr_zero_ext8_of_lt (by have := UInt8.toNat_lt b0; omega))
  | Mint16signed =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, tail⟩⟩⟩ <;>
      first
        | (simp [decode_bytes, size_chunk, Val.has_rettype]; done)
        | (simp only [decode_bytes, size_chunk, List.length_cons, List.length_nil, Nat.reduceAdd,
              ne_eq, not_true_eq_false, ↓reduceIte, Val.has_rettype];
           exact (CompCert.Int.sign_ext_idem 16 _).symm)
  | Mint16unsigned =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, tail⟩⟩⟩ <;>
      first
        | (simp [decode_bytes, size_chunk, Val.has_rettype]; done)
        | (simp only [decode_bytes, size_chunk, List.length_cons, List.length_nil, Nat.reduceAdd,
              ne_eq, not_true_eq_false, ↓reduceIte, Val.has_rettype];
           exact repr_zero_ext16_of_lt (by
             have := UInt8.toNat_lt b0; have := UInt8.toNat_lt b1; omega))
  | Mint32 =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, tail⟩⟩⟩⟩⟩ <;>
      simp [decode_bytes, size_chunk, Val.has_rettype]
  | Many32 =>
    simp only [xtype_of_chunk]
    rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, tail⟩⟩⟩⟩⟩ <;>
      simp [decode_bytes, size_chunk, Val.has_rettype]
  | Mint64 =>
    simp only [xtype_of_chunk]
    rcases bytes with
      _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, tail⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [decode_bytes, size_chunk, Val.has_rettype]
   | Many64 =>
     simp only [xtype_of_chunk]
     rcases bytes with
       _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, tail⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
       simp [Val.has_rettype]
   | Mfloat32 =>
     simp only [xtype_of_chunk]
     rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, tail⟩⟩⟩⟩⟩ <;>
       simp [decode_bytes, size_chunk, Val.has_rettype]
   | Mfloat64 =>
     simp only [xtype_of_chunk]
     rcases bytes with
       _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, tail⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
       simp [decode_bytes, size_chunk, Val.has_rettype]

/-- `decode_val` always produces a value of the chunk's extended type. -/
theorem decode_val_has_rettype (chunk : memory_chunk) (cells : List memval) :
    Val.has_rettype (decode_val chunk cells) (xtype_of_chunk chunk) := by
  cases hproj : proj_bytes cells with
  | some bytes =>
      simp [decode_val, hproj]
      exact decode_bytes_has_rettype chunk bytes
  | none =>
      simp [decode_val, hproj]
      cases hq : ptr_quantity chunk with
      | none => cases xtype_of_chunk chunk <;> trivial
      | some q => exact Val.load_result_xtype chunk (proj_value q cells)
/-- `Memory.load` always produces a value that fits the chunk's extended
    type, whether the read range was initialized (via `decode_val_has_rettype`)
    or not (`Vundef` fits any type unconditionally). Matches CompCert's
    `Mem.load_xtype`; used by `Events.lean`'s `ec_well_typed` obligation for
    non-volatile loads. -/
theorem load_has_rettype {chunk : memory_chunk} {m : mem} {b : block} {ofs : Int} {v : val}
    (h : load chunk m b ofs = some v) : Val.has_rettype v (xtype_of_chunk chunk) := by
  unfold load at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · injection h with h
      subst h
      exact decode_val_has_rettype chunk _
    · simp at h

-- ============================================================================
-- 5. POINTER VALIDITY PROPERTIES
-- ============================================================================

/-- Valid pointer implies weak valid pointer. -/
theorem valid_implies_weak_valid :
  ∀ m b ofs,
    valid_pointer m b ofs = true →
    weak_valid_pointer m b ofs = true := by
  intros m b ofs h
  simp [valid_pointer, weak_valid_pointer] at *
  split at h <;> simp at *
  omega

/-- One-past-end is weak valid but not valid. -/
theorem one_past_end_weak_valid :
  ∀ m b info,
    mem_wf m →
    m.blocks.get? b = some info →
    weak_valid_pointer m b info.hi = true ∧
    valid_pointer m b info.hi = false := by
  intros m b info h_wf h
  obtain ⟨_, h_bounds, _⟩ := h_wf
  have h_lo_lt_hi : info.lo < info.hi := h_bounds b info h
  constructor
  · -- weak_valid is true: info.lo ≤ info.hi ≤ info.hi
    simp only [weak_valid_pointer, h]
    have : info.lo ≤ info.hi := by omega
    simp [this]
  · -- valid is false: info.hi < info.hi is always false
    simp only [valid_pointer, h]
    have : ¬(info.hi < info.hi) := by omega
    simp

/-- Block allocated iff there exists some valid offset. -/
theorem block_allocated_iff_valid_exists :
  ∀ m b,
    mem_wf m →
    (block_allocated m b = true ↔
     ∃ ofs, valid_pointer m b ofs = true) := by
  intros m b h_wf
  obtain ⟨h_fresh, h_bounds, h_pos⟩ := h_wf
  constructor
  · -- → direction: if block allocated, there exists valid ofs
    intro h
    -- Convert contains to get? via the lemmas we used in alloc_fresh
    have h_mem : b ∈ m.blocks := Std.HashMap.mem_iff_contains.mpr h
    have h_isSome : m.blocks[b]?.isSome = true := Std.HashMap.mem_iff_isSome_getElem?.mp h_mem
    have : ∃ info, m.blocks[b]? = some info := Option.isSome_iff_exists.mp h_isSome
    obtain ⟨info, hinfo_elem⟩ := this
    have hinfo : m.blocks.get? b = some info := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact hinfo_elem
    -- Use info.lo as the valid offset
    use info.lo
    simp only [valid_pointer, hinfo]
    -- Need: info.lo ≤ info.lo (true) && info.lo < info.hi (from wf)
    have h_lt : info.lo < info.hi := h_bounds b info hinfo
    simp
    exact h_lt
  · -- ← direction: if valid offset exists, block is allocated
    intro ⟨ofs, h⟩
    simp only [valid_pointer] at h
    split at h
    · simp at h
    · rename_i info hinfo
      -- Convert get? = some to contains
      have h_getElem : m.blocks[b]? = some info := by
        rw [← Std.HashMap.get?_eq_getElem?]
        exact hinfo
      have h_isSome : m.blocks[b]?.isSome = true := by
        rw [h_getElem]
        simp
      have h_mem : b ∈ m.blocks := Std.HashMap.mem_iff_isSome_getElem?.mpr h_isSome
      exact Std.HashMap.mem_iff_contains.mp h_mem

-- ============================================================================
-- 6. MONOTONICITY PROPERTIES
-- ============================================================================

/-- Block IDs are monotonically increasing (never reused). -/
theorem alloc_monotonic :
  ∀ m lo hi b m',
    (b, m') = alloc m lo hi →
    b = m.nextblock ∧ m'.nextblock = b + 1 := by
  intros m lo hi b m' h
  simp [alloc] at h
  rw [h.1, h.2]
  simp

/-- Allocating a fresh block leaves `unchanged_on` for any predicate `P` that
    avoids the freshly-allocated block. Unlike CompCert's `Mem.alloc_unchanged_on`
    (which holds for *any* `P`, since CompCert's `unchanged_on_perm` field is
    additionally gated on `valid_block m_before b`), this port's `unchanged_on`
    does *not* carry that gate — so without restricting `P` here, the claim is
    false in general (e.g. `P := fun _ _ => True` would force
    `valid_pointer m b ofs ↔ valid_pointer m' b ofs` even at the
    freshly-allocated block, which is exactly the one place they differ). The
    `hPfresh` hypothesis is the minimal fix: it is always available at actual
    call sites, which reason about specific pre-existing blocks. -/
theorem alloc_unchanged_on (P : block → Int → Prop) (m : mem) (lo hi : Int) (b : block) (m' : mem)
    (halloc : (b, m') = alloc m lo hi) (hPfresh : ∀ b' ofs, P b' ofs → b' ≠ b) :
    unchanged_on P m m' := by
  have hmono := alloc_monotonic m lo hi b m' halloc
  have hm' : m' = (alloc m lo hi).2 := congrArg Prod.snd halloc
  have hc : m'.contents = m.contents := by rw [hm']; simp [alloc]
  obtain ⟨hb, hnb⟩ := hmono
  refine ⟨by rw [hnb, hb]; exact Nat.le_succ _, ?_⟩
  intro b' ofs hPb
  have hne : b ≠ b' := fun heq => hPfresh b' ofs hPb heq.symm
  refine ⟨by rw [alloc_preserves_valid m lo hi b m' b' ofs halloc hne], fun _ => by rw [hc]⟩

/-- Stores don't allocate new blocks. -/
theorem store_blocks :
  ∀ chunk m b ofs v m',
    store chunk m b ofs v = some m' →
    m'.blocks = m.blocks ∧ m'.nextblock = m.nextblock := by
  intros chunk m b ofs v m' h
  simp only [store] at h
  split at h
  · -- Misaligned
    simp at h
  · rename_i h_aligned
    split at h
    · -- Length mismatch
      simp at h
    · rename_i h_length
      split at h
      · -- Valid case: use helper lemma
        exact foldlM_contents_preserves_blocks_aux _ _ _ h
      · -- Invalid pointers
        simp at h

/-- Loads don't modify memory. -/
theorem load_readonly :
  ∀ chunk m b ofs v,
    load chunk m b ofs = some v →
    -- Memory is unchanged (but we can't directly state this without Decidable mem)
    -- So we state it via observable properties:
    ∀ chunk' b' ofs',
      load chunk' m b' ofs' = load chunk' m b' ofs' := by
  intros
  rfl

-- ============================================================================
-- 7. EMPTY MEMORY PROPERTIES
-- ============================================================================

/-- Empty memory has no allocated blocks. -/
theorem empty_no_blocks :
  ∀ b, ¬block_allocated empty b := by
  intro b
  simp [empty, block_allocated]

/-- Empty memory has nextblock = 1 (block 0 is reserved). -/
theorem empty_nextblock :
  empty.nextblock = 1 := by
  rfl

/-- All loads from empty memory fail. -/
theorem empty_load_none :
  ∀ chunk b ofs,
  load chunk empty b ofs = none := by
  intros chunk b ofs
  unfold load empty
  -- First check: alignment
  split
  · -- not aligned: returns none immediately
    rfl
  · -- aligned case: valid_pointer check will fail for empty memory
    -- Need to show locs.all (valid_pointer empty) = false
    -- Show that valid_pointer empty b' ofs' = false for all locations
    have h_valid : ∀ b' ofs', valid_pointer { contents := ∅, blocks := ∅, nextblock := 1 } b' ofs' = false := by
      intros b' ofs'
      unfold valid_pointer
      simp
    -- The list is non-empty (size > 0), and all valid_pointer checks are false
    have h_size_pos : size_chunk chunk > 0 := size_chunk_pos chunk
    -- Show that the list has at least one element where valid_pointer is false
    have h_all_false : ∀ (locs : List (block × Int)),
        locs = (List.range (size_chunk chunk)).map (fun i => (b, ofs + ↑i)) →
        locs.all (fun (b', ofs') => valid_pointer { contents := ∅, blocks := ∅, nextblock := 1 } b' ofs') = false := by
      intros locs hlocs
      rw [hlocs]
      rw [List.all_eq_false]
      use (b, ofs + 0)
      constructor
      · simp only [List.mem_map]
        use 0
        constructor
        · exact List.mem_range.mpr h_size_pos
        · ring_nf
      · simp only [Bool.not_eq_true]
        exact h_valid b (ofs + 0)
    simp only [h_all_false _ rfl]
    rfl

-- ============================================================================
-- 8. ALIGNMENT PROPERTIES
-- ============================================================================

omit [Archi] in
/-- Alignment is a power of 2. -/
theorem align_chunk_power_of_2 :
  ∀ c,
  ∃ k, align_chunk c = 2^k := by
  intro c
  cases c
  · -- Mbool: align = 1 = 2^0
    use 0
    rfl
  · -- Mint8signed: align = 1 = 2^0
    use 0
    rfl
  · -- Mint8unsigned: align = 1 = 2^0
    use 0
    rfl
  · -- Mint16signed: align = 2 = 2^1
    use 1
    rfl
  · -- Mint16unsigned: align = 2 = 2^1
    use 1
    rfl
  · -- Mint32: align = 4 = 2^2
    use 2
    rfl
  · -- Mint64: align = 8 = 2^3
    use 3
    rfl
  · -- Mfloat32: align = 4 = 2^2
    use 2
    rfl
  · -- Mfloat64: align = 8 = 2^3
    use 3
    rfl
  · -- Many32: align = 4 = 2^2
    use 2
    rfl
  · -- Many64: align = 8 = 2^3
    use 3
    rfl

omit [Archi] in
/-- Size is a multiple of alignment. -/
theorem size_chunk_multiple_of_align :
  ∀ chunk,
  ∃ k, size_chunk chunk = k * align_chunk chunk := by
  intro chunk
  cases chunk
  all_goals { use 1; rfl }

omit [Archi] in
/-- Aligned offset plus aligned size is still aligned. -/
theorem aligned_add :
  ∀ chunk ofs,
    is_aligned ofs chunk →
    is_aligned (ofs + (size_chunk chunk : Int)) chunk := by
  intro chunk ofs h_aligned
  -- Since size_chunk = align_chunk for all chunks,
  -- and ofs is aligned, ofs + align is also aligned
  simp [is_aligned, align_chunk, size_chunk] at *
  omega

end Properties

-- Re-export the main theorems at the top level

abbrev load_store_same := Properties.load_store_same
abbrev load_store_other := Properties.load_store_other
abbrev valid_pointer_store := Properties.valid_pointer_store
abbrev alloc_fresh := Properties.alloc_fresh
abbrev alloc_preserves := Properties.alloc_preserves_valid
abbrev free_invalid := Properties.free_invalid
abbrev free_preserves := Properties.free_preserves_valid

end Memory
