# Memory Model Design Document

## Overview

This document explains the design decisions behind `CLightLean/Memory.lean`, a simplified memory model for Clight semantics and program verification.

## Goals

1. **Executable**: Can run Clight programs for testing and symbolic execution
2. **Provable**: Simple enough to prove key correctness properties
3. **Faithful**: Matches Clight/C semantics (including uninitialized memory as `Vundef`)
4. **Iris-Compatible**: Uses block-based model that Iris separation logic expects

## Non-Goals

- **Compiler correctness**: We're not proving CompCert-style compiler passes preserve semantics
- **Optimization proofs**: We don't need to prove memory layout optimizations are sound
- **Performance**: Runtime efficiency is secondary to simplicity (though we use efficient data structures where easy)

---

## Design Decisions

### 1. Block Representation: `def block := Nat`

**Decision**: Use `Nat` directly for block identifiers.

**Rationale**:
- Simple and efficient
- Natural support for equality, hashing, ordering
- Monotonic allocation (nextblock always increases) is easy to reason about
- Block 0 reserved as "invalid" (never allocated)

**Alternatives Considered**:
- **Separate opaque type** (e.g., `structure block where id : Nat`): Rejected because it adds boilerplate without benefit. We don't need to enforce invariants on blocks themselves.
- **Finite set with reuse**: Rejected because reuse complicates proofs (need to track "block has been freed and not reallocated"). Monotonic allocation is simpler.

**CompCert Comparison**: CompCert uses `positive` (positive integers) in Coq. `Nat` in Lean serves the same purpose.

---

### 2. Memory Contents: sparse operational `memval` cells

**Decision**: `Memory.mem.contents` uses a sparse
`HashMap (block × Int) Memory.memval`. The operational design uses tagged
cells for provenance-preserving storage, for both the chunk API and the
byte-range (`loadbytes`/`storebytes`) API, matching CompCert.

**Rationale**:
- **Sparse representation**: Only stores non-`Undef` cells that have been written
- **Uninitialized = absent from map**: Reading an absent key is `memval.Undef`
  and an in-bounds typed read returns `Some Vundef`
- **Efficient for typical programs**: Most allocated memory is either fully initialized or has large uninitialized regions (no need to store millions of `Vundef` entries)
- **Simple invariant**: "If (b, ofs) is in contents, then block b must be allocated"

`memval` is `Undef | Byte UInt8 | Fragment val quantity Nat`. Pointer-width
stores write complete, indexed fragment sequences (`Q32` on x86-32 and `Q64`
on x86-64). Loads accept only complete homogeneous sequences; partial, mixed,
overwritten, or incompatible fragments decode to `Vundef`.

**Alternatives Considered**:
- **`HashMap block ByteArray`** (one array per block): 
  - Pros: More efficient for contiguous reads/writes
  - Cons: Requires tracking which bytes within each ByteArray are initialized (needs separate metadata)
  - Rejected: Premature optimization. Current design is simpler and "good enough" for now. Can optimize later if needed.
  
- **`HashMap (block × Int) (Option UInt8)`** (storing `None` for uninitialized):
  - Pros: Makes "uninitialized" explicit in the map
  - Cons: Wastes space (storing `None` entries), harder to reason about (need to filter out `None` entries)
  - Rejected: Sparse map is cleaner

- **Separate `initialized : HashSet (block × Int)`**:
  - Pros: Explicit tracking of initialization status
  - Cons: Redundant with sparse contents map
  - Rejected: "Absence from contents map" already means "uninitialized"

**CompCert Comparison**: CompCert uses `ZMap.t memval` per block. This model
uses a sparse keyed map but integrates the same tagged-cell idea in the actual
operational memory.

---

### 3. Permissions: Boolean "is allocated?"

**Decision**: No permission algebra. A block is either allocated (readable/writable) or not.

**Rationale**:
- **CompCert's permission algebra** (Freeable > Writable > Readable > Nonempty) is designed for **compiler correctness proofs**:
  - "This optimization preserves Freeable permission"
  - "Inlining preserves Readable permission"
  - "Dead code elimination doesn't increase permissions"
- **We don't need this** because:
  - We're not proving compiler passes correct
  - Iris separation logic will layer ownership/permissions on top (e.g., `l ↦ v` means "I own location l")
  - For executable semantics, "allocated = can read/write" is sufficient
- **Dramatic simplification**: Removes ~1000 lines of permission-tracking code from CompCert's Memory.v

**Alternatives Considered**:
- **Two-level permissions** (Readable/Writable):
  - Pros: Could model `const` data (readable but not writable)
  - Cons: Adds complexity, not essential for Clight (no `const` in core language)
  - Rejected: Can add later if needed, but YAGNI for now

**Iris Compatibility**: Iris's separation logic handles ownership at a higher level (logical state), so the physical memory model doesn't need permissions. Iris proves "if you have `l ↦ v` in your context, the physical memory has `v` at `l`" via adequacy theorem.

---

### 4. Alignment: Checked at Load/Store Time

**Decision**: `is_aligned ofs chunk` is checked when loading/storing, not stored in block metadata.

**Rationale**:
- **Simple**: No per-block alignment tracking
- **Sufficient**: Misaligned access returns `None` (error), which is correct for Clight
- **Flexible**: Different chunks can have different alignment requirements without complicating block allocation

**Alternatives Considered**:
- **Store alignment in `block_info`**:
  - Pros: Could enforce "block allocated at 8-byte boundary" statically
  - Cons: Complicates allocation, not needed (compiler ensures alignment)
  - Rejected: Runtime check is simpler and sufficient

**CompCert Comparison**: CompCert also checks alignment at load/store time (via `Mem.valid_access` predicate).

---

### 5. Bounds: `(lo, hi)` per Block

**Decision**: Store `(lo, hi)` bounds per allocated block, where `hi` is exclusive (i.e., valid offsets are `[lo, hi)`).

**Rationale**:
- **CompCert stores `(lo, hi, max)`**: The `max` field tracks "maximum permission bound" for compiler optimization proofs.
- **We only need `(lo, hi)`** for validity checks: "is this offset in bounds?"
- **Exclusive `hi`**: Matches C semantics where array of size `n` has valid indices `[0, n)` and one-past-end pointer `&arr[n]` is legal (but not dereferenceable).

**`weak_valid_pointer` vs `valid_pointer`**:
- `valid_pointer m b ofs`: `lo ≤ ofs < hi` (can dereference)
- `weak_valid_pointer m b ofs`: `lo ≤ ofs ≤ hi` (can have pointer, even if one-past-end)

This distinction is crucial for C semantics: `&arr[n]` is legal, `arr[n]` is not.

**Alternatives Considered**:
- **Inclusive `hi`**: Rejected because it's confusing (is `hi` valid or not?) and doesn't match array semantics.
- **Store size instead of `hi`**: Could store `size` and compute `hi = lo + size`. Rejected: no real benefit, and `(lo, hi)` is more direct.

**CompCert Comparison**: CompCert also uses `[lo, hi)` for bounds (though they call it `nextblock` at the per-block level).

---

### 6. Uninitialized Memory: Returns `Vundef`

**Decision**: Reading uninitialized memory (absent from `contents` map) returns `Some Vundef`, not `None`.

**Rationale**:
- **Faithfulness to C**: C doesn't crash on uninitialized reads; the value is "indeterminate" (undefined)
- **Clight semantics**: CompCert models this as `Vundef` (undefined value)
- **Operations propagate `Vundef`**: `Vundef + x = Vundef`, so uninitialized data "poisons" computations (can't depend on it)

**Distinction from Out-of-Bounds**:
- **Uninitialized in-bounds read**: `Some Vundef` (permitted, but value is undefined)
- **Out-of-bounds read**: `None` (hard error, program is stuck)

**Example**:
```c
int x;        // uninitialized
int y = x;    // y = Vundef (not a crash)
int z = y + 1; // z = Vundef (propagates)
```

**Alternatives Considered**:
- **Return `None` for uninitialized**: Rejected because it diverges from C semantics (real C programs don't crash on uninitialized reads).
- **Non-deterministic value**: Rejected because it complicates proofs (need to quantify over all possible values) and doesn't match CompCert.

**Iris Compatibility**: Iris's adequacy theorem will say "if you prove `{P} e {Q}` and `P` holds (including initialization invariants), then `e` never reads uninitialized memory" — but the physical semantics must still handle `Vundef` for completeness.

---

### 7. Byte-Level Representation and pointer provenance

**Decision**: Typed chunk operations store `memval` cells. Scalar values use
`Byte` cells containing the existing little-endian representation. Matching
pointer chunks use `Fragment` cells containing the complete original pointer.

**Rationale**:
- **Supports type-punning**: C allows reading a `float` as an `int` (via unions or pointer casts)
- **Memcpy/memmove**: `loadbytes : ... → Option (List memval)` and
  `storebytes : ... → List memval → ...` operate on `memval` cells (matching
  CompCert's `Mem.loadbytes`/`Mem.storebytes`), so a bytewise copy of a
  pointer-containing object preserves its `Fragment` cells — `memcpy` is
  provenance-preserving. `loadbytes` succeeds over any valid range (returning
  `.Undef` cells for uninitialized bytes), like CompCert.
- **Realistic**: Matches how real hardware works (memory is bytes, not typed values)

**Encoding/Decoding**:
- `encode_val chunk v : List memval` — scalars become `Byte` cells (little-endian,
  e.g. `Vint 42` → `[Byte 42, Byte 0, Byte 0, Byte 0]` for 32-bit); a `Vptr`
  through the pointer chunk becomes `Fragment` cells carrying the full pointer.
- `decode_val chunk cells : val` — an all-`Byte` run decodes via the scalar byte
  codec (`proj_bytes`/`decode_bytes`); a valid `Fragment` run reconstructs the
  original `Vptr` (`proj_value`); anything malformed/uninitialized → `Vundef`.
- The scalar byte layer (`encode_bytes`/`decode_bytes`, `List UInt8`) is retained
  underneath and is where the little-endian integer/float math lives.

**Provenance guarantee (proven)**: `Memory.Properties.load_store_ptr` shows that
storing `.Vptr tb tofs` through a pointer chunk and loading it back yields
`Val.load_result chunk (.Vptr tb tofs)` — i.e. the *target* block `tb` and offset
are preserved (not the containing block, not an integer). This is validated both
as a theorem and executably (`Test/MemoryPointerRoundtrip.lean`).

**Endianness**: Scalar bytes are hard-coded **little-endian** (x86/ARM). TODO: Support `Archi.big_endian`.

**Alternatives Considered**:
- **Store `val` directly**: Rejected because it doesn't support type-punning or byte-level operations.
- **Store abstract `memval` (like CompCert)**: This is the operational design,
  for both the chunk API (`load`/`store`) and the byte-range API
  (`loadbytes`/`storebytes`), fully matching CompCert.

**CompCert Comparison**: CompCert uses `memval` to preserve fragments and
provenance. This repository integrates that representation into operational
`Memory.mem`.

---

### 8. Property-proof backlog

**Decision**: Existing property declarations remain part of the compatibility
surface, with the operational design documented above. The migration adds no
`axiom`, `sorry`, or `admit`.

**Rationale**:
- **Unblock Cop/Clight development**: Higher-level semantics continue to use the
  established theorem surface while the representation migration proceeds
- **Prove later**: Remaining backlog is separate from the sound typed-cell
  adapter and requires additional proof work
- **Test executability first**: Want to run some programs and ensure the model works before investing in proofs

**Properties to Prove** (in `Memory/Properties.lean`):
1. **Load-after-store**: `store chunk m b ofs v = some m' → load chunk m' b ofs = some v`
2. **Non-interference**: Stores to different locations don't affect each other
3. **Valid pointer preservation**: Stores don't change which pointers are valid
4. **Allocation freshness**: Newly allocated block is distinct from all existing blocks
5. **Free invalidation**: Freed block becomes invalid

**Timeline**: Once Memory is being used by Cop/Clight, come back and prove these (~2-3 weeks of proof work).

---

## Comparison with CompCert

| Feature | CompCert Memory.v | Our Memory.lean | Rationale |
|---------|-------------------|-----------------|-----------|
| **Permissions** | 4-level algebra (Freeable/Writable/Readable/Nonempty) | Boolean (allocated or not) | Don't need compiler optimization proofs |
| **Max permissions** | Tracked per-block | Not tracked | Only needed for compiler proofs |
| **Memory injection** | Full theory (~500 lines) | Not included | Only needed for compiler correctness |
| **Memory extensions** | Full theory (~300 lines) | Not included | Only needed for compiler correctness |
| **Contents representation** | `ZMap.t memval` per block | `HashMap (block × Int) UInt8` | Simpler, sparse is efficient |
| **`memval` type** | `Byte | Fragment` (tracks multi-byte values) | Just `UInt8` | Simpler encoding/decoding |
| **Alignment** | Part of `valid_access` predicate | Checked in `load`/`store` | Same effect, simpler |
| **Total lines** | ~3000 (Memory.v + Memtype.v + Memdata.v) | ~600 (this file) | **5x smaller** |

---

## Future Optimizations (if needed)

### 1. ByteArray per Block
If profiling shows `HashMap (block × Int) UInt8` is too slow:
- Change to `HashMap block ByteArray`
- Track initialization separately (e.g., `HashMap block BitSet`)
- Pro: Faster bulk reads/writes
- Con: More complex, harder to prove

### 2. Block Reuse
If memory usage is a problem (e.g., long-running programs):
- Reuse freed block IDs
- Need to track "generation numbers" to avoid confusion
- Pro: Bounded memory usage
- Con: Much harder to prove (ABA problem)

### 3. Big-Endian Support
Currently assumes little-endian. To support big-endian:
- Check `Archi.big_endian` in `encode_val`/`decode_val`
- Reverse byte order for big-endian

### 4. Pointer Encoding (DONE)
The operational codec uses complete CompCert-style `Fragment` sequences tagged
with `Q32`/`Q64` (selected from `Archi.ptr64`) to preserve full pointer
provenance; malformed, partial, or incompatible sequences decode to `Vundef`.
See `Memory.Properties.load_store_ptr` and `Test/MemoryPointerRoundtrip.lean`.

---

## Testing Plan

Before proving properties, we should test executability:

1. **Unit tests**: Small examples of alloc/free/load/store
2. **Roundtrip tests**: Store value, load it back, check equality
3. **Clight programs**: Simple programs (factorial, sum array) that exercise memory
4. **Symbolic execution**: Run programs symbolically to check for crashes

Once tests pass, start proving properties.

---

## Open Questions / TODOs

1. **Pointer provenance**: DONE. `mem.contents` is `HashMap (block × Int) memval`
   and `load`/`store`/`loadv`/`storev` preserve full `Vptr` provenance through the
   `Fragment` codec. Proven (`load_store_ptr`) and validated executably
   (`Test/MemoryPointerRoundtrip.lean`, x86-64 and x86-32). The byte-range API
   (`loadbytes`/`storebytes`) is also `memval`-based, so `memcpy` and the
   global-initializer characterization preserve pointer provenance uniformly
   (including `Init_addrof`), matching CompCert.

2. **External functions**: How do we model `malloc`/`free` from libc?
   - **For now**: Model them as built-ins that call our `alloc`/`free`
   - **Future**: May need more sophisticated model for realistic programs

3. **Concurrency**: This model is single-threaded. For concurrent Clight:
   - Need memory model with atomic operations, fences, etc.
   - Iris will help here (Iris supports concurrency)
   - **Defer until single-threaded semantics are solid**

4. **Undefined behavior**: C has many forms of UB (signed overflow, use-after-free, etc.). How much do we model?
   - **For now**: Use-after-free returns `None` (stuck), signed overflow wraps (no UB), uninitialized reads return `Vundef`
   - **Future**: May want to track UB explicitly (e.g., "program has triggered UB" flag) for verification purposes

---

## Summary

This memory model is **dramatically simpler** than CompCert's (~600 lines vs ~3000 lines) because:
1. **No permissions** (Iris will handle ownership)
2. **No memory injection/extension** (not doing compiler correctness)
3. **Sparse representation** (only store initialized cells)
4. **Controlled migration**: raw bytes remain compatible, while typed pointers
   use a minimal `Fragment` representation

It is **sufficient for**:
- Executable Clight semantics
- Basic Hoare Logic
- Iris instantiation (adequacy theorem)
- Program verification (with separation logic)

It is **not sufficient for**:
- CompCert-style compiler correctness proofs
- Advanced optimizations (register allocation, instruction scheduling, etc.)
- Pointer-preserving `loadbytes`/`storebytes` until their API is migrated to
  `List memval`

**For our goals (Clight semantics + Iris verification), this is the right design.**
