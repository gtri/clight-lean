import CLightLean.Memory

/-! Operational pointer-provenance regression, proved via `load_store_ptr`.
    A pointer to block `target` is stored into a *different* containing block
    and loaded back through the real `Memory.store`/`Memory.load` API; the
    result is the SAME pointer (target block + offset preserved).  Under the old
    byte-only model this returned an integer / lost the block; the memval
    `Fragment` codec now preserves full provenance. -/

namespace X86_64
attribute [local instance] x86_64

/-- x86-64: storing `Vptr target ofs` into block `containing` and loading it
    back yields `Val.load_result Mptr (Vptr target ofs)` — i.e. the pointer
    itself, target block preserved (not the containing block, not an integer). -/
theorem ptr_roundtrip
    (m : Memory.mem) (containing target : block) (ofs : Int) (tofs : Ptrofs)
    (m' : Memory.mem)
    (h : Memory.store Mptr m containing ofs (.Vptr target tofs) = some m') :
    Memory.load Mptr m' containing ofs
      = some (Val.load_result Mptr (.Vptr target tofs)) :=
  Memory.Properties.load_store_ptr Mptr m containing ofs target tofs .Q64 m'
    (by simp [Memory.ptr_quantity, Mptr, show Archi.ptr64 = true from rfl]) h

end X86_64

namespace X86_32
attribute [local instance] x86_32

/-- x86-32: same provenance-preservation property with 32-bit pointers. -/
theorem ptr_roundtrip
    (m : Memory.mem) (containing target : block) (ofs : Int) (tofs : Ptrofs)
    (m' : Memory.mem)
    (h : Memory.store Mptr m containing ofs (.Vptr target tofs) = some m') :
    Memory.load Mptr m' containing ofs
      = some (Val.load_result Mptr (.Vptr target tofs)) :=
  Memory.Properties.load_store_ptr Mptr m containing ofs target tofs .Q32 m'
    (by simp [Memory.ptr_quantity, Mptr, show Archi.ptr64 = false from rfl]) h

end X86_32
