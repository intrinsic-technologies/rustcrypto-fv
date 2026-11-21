import ChaCha20Poly1305.Proofs.MemoryRoutines.Memcpy
import ChaCha20Poly1305.Proofs.MemoryRoutines.Memset

namespace ChaCha20Poly1305.Proofs.MemoryContracts

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program

export ChaCha20Poly1305.Proofs.Common (WritableRange)
export ChaCha20Poly1305.Proofs.MemoryRoutines (rdx destination CallPre MemcpyPre MemsetPre
  callChanges CallResult MemcpyResult MemsetResult)

def memcpyEntry : BitVec 64 := 0x102dc0

def memcpyLength : Nat := 47

def memsetEntry : BitVec 64 := 0x102d70

def memsetLength : Nat := 69

def memcpySlot : BitVec 64 := 0x2013a8

def memsetSlot : BitVec 64 := 0x2013e0

theorem slot_read {s : RamState} (hc : CodeIn Extracted.programImage s) (offset : Nat)
    (hoff : offset + 8 ≤ Extracted.rodataBytes.size) (value : BitVec 64)
    (hbytes : ∀ i < 8, (Extracted.rodataBytes.toListFrom offset 8)[i]! = storedByte value i) :
    (Operand.mem (Extracted.rodataAddress + BitVec.ofNat 64 offset) : Operand 64).read s =
      value := by
  have hs := (hc.slice_of_section (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) offset 8 hoff).bytesAt
  change memLoad s.external _ 64 = value
  apply storedByte_injective (by decide)
  intro i hi
  rw [storedByte_memLoad _ _ _ hi, ← hbytes i hi]
  have hl : i < (Extracted.rodataBytes.toListFrom offset 8).length := by
    rw [chunked_toListFrom_length]; omega
  have he := hs i hl
  change (s.external[_]?).getD 0 = _
  rw [he, Option.getD_some]
  exact (getElem!_pos (Extracted.rodataBytes.toListFrom offset 8) i hl).symm

theorem memcpy_slot (s : RamState) (hc : CodeIn Extracted.programImage s) :
    (Operand.mem memcpySlot : Operand 64).read s = memcpyEntry :=
  slot_read hc 0x13a8 (by decide +kernel) memcpyEntry (by decide +kernel)

theorem memset_slot (s : RamState) (hc : CodeIn Extracted.programImage s) :
    (Operand.mem memsetSlot : Operand 64).read s = memsetEntry :=
  slot_read hc 0x13e0 (by decide +kernel) memsetEntry (by decide +kernel)

theorem memcpy_returns [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ MemcpyResult s t :=
  MemoryRoutines.memcpy_returns hstride s hr hc hp

theorem memcpy_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < memcpyEntry.toNat ∨
      memcpyEntry.toNat + memcpyLength ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ MemcpyResult s t :=
  MemoryRoutines.memcpy_advances hstride boundary hb s hr hc hp hne

theorem memset_returns [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemsetPre s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ MemsetResult s t :=
  MemoryRoutines.memset_returns hstride s hr hc hp

theorem memset_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < memsetEntry.toNat ∨
      memsetEntry.toNat + memsetLength ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemsetPre s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ MemsetResult s t :=
  MemoryRoutines.memset_advances hstride boundary hb s hr hc hp hne

end ChaCha20Poly1305.Proofs.MemoryContracts
