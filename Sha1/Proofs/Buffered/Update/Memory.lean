import Sha1.Proofs.Buffered.Update.Contracts

namespace Sha1.Proofs.Buffered.Update

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hasBytes_extract {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes memory bytes) (start stop : Nat) :
    (⟨region.start + start, (bytes.extract start stop).size⟩ : MemoryRegion).HasBytes
      memory (bytes.extract start stop) := by
  refine ⟨rfl, ?_⟩
  intro i
  have hi : start + i.val < bytes.size := ByteArray.getElem_extract_aux i.isLt
  simpa only [Nat.add_assoc, ByteArray.getElem_extract] using h.2 ⟨start + i.val, hi⟩

theorem hasBytes_append {memory : Ram} {start : Nat} {a b : ByteArray}
    (ha : (⟨start, a.size⟩ : MemoryRegion).HasBytes memory a)
    (hb : (⟨start + a.size, b.size⟩ : MemoryRegion).HasBytes memory b) :
    (⟨start, (a ++ b).size⟩ : MemoryRegion).HasBytes memory (a ++ b) := by
  refine ⟨rfl, ?_⟩
  intro i
  by_cases hi : i.val < a.size
  · simpa only [ByteArray.getElem_append_left hi] using ha.2 ⟨i.val, hi⟩
  · have hj : i.val - a.size < b.size := by
      have : i.val < a.size + b.size := by simpa only [ByteArray.size_append] using i.isLt
      omega
    have he : start + a.size + (i.val - a.size) = start + i.val := by omega
    rw [ByteArray.getElem_append_right (by omega)]
    simpa only [he] using hb.2 ⟨i.val - a.size, hj⟩

theorem allocated_of_hasBytes {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes memory bytes) : region.Allocated memory := by
  intro address ha
  have hi : address.toNat - region.start < bytes.size := by
    have hs := h.1
    change bytes.size = region.size at hs
    rcases ha with ⟨_, _⟩
    omega
  refine ⟨bytes[address.toNat - region.start], ?_⟩
  have he : region.start + (address.toNat - region.start) = address.toNat :=
    Nat.add_sub_of_le ha.1
  simpa only [he, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.2 ⟨_, hi⟩

theorem allocated_of_agrees {s t : RamState} {changes : List Component} {region : MemoryRegion}
    (h : AgreesExcept changes s t) (ha : region.Allocated s.external) : region.Allocated t.external := by
  intro address hx
  exact Option.isSome_iff_exists.mp (h.grow address (Option.isSome_iff_exists.mpr (ha address hx)))

theorem hasBytes_of_copy {source destination : Ram} {src dst : BitVec 64} {bytes : ByteArray}
    (h : ∀ i < bytes.size, destination[dst + BitVec.ofNat 64 i]? =
      source[src + BitVec.ofNat 64 i]?)
    (hb : (⟨src.toNat, bytes.size⟩ : MemoryRegion).HasBytes source bytes) :
    (⟨dst.toNat, bytes.size⟩ : MemoryRegion).HasBytes destination bytes := by
  refine ⟨rfl, ?_⟩
  intro i
  have hb' := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb' ⊢
  exact (h i.val i.isLt).trans hb'

end Sha1.Proofs.Buffered.Update
