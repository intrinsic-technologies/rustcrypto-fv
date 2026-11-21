import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Message
import K256.Proofs.Signing.UpdateV.Finalize.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.Hash

theorem appendBytes {memory : Ram} {address : BitVec 64} {first second : ByteArray}
    (left : (MemoryRegion.mk address.toNat first.size).HasBytes memory first)
    (right : (MemoryRegion.mk (address + BitVec.ofNat 64 first.size).toNat second.size).HasBytes
      memory second) :
    (MemoryRegion.mk address.toNat (first ++ second).size).HasBytes memory (first ++ second) := by
  refine ⟨rfl, fun i => ?_⟩
  by_cases before : i.val < first.size
  · have h := left.2 ⟨i.val, before⟩
    simpa only [ByteArray.getElem_append_left before] using h
  · have after : i.val - first.size < second.size := by
      have bound : i.val < first.size + second.size := by
        simpa only [ByteArray.size_append] using i.isLt
      omega
    have h := right.2 ⟨i.val - first.size, after⟩
    change memory[BitVec.ofNat 64 ((address + BitVec.ofNat 64 first.size).toNat +
      (i.val - first.size))]? = some second[i.val - first.size] at h
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_sub_of_le (by omega : first.size ≤ i.val)] at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_append_right (by omega : first.size ≤ i.val)] using h

theorem appendShortAfter {m n : Ram} {p : BitVec 64} {key input extra : ByteArray}
    {rs : List MemoryRegion} (old : UpdateV.HmacStateAt m p key input)
    (frame : RamWriteFrame m n rs) (fits : input.size % 64 + extra.size < 64)
    (outer : Outside rs p 64) (buffer : Outside rs (p + 64) (input.size % 64))
    (hash : Outside rs (p + 128) 32) (count : Outside rs (p + 160) 8)
    (copied : (⟨(p + 64 + BitVec.ofNat 64 (input.size % 64)).toNat, extra.size⟩ : MemoryRegion).HasBytes n extra)
    (used : memLoad n (p + 127) 8 = BitVec.ofNat 8 (input.size % 64 + extra.size)) :
    UpdateV.HmacStateAt n p key (input ++ extra) := by
  let oldInput := UpdateV.keyPad key 0x36 ++ input
  have padded : oldInput.size = 64 + input.size := by rw [ByteArray.size_append, UpdateV.keyPad_size]
  have len : (remainderBytes oldInput).size = input.size % 64 := by rw [remainderBytes_size,padded]; omega
  have inside : oldInput.size % 64 + extra.size < 64 := by rw [padded]; omega
  have rem : (input ++ extra).size % 64 = input.size % 64 + extra.size := by rw [ByteArray.size_append]; omega
  have blocks : (input ++ extra).size / 64 = input.size / 64 := by rw [ByteArray.size_append]; omega
  have left := UpdateV.Finalize.bytesAfter frame buffer old.buffer
  have combined := appendBytes (first := remainderBytes oldInput) (second := extra)
    (by simpa only [len] using left) (by simpa only [len] using copied)
  have allSize : (remainderBytes oldInput ++ extra).size = (input ++ extra).size % 64 := by
    rw [ByteArray.size_append,len,rem]
  refine ⟨UpdateV.Finalize.bytesAfter frame outer old.outer, ?_, rem ▸ used, ?_, ?_⟩
  · rw [← ByteArray.append_assoc, remainderBytes_append_within _ _ inside]
    simpa only [allSize] using combined
  · rw [← ByteArray.append_assoc, compressBlocks_append_within _ _ _ inside]
    exact UpdateV.Finalize.stateAfter frame hash old.hash
  · rw [blocks]
    exact (frame.memLoad_eq count).trans old.count

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb
