import K256.Proofs.Ecdh.Decode.Packing.Blocks

namespace K256.Proofs.Ecdh.Decode.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR

theorem packed_suffix_memory (img : StackImage) (sp src : BitVec 64) (m : Ram) (acc : BitVec 32)
    (h : ∀ a, img.memory sp src m a = img.memory sp src m 0) :
    (packedImage .original).memory sp 0 (img.memory sp src m 0) acc =
      (packedImage img).memory sp src m acc := by
  unfold packedImage
  simp only [StackImage.memory, h]

set_option maxRecDepth 4096 in
theorem compressed_suffix_memory (sp src : BitVec 64) (m : Ram) (acc : BitVec 32) :
    (packedImage .original).memory sp 0 (compressedImage.memory sp src m 0) acc =
      (packedImage compressedImage).memory sp src m acc :=
  packed_suffix_memory _ _ _ _ _ (fun _ => rfl)

theorem identity_suffix_memory (sp src : BitVec 64) (m : Ram) (acc : BitVec 32) :
    (packedImage .original).memory sp 0 (identityImage.memory sp src m 0) acc =
      (packedImage identityImage).memory sp src m acc :=
  packed_suffix_memory _ _ _ _ _ (fun _ => rfl)

private theorem compressed_origin :
    ∀ i < 65, (packedImage compressedImage).origin (72 + i) =
      if 7 ≤ i ∧ i < 11 then .accumulator (i - 7) else
      if i < 33 then .input i else .zero := by decide +kernel

private theorem identity_origin :
    ∀ i < 65, (packedImage identityImage).origin (72 + i) =
      if 7 ≤ i ∧ i < 11 then .accumulator (i - 7) else .zero := by decide +kernel

theorem compressed_bytes (sp src : BitVec 64) (m : Ram)
    (low : sp.toNat + 232 < 2^64) (apart : Outside [⟨sp.toNat, 232⟩] src 33)
    (i : Nat) (hi : i < 65) :
    memByte ((packedImage compressedImage).memory sp src m (memLoad m (src + 7) 32))
      (sp + BitVec.ofNat 64 (72 + i)) =
      if i < 33 then memByte m (src + BitVec.ofNat 64 i) else 0 := by
  rw [StackImage.byte_origin _ _ _ _ _ (by decide +kernel) low apart _ (by omega), compressed_origin i hi]
  split
  next h =>
    obtain ⟨lo, high⟩ := h
    simp only [StackImage.byte, ite_eq_left (show i < 33 by omega)]
    rw [storedByte_memLoad _ _ _ (by omega)]
    change memByte m (src + BitVec.ofNat 64 7 + BitVec.ofNat 64 (i - 7)) = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le lo]
  · split <;> rfl

theorem identity_bytes (sp src : BitVec 64) (m : Ram)
    (low : sp.toNat + 232 < 2^64) (apart : Outside [⟨sp.toNat, 232⟩] src 33)
    (i : Nat) (hi : i < 65) :
    memByte ((packedImage identityImage).memory sp src m 0)
      (sp + BitVec.ofNat 64 (72 + i)) = 0 := by
  rw [StackImage.byte_origin _ _ _ _ _ (by decide +kernel) low apart _ (by omega), identity_origin i hi]
  split
  · simp [StackImage.byte, storedByte]
  · rfl

theorem packedCall_byte {m : Ram} {sp : BitVec 64} {i : Nat} (hi : i < 65) :
    memByte (memStore m (sp - 8) (0x121177 : BitVec 64)) (sp + 72 + BitVec.ofNat 64 i) =
      memByte m (sp + BitVec.ofNat 64 (72 + i)) := by
  rw [BitVec.ofNat_add]
  change memByte (memStore m (sp - 8) (0x121177 : BitVec 64)) (sp + 72 + BitVec.ofNat 64 i) =
    memByte m (sp + ((72 : BitVec 64) + BitVec.ofNat 64 i))
  rw [← BitVec.add_assoc]
  have apart : RangeApart (sp - 8) 8 (sp + 72) 65 :=
    RangeApart.of_offsets (x := sp) (c := 0 - 8) (d := 72) (addr_sub _ _) rfl (by decide)
  change ((memStore m (sp - 8) (0x121177 : BitVec 64))[sp + 72 + BitVec.ofNat 64 i]?).getD 0 = _
  rw [memStore_getElem?_of_ne _ _ _ _ fun j hj => apart j hj i hi]
  rfl

theorem image_frame {code : CodeMap} {sp src : BitVec 64} {m : Ram}
    (win : Writable code m (sp - 8) 272) (img : StackImage) (acc : BitVec 32)
    (bound : img.endOffset ≤ 232) :
    RamWriteFrame m (img.memory sp src m acc) [window sp] := by
  have base : sp.toNat = (sp - 8).toNat + 8 := by
    have e := toNat_of_offsets (n := 232) (c := 0) (addr_self sp) (addr_sub sp 8)
      win.readable.low (by decide)
    exact e
  have low := win.readable.low
  apply (RamWriteFrame.refl _ _).trans (img.frame _ _ _ _ bound (by omega))
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, by simp only [window]; omega, by simp only [window]; omega⟩

theorem packedCall_frame {code : CodeMap} {sp src : BitVec 64} {m : Ram}
    (win : Writable code m (sp - 8) 272) (img : StackImage) (acc : BitVec 32)
    (bound : img.endOffset ≤ 232) :
    RamWriteFrame m (memStore (img.memory sp src m acc) (sp - 8) (0x121177 : BitVec 64))
      [window sp] :=
  (image_frame win img acc bound).memStore _
    (stackRange (off := 0 - 8) win (addr_sub _ _) (by decide))

theorem saved_after_packing {sp src : BitVec 64} {m : Ram} {img : StackImage}
    (winLow : (sp - 8).toNat + 272 ≤ 2^32) (bound : img.endOffset ≤ 232)
    (acc : BitVec 32) {off : BitVec 64} (far : 232 ≤ off.toNat ∧ off.toNat + 8 ≤ 264) :
    memLoad (memStore (img.memory sp src m acc) (sp - 8) (0x121177 : BitVec 64))
      (sp + off) 64 = memLoad m (sp + off) 64 := by
  have base : sp.toNat = (sp - 8).toNat + 8 :=
    toNat_of_offsets (n := 232) (c := 0) (addr_self sp) (addr_sub sp 8)
      winLow (by decide)
  have loc : (sp + off).toNat = sp.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have apart : RangeApart (sp - 8) 8 (sp + off) 8 :=
    RangeApart.of_toNat (by omega) (by omega) (Or.inl (by omega))
  rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart]
  apply (img.frame sp src m acc bound (by omega)).memLoad_eq
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  exact Or.inr (by change sp.toNat + 232 ≤ _; omega)

end K256.Proofs.Ecdh.Decode.Packing
