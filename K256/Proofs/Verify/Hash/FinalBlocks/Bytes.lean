import K256.Proofs.Verify.Hash.FinalBlocks.Memory
import K256.Proofs.Verify.Hash.Padding.Finalize
import K256.Proofs.Common.Encoding

namespace K256.Proofs.Verify.Hash.FinalBlocks

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine
  Standards.SECG.ECC.Encoding

private theorem stageByte (m : Ram) (sp high ret : Word) (dst : Readable m (sp+160) 64)
    (i : Nat) (hi : i < 64) :
    (stage m sp high ret)[BitVec.ofNat 64 ((sp+160).toNat+i)]? =
      some (if i < 56 then memByte m (sp+8+BitVec.ofNat 64 i) else storedByte high (i%8)) := by
  have present : Readable (stage m sp high ret) (sp+160) 64 := by
    unfold stage
    repeat' apply Readable.memStore
    exact dst
  have hj : i / 8 < 8 := by omega
  have rem : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have address (p : Word) : wordAddr p 64 (i/8) + BitVec.ofNat 64 (i%8) = p + BitVec.ofNat 64 i := by
    rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  have h := congrArg (fun x : Word => storedByte x (i%8)) (stage_word m sp high ret ⟨i/8,hj⟩)
  rw [storedByte_memLoad _ _ _ rem, address] at h
  have byte : memByte (stage m sp high ret) (sp+160+BitVec.ofNat 64 i) =
      if i < 56 then memByte m (sp+8+BitVec.ofNat 64 i) else storedByte high (i%8) := by
    by_cases isPrefix : i < 56
    · rw [ite_eq_right (by omega : i/8 ≠ 7), storedByte_memLoad _ _ _ rem, address] at h
      rwa [ite_eq_left isPrefix]
    · rw [ite_eq_left (by omega : i/8 = 7)] at h
      rwa [ite_eq_right isPrefix]
  rw [ofNat_toNat_add]
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (present.present i hi)
  rw [hv]
  simpa only [memByte, PhysicalMemory.read, hv, Option.getD_some] using congrArg some byte

private theorem sourceByte {m : Ram} {p : Word} {n : Nat} {bytes : ByteArray}
    (h : (⟨p.toNat,n⟩ : MemoryRegion).HasBytes m bytes) (i : Nat) (hi : i < bytes.size) :
    memByte m (p + BitVec.ofNat 64 i) = bytes[i] := by
  have byte := h.2 ⟨i,hi⟩
  change m[BitVec.ofNat 64 (p.toNat + i)]? = some bytes[i] at byte
  rw [ofNat_toNat_add] at byte
  simp only [memByte, PhysicalMemory.read, byte, Option.getD_some]

theorem stagedFirst (m : Ram) (sp ret : Word) (message : ByteArray)
    (source : (⟨(sp+8).toNat, 64⟩ : MemoryRegion).HasBytes m (paddedBuffer message))
    (dst : Readable m (sp+160) 64) :
    (⟨(sp+160).toNat,64⟩ : MemoryRegion).HasBytes
      (stage m sp (memLoad m (sp+64) 64) ret) (paddedBuffer message) := by
  refine ⟨source.1, fun i => ?_⟩
  have hi : i.val < 64 := (paddedBuffer_size message) ▸ i.isLt
  rw [stageByte _ _ _ _ dst _ hi]
  by_cases hp : i.val < 56
  · rw [ite_eq_left hp, sourceByte source i.val i.isLt]
  · rw [ite_eq_right hp, storedByte_memLoad _ _ _ (Nat.mod_lt _ (by decide)),
      show sp + 64 = sp + 8 + BitVec.ofNat 64 56 by bv_omega,
      BitVec.add_assoc (sp+8), ← BitVec.ofNat_add]
    change some (memByte m (sp+8 + BitVec.ofNat 64 (56+i.val%8))) = _
    rw [show 56+i.val%8 = i.val by omega, sourceByte source i.val i.isLt]

theorem shortPrefix (m : Ram) (sp : Word) (message : ByteArray)
    (short : message.size % 64 < 56)
    (source : (⟨(sp+8).toNat,64⟩ : MemoryRegion).HasBytes m (paddedBuffer message)) :
    (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes m (finalPrefix message) := by
  rw [← paddedBuffer_prefix message short]
  refine ⟨by rw [ByteArray.size_extract, paddedBuffer_size]; rfl, fun i => ?_⟩
  rw [ByteArray.getElem_extract]
  have h : i.val < (paddedBuffer message).size := Nat.zero_add i.val ▸ ByteArray.getElem_extract_aux i.isLt
  have eq : (0 + i.val : Nat) = i.val := Nat.zero_add _
  have byte := congrArg (fun j : Fin (paddedBuffer message).size => (paddedBuffer message)[j.val])
    (Fin.ext (a := ⟨0+i.val,ByteArray.getElem_extract_aux i.isLt⟩) (b := ⟨i.val,h⟩) eq)
  exact (source.2 ⟨i.val,h⟩).trans (congrArg some byte.symm)

theorem clearedPrefix (m : Ram) (sp : Word) (message : ByteArray)
    (long : ¬ message.size % 64 < 56) (src : Readable m (sp+8) 56) :
    (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes (clearPrefix m sp) (finalPrefix message) := by
  rw [finalPrefix, ite_eq_right long]
  refine ⟨Array.size_replicate, fun i => ?_⟩
  have hi : i.val < 56 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
  have present : Readable (clearPrefix m sp) (sp+8) 56 := by
    unfold clearPrefix
    repeat' apply Readable.memStore
    exact src
  have h := congrArg (fun x : Word => storedByte x (i.val%8))
    (clearPrefix_word m sp ⟨i.val/8, by omega⟩)
  rw [storedByte_memLoad _ _ _ (Nat.mod_lt _ (by decide)), wordAddr,
    BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod] at h
  have zero : storedByte (0 : Word) (i.val%8) = 0 := by
    change UInt8.ofNat (0 >>> (8 * (i.val%8))) = 0
    rw [Nat.zero_shiftRight]
    rfl
  rw [zero] at h
  change (clearPrefix m sp)[BitVec.ofNat 64 ((sp+8).toNat+i.val)]? = some ((Array.replicate 56 (0 : UInt8))[i.val]'(i.isLt))
  rw [ofNat_toNat_add, Array.getElem_replicate]
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (present.present i.val hi)
  rw [hv]
  simpa only [memByte, PhysicalMemory.read, hv, Option.getD_some] using congrArg some h

private theorem lengthByte (value i : Nat) (hi : i < 8) :
    storedByte (bswapSpec (BitVec.ofNat 64 value)) i = (natToOctets 8 value)[i]'(by
      rwa [Common.Encoding.natToOctets_size]) := by
  have byte := lane_ofLanes (n := 64) (w := 8) (fun j => lane 8 (BitVec.ofNat 64 value) (7-j)) i hi
  rw [storedByte_eq_extract]
  change UInt8.ofBitVec ((ofLanes 64 8 _).extractLsb' (8*i) 8) = _
  rw [show 8*i = i*8 by omega]
  change UInt8.ofBitVec (lane 8 (ofLanes 64 8 _) i) = _
  rw [byte]
  change UInt8.ofBitVec ((BitVec.ofNat 64 value).extractLsb' ((7-i)*8) 8) = _
  rw [show (7-i)*8 = 8*(7-i) by omega, ← storedByte_eq_extract]
  change storedByte (BitVec.ofNat 64 value) (7-i) = (natToOctets 8 value).data[i]'(by simpa only [ByteArray.size_data, Common.Encoding.natToOctets_size] using hi)
  rw [Common.Encoding.natToOctets_getElem _ _ _ hi]
  simp only [storedByte, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul, Nat.reducePow]
  change UInt8.ofNat (value % 18446744073709551616 / 256^(7-i)) =
    UInt8.ofNat (value / 256^(7-i) % 256)
  have power : 256 ^ (7-i) * 256 ∣ 18446744073709551616 := by
    rw [← Nat.pow_succ]
    exact Nat.pow_dvd_pow 256 (show 7-i+1 ≤ 8 by omega)
  rw [← UInt8.ofNat_mod_size (x := value % 18446744073709551616 / 256^(7-i))]
  congr 1
  change value % 18446744073709551616 / 256^(7-i) % 256 = value / 256^(7-i) % 256
  rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ power, Nat.mod_mul_right_div_self]

theorem stagedLast (m : Ram) (sp ret : Word) (message : ByteArray)
    (source : (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes m (finalPrefix message))
    (dst : Readable m (sp+160) 64) :
    let length := bswapSpec (BitVec.ofNat 64 (8*message.size))
    (⟨(sp+160).toNat,64⟩ : MemoryRegion).HasBytes
      (stage (memStore m (sp+64) length) sp length ret) (finalBlock message) := by
  dsimp only
  let length := bswapSpec (BitVec.ofNat 64 (8*message.size))
  have dst' := dst.memStore (sp+64) length
  have source' : (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes (memStore m (sp+64) length) (finalPrefix message) := by
    refine ⟨source.1, fun i => ?_⟩
    have apart : RangeApart (sp+64) 8 (sp+8) 56 := RangeApart.of_offsets rfl rfl (by decide)
    have sz : (finalPrefix message).size = 56 := source.1
    have hi : i.val < 56 := sz ▸ i.isLt
    change (memStore m (sp+64) length)[BitVec.ofNat 64 ((sp+8).toNat + i.val)]? = _
    rw [ofNat_toNat_add, memStore_getElem?_of_ne m (sp+64) length _ (fun j hj =>
      apart j hj i.val hi), ← ofNat_toNat_add]
    exact source.2 i
  refine ⟨finalBlock_size message, fun i => ?_⟩
  have hi : i.val < 64 := (finalBlock_size message) ▸ i.isLt
  rw [stageByte _ _ _ _ dst' _ hi]
  let suffix := natToOctets 8 (8*message.size)
  have iAppend : i.val < (finalPrefix message ++ suffix).size := i.isLt
  change some _ = some ((finalPrefix message ++ suffix)[i.val]'iAppend)
  have sz : (finalPrefix message).size = 56 := source.1
  by_cases hp : i.val < 56
  · have hleft : i.val < (finalPrefix message).size := by omega
    rw [ite_eq_left hp, sourceByte source' i.val hleft]
    exact congrArg some (ByteArray.getElem_append_left (h := iAppend) hleft).symm
  · have hright : (finalPrefix message).size ≤ i.val := by omega
    rw [ite_eq_right hp]
    refine congrArg some ((lengthByte _ _ (Nat.mod_lt _ (by decide))).trans ?_)
    refine Eq.trans ?_ (ByteArray.getElem_append_right (h := iAppend) hright).symm
    have idx : i.val % 8 = i.val - (finalPrefix message).size := by omega
    have j : i.val % 8 < suffix.size := by
      change i.val % 8 < (natToOctets 8 (8*message.size)).size
      rw [Common.Encoding.natToOctets_size]
      exact Nat.mod_lt _ (by decide)
    exact congrArg (fun j : Fin suffix.size => suffix[j.val])
      (Fin.ext (a := ⟨i.val % 8,j⟩) (b := ⟨i.val - (finalPrefix message).size,idx ▸ j⟩) idx)

end K256.Proofs.Verify.Hash.FinalBlocks
