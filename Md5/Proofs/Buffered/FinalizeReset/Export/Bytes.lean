import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset.Export

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem bytes_of_read {s : RamState} {base : BitVec 64} {word : BitVec 64}
    (ha : ∀ i < 8, (s.external[base + BitVec.ofNat 64 i]?).isSome)
    (hr : (Operand.mem base : Operand 64).read s = word) :
    Bytes s.external base 8 (storedByte word) := by
  change memLoad s.external base 64 = word at hr
  have hb := Bytes.of_memLoad (n := 64) ha
  rwa [hr] at hb

theorem hasBytes_of_halves {s : RamState} {base : BitVec 64}
    {bytes : Vector UInt8 16} {lo hi : BitVec 64}
    (ha : ∀ i < 16, (s.external[base + BitVec.ofNat 64 i]?).isSome)
    (hlo : (Operand.mem base : Operand 64).read s = lo)
    (hhi : (Operand.mem (base + 8) : Operand 64).read s = hi)
    (blo : ∀ i : Fin 8, storedByte lo i.val = bytes[i.val])
    (bhi : ∀ i : Fin 8, storedByte hi i.val = bytes[8 + i.val]) :
    (⟨base.toNat, 16⟩ : MemoryRegion).HasBytes s.external ⟨bytes.toArray⟩ := by
  have hl := bytes_of_read (fun i hi ↦ ha i (by omega)) hlo
  have hh := bytes_of_read (fun i hi ↦ by
    have he : base + 8 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (8 + i) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
      rfl
    rw [he]
    exact ha (8 + i) (by omega)) hhi
  refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
  intro i
  have hi16 : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  change s.external[BitVec.ofNat 64 (base.toNat + i.val)]? = some bytes[i.val]
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases hi8 : i.val < 8
  · exact (hl i.val hi8).trans (congrArg some (blo ⟨i.val, hi8⟩))
  · have he : base + BitVec.ofNat 64 i.val = base + 8 + BitVec.ofNat 64 (i.val - 8) := by
      change base + BitVec.ofNat 64 i.val = base + BitVec.ofNat 64 8 + _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
    rw [he]
    have hb := bhi ⟨i.val - 8, by omega⟩
    simp only [Nat.add_sub_cancel' (by omega : 8 ≤ i.val)] at hb
    exact (hh (i.val - 8) (by omega)).trans (congrArg some hb)

theorem digest_half {s : RamState} {base : BitVec 64} {digest : Vector UInt8 16}
    (h : (⟨base.toNat, 16⟩ : MemoryRegion).HasBytes s.external ⟨digest.toArray⟩)
    (offset : Nat) (ho : offset + 8 ≤ 16) (i : Fin 8) :
    storedByte ((Operand.mem (base + BitVec.ofNat 64 offset) : Operand 64).read s) i.val =
      digest[offset + i.val] := by
  change storedByte (memLoad s.external _ 64) _ = _
  rw [storedByte_memLoad _ _ _ i.isLt]
  have hb := h.2 ⟨offset + i.val, by simp only [ByteArray.size, Vector.size_toArray]; omega⟩
  change s.external[BitVec.ofNat 64 (base.toNat + (offset + i.val))]? =
    some digest[offset + i.val] at hb
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add, ← BitVec.add_assoc] at hb
  change (s.external[_]?).getD 0 = _
  rw [hb]
  rfl

theorem effect_absorbed {variant : Variant} {s t : RamState} (hs : Storage s variant) (h : (effect s variant).Holds s t) :
    Absorbed (context s) ByteArray.empty t := by
  have hw : Write.AllHold t
      [⟨(.mem (stackPtr s + 0x50) : Operand 64), 0x1032547698badcfe⟩,
       ⟨(.mem (stackPtr s + 0x48) : Operand 64), 0xefcdab8967452301⟩,
       ⟨(.mem (stackPtr s + 0x58) : Operand 64), 0⟩,
       ⟨(.mem (stackPtr s + 0x47) : Operand 8), 0⟩] := by
    have hw := h.writes
    cases variant <;> simp only [effect, Write.AllHold] at hw ⊢
    · exact ⟨hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1,
        hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1⟩
    · exact ⟨hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1⟩
  simp only [Write.AllHold] at hw
  have hv : 368 ≤ variant.stackBytes := by cases variant <;> decide
  have ha : ∀ i < 16, (t.external[stackPtr s + 0x48 + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ h.agrees.grow _ ((stackWritable hs 0x48 16 (by omega)).bytes i hi)
  have hb := hasBytes_of_halves (base := stackPtr s + 0x48)
    (bytes := Standards.RFC.MD5.Buffer.initial.toBytes) ha hw.2.1
    (by simpa [BitVec.add_assoc] using hw.1)
    (show ∀ i : Fin 8, storedByte (0xefcdab8967452301 : BitVec 64) i.val =
      Standards.RFC.MD5.Buffer.initial.toBytes[i.val]'(Nat.lt_trans i.isLt (by decide)) by decide +kernel)
    (show ∀ i : Fin 8, storedByte (0x1032547698badcfe : BitVec 64) i.val =
      Standards.RFC.MD5.Buffer.initial.toBytes[8 + i.val]'(Nat.add_lt_add_left i.isLt 8) by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [absorbedBuffer_empty]
    have he : (context s).toNat + 64 = (stackPtr s + 0x48).toNat := by
      change (stackPtr s + BitVec.ofNat 64 8).toNat + 64 =
        (stackPtr s + BitVec.ofNat 64 0x48).toNat
      rw [stackAddress_toNat hs 8 (by omega), stackAddress_toNat hs 0x48 (by omega)]
    simpa only [he] using hb
  · refine ⟨?_, ?_⟩
    · rfl
    · intro i
      have hi := i.isLt
      change i.val < 0 at hi
      omega
  · simpa [context, BitVec.add_assoc] using hw.2.2.2
  · simpa [context, BitVec.add_assoc] using hw.2.2.1

theorem effect_digest {variant : Variant} {s t : RamState} {digest : Vector UInt8 16}
    (hs : Storage s variant) (h : (effect s variant).Holds s t)
    (hd : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    (outputRegion s).HasBytes t.external ⟨digest.toArray⟩ := by
  have hw : Write.AllHold t
      [⟨(.mem (outputAddress s + 8) : Operand 64),
        (Operand.mem (stackPtr s + 0xf0) : Operand 64).read s⟩,
       ⟨(.mem (outputAddress s) : Operand 64),
        (Operand.mem (stackPtr s + 0xe8) : Operand 64).read s⟩] := by
    have hw := h.writes
    cases variant <;> simp only [effect, Write.AllHold] at hw ⊢
    · exact hw.2.2.2.2.2.2.2.2.2
    · exact hw.2.2.2.2.2.2.2
  simp only [Write.AllHold] at hw
  have ha : ∀ i < 16, (t.external[outputAddress s + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    apply h.agrees.grow
    simpa only [BitVec.add_zero] using (outputWritable hs 0 16 (by decide)).bytes i hi
  apply hasBytes_of_halves ha hw.2 hw.1
  · intro i
    simpa only [BitVec.add_zero, Nat.zero_add] using
      digest_half hd 0 (by decide) i
  · intro i
    simpa [BitVec.add_assoc] using digest_half hd 8 (by decide) i

end Md5.Proofs.Buffered.FinalizeReset.Export
