import Md5.Proofs.Buffered.Update.Algebra
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def fillWriteRegions (kind : UpdateKind) (s : RamState) (message : ByteArray) :
    Vector MemoryRegion 2 :=
  #v[UpdateKind.scratchRegion s,
    ⟨(kind.context s).toNat + message.size % 64, 64 - message.size % 64⟩]

set_option maxRecDepth 4096 in
theorem filledBlock_of_frame [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s)
    (hfull : 64 - message.size % 64 ≤ input.size)
    (hf : MemoryWriteFrame s t (fillWriteRegions kind s message))
    (hi : (⟨(kind.context s).toNat + message.size % 64, 64 - message.size % 64⟩ :
      MemoryRegion).HasBytes t.external (input.extract 0 (64 - message.size % 64))) :
    (⟨(kind.context s).toNat, 64⟩ : MemoryRegion).HasBytes t.external
      (updateBlock message input) ∧
    (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ ∧
    (Operand.mem (kind.context s + 80) : Operand 64).read t =
      BitVec.ofNat 64 (message.size / 64) := by
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  have htail := size_tailBytes message
  have hprefix : (⟨(kind.context s).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
      t.external (tailBytes message) := by
    apply hasBytes_of_memoryWriteFrame hf h.absorbed.tail
    · change (kind.context s).toNat + (tailBytes message).size < 2^32
      omega
    · intro region hr
      simp only [fillWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      all_goals intro address ha hb
      all_goals dsimp only [MemoryRegion.Contains, UpdateKind.scratchRegion] at ha hb
      all_goals omega
  refine ⟨?_, ?_, ?_⟩
  · have hs := size_updateBlock message input hfull
    have hcopy : (⟨(kind.context s).toNat, (updateBlock message input).size⟩ : MemoryRegion).HasBytes
        t.external (updateBlock message input) := by
      unfold updateBlock
      apply hasBytes_append hprefix
      have hsize : (input.extract 0 (64 - message.size % 64)).size =
          64 - message.size % 64 := by simp only [ByteArray.size_extract]; omega
      simpa only [htail, hsize] using hi
    simpa only [hs] using hcopy

  · apply hasBytes_of_memoryWriteFrame hf h.absorbed.buffer
    · change (kind.context s).toNat + 64 + 16 < 2^32
      omega
    · intro region hr
      simp only [fillWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      all_goals intro address ha hb
      all_goals dsimp only [MemoryRegion.Contains, UpdateKind.scratchRegion] at ha hb
      all_goals omega
  · refine Eq.trans ?_ h.absorbed.blocks
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
    apply hf
    intro region hr
    have haddr : (kind.context s + 80 + BitVec.ofNat 64 i).toNat =
        (kind.context s).toNat + 80 + i := by
      have he : kind.context s + 80 + BitVec.ofNat 64 i =
          kind.context s + BitVec.ofNat 64 (80 + i) := by
        rw [BitVec.ofNat_add]
        exact BitVec.add_assoc ..
      rw [he, toNat_add_ofNat _ _ (by omega)]
      omega
    simp only [fillWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals intro hb
    all_goals dsimp only [MemoryRegion.Contains, UpdateKind.scratchRegion] at hb
    all_goals rw [haddr] at hb
    all_goals omega

end Md5.Proofs.Buffered
