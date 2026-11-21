import Md5.Proofs.Buffered.Update.Algebra
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def shortWriteRegions (kind : UpdateKind) (s : RamState) (message input : ByteArray) :
    Vector MemoryRegion 3 :=
  #v[UpdateKind.scratchRegion s,
    ⟨(kind.context s).toNat + message.size % 64, input.size⟩,
    ⟨(kind.context s).toNat + 63, 1⟩]

theorem absorbed_append_short_of_frame [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s)
    (hshort : message.size % 64 + input.size < 64)
    (hf : MemoryWriteFrame s t (shortWriteRegions kind s message input))
    (hi : (⟨(kind.context s).toNat + message.size % 64, input.size⟩ : MemoryRegion).HasBytes
      t.external input)
    (hp : (Operand.mem (kind.context s + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size)) :
    Absorbed (kind.context s) (message ++ input) t := by
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  have ht := size_tailBytes message
  have hbuffer : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    apply hasBytes_of_memoryWriteFrame hf h.absorbed.buffer
    · change (kind.context s).toNat + 64 + 16 < 2^32
      omega
    · intro r hr
      simp only [shortWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · intro address ha hb
        have ha' : (kind.context s).toNat + 64 ≤ address := ha.1
        have hb' : address < (stackPtr s).toNat - 320 + 320 := hb.2
        omega
      · intro address ha hb
        have ha' : (kind.context s).toNat + 64 ≤ address := ha.1
        have hb' : address < (kind.context s).toNat + message.size % 64 + input.size := hb.2
        omega
      · intro address ha hb
        have ha' : (kind.context s).toNat + 64 ≤ address := ha.1
        have hb' : address < (kind.context s).toNat + 63 + 1 := hb.2
        omega
  have htail : (⟨(kind.context s).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
      t.external (tailBytes message) := by
    apply hasBytes_of_memoryWriteFrame hf h.absorbed.tail
    · change (kind.context s).toNat + (tailBytes message).size < 2^32
      omega
    · intro r hr
      simp only [shortWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · intro address ha hb
        have ha' : (kind.context s).toNat ≤ address := ha.1
        have hb' : address < (stackPtr s).toNat - 320 + 320 := hb.2
        omega
      · intro address ha hb
        have ha' : address < (kind.context s).toNat + (tailBytes message).size := ha.2
        have hb' : (kind.context s).toNat + message.size % 64 ≤ address := hb.1
        omega
      · intro address ha hb
        have ha' : address < (kind.context s).toNat + (tailBytes message).size := ha.2
        have hb' : (kind.context s).toNat + 63 ≤ address := hb.1
        omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [absorbedBuffer_append_short _ _ hshort]
    exact hbuffer
  · rw [tailBytes_append_short _ _ hshort]
    apply hasBytes_append htail
    simpa only [ht] using hi
  · rw [position_append_short _ _ hshort]
    exact hp
  · rw [blockCount_append_short _ _ hshort]
    refine Eq.trans ?_ h.absorbed.blocks
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
    apply hf
    intro r hr
    have haddr : (kind.context s + 80 + BitVec.ofNat 64 i).toNat =
        (kind.context s).toNat + 80 + i := by
      have ha : kind.context s + 80 + BitVec.ofNat 64 i =
          kind.context s + BitVec.ofNat 64 (80 + i) := by
        rw [BitVec.ofNat_add]
        exact BitVec.add_assoc ..
      rw [ha, toNat_add_ofNat _ _ (by omega)]
      omega
    simp only [shortWriteRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · intro hb
      have hb' : (kind.context s + 80 + BitVec.ofNat 64 i).toNat <
          (stackPtr s).toNat - 320 + 320 := hb.2
      rw [haddr] at hb'
      omega
    · intro hb
      have hb' : (kind.context s + 80 + BitVec.ofNat 64 i).toNat <
          (kind.context s).toNat + message.size % 64 + input.size := hb.2
      rw [haddr] at hb'
      omega
    · intro hb
      have hb' : (kind.context s + 80 + BitVec.ofNat 64 i).toNat <
          (kind.context s).toNat + 63 + 1 := hb.2
      rw [haddr] at hb'
      omega

end Md5.Proofs.Buffered
