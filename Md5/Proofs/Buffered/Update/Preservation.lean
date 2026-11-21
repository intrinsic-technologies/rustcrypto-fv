import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem UpdatePre.state_of_tail_frame [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {buffer : Standards.RFC.MD5.Buffer}
    {initial s t : RamState} (h : UpdatePre kind boundary message input initial)
    (hf : MemoryWriteFrame s t
      #v[UpdateKind.scratchRegion initial, ⟨(kind.context initial).toNat, 64⟩])
    (hb : (⟨(kind.context initial).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(kind.context initial).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ ∧
    (Operand.mem (kind.context initial + 80) : Operand 64).read t =
      (Operand.mem (kind.context initial + 80) : Operand 64).read s := by
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  refine ⟨?_, ?_⟩
  · apply hasBytes_of_memoryWriteFrame hf hb
    · change (kind.context initial).toNat + 64 + 16 < 2^32
      omega
    · intro region hr
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      all_goals intro address ha hb
      all_goals dsimp only [MemoryRegion.Contains, UpdateKind.scratchRegion] at ha hb
      all_goals omega
  · apply memLoad_congr
    intro i hi
    have haddr : (kind.context initial + 80 + BitVec.ofNat 64 i).toNat =
        (kind.context initial).toNat + 80 + i := by
      have he : kind.context initial + 80 + BitVec.ofNat 64 i =
          kind.context initial + BitVec.ofNat 64 (80 + i) := by
        rw [BitVec.ofNat_add]
        exact BitVec.add_assoc ..
      rw [he, toNat_add_ofNat _ _ (by omega)]
      omega
    apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
    apply hf
    intro region hr
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals intro hh
    all_goals dsimp only [MemoryRegion.Contains, UpdateKind.scratchRegion] at hh
    all_goals rw [haddr] at hh
    all_goals omega

theorem UpdatePre.bytes_before_counter_of_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input bytes : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial) {changes : List Component}
    (ha : AgreesExcept changes s t)
    (hm : ∀ c ∈ changes, ∀ address, c.Covers address →
      (Component.mem (kind.context initial + 80) 8).Covers address)
    {offset : Nat} (hoff : offset + bytes.size ≤ 80)
    (hb : (⟨(kind.context initial).toNat + offset, bytes.size⟩ : MemoryRegion).HasBytes
      s.external bytes) :
    (⟨(kind.context initial).toNat + offset, bytes.size⟩ : MemoryRegion).HasBytes
      t.external bytes := by
  have hctx : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  have hcBound : (⟨(kind.context initial).toNat + 80, 8⟩ : MemoryRegion).Bounded := by
    change (kind.context initial).toNat + 80 + 8 < 2^32
    omega
  refine ⟨rfl, fun i ↦ ?_⟩
  refine Eq.trans (ha.byte ?_) (hb.2 i)
  intro c hc hcover
  have hh := hm c hc _ hcover
  change (Component.mem (kind.context initial + 80#64) 8).Covers _ at hh
  have hcontains := Block.contains_of_mem_covers hcBound (by
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh)
  have hi := i.isLt
  have haddr : (kind.context initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i.val).toNat =
      (kind.context initial).toNat + offset + i.val := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)]
    omega
  change (kind.context initial).toNat + 80 ≤ _ ∧ _ at hcontains
  rw [haddr] at hcontains
  omega

end Md5.Proofs.Buffered
