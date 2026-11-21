import Md5.Proofs.Buffered.Update.Calls

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem CallSiteResult.context_prefix_frame [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s u v : RamState}
    (h : UpdatePre kind boundary message input s) {ret : BitVec 64}
    (hc : CallSiteResult boundary ret u v) (hsp : stackPtr u = stackPtr s)
    (hdi : rdi.read u = kind.context s)
    (hcount : (MemoryRoutines.rdx.read u).toNat ≤ 64) :
    MemoryWriteFrame u v #v[UpdateKind.scratchRegion s,
      ⟨(kind.context s).toNat, (MemoryRoutines.rdx.read u).toNat⟩] := by
  have hctx : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  apply hc.agrees.memoryWriteFrame
  intro c hc' address hcover
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨⟨(kind.context s).toNat, (MemoryRoutines.rdx.read u).toNat⟩, by simp, ?_⟩
    change (kind.context s).toNat ≤ _ ∧
      _ < (kind.context s).toNat + (MemoryRoutines.rdx.read u).toNat
    rw [hdi, toNat_add_ofNat _ _ (by omega)]
    omega
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨UpdateKind.scratchRegion s, by simp, ?_⟩
    have hlo := h.stackLow
    have hhi : (stackPtr s).toNat + kind.contextOffset + 88 < 2^32 := h.stackHigh
    have hsn : (pushAddr u).toNat = (stackPtr s).toNat - 8 := by
      rw [pushAddr, hsp, BitVec.toNat_sub_of_le]
      · rfl
      · rw [BitVec.le_def]
        change 8 ≤ (stackPtr s).toNat
        omega
    rw [toNat_add_ofNat _ _ (by rw [hsn]; omega), hsn]
    change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + 320
    omega

theorem CallSiteResult.preserves_position [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s u v : RamState}
    (h : UpdatePre kind boundary message input s) {ret : BitVec 64}
    (hc : CallSiteResult boundary ret u v) (hsp : stackPtr u = stackPtr s)
    (hdi : rdi.read u = kind.context s)
    (hcount : (MemoryRoutines.rdx.read u).toNat < 64) :
    (Operand.mem (kind.context s + 63) : Operand 8).read v =
      (Operand.mem (kind.context s + 63) : Operand 8).read u := by
  have hf := hc.context_prefix_frame h hsp hdi (by omega)
  have hctx : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  have hctxval := h.context_toNat
  have hlo := h.stackLow
  apply memLoad_congr
  intro i hi
  have : i = 0 := by omega
  subst i
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply hf
  intro region hr hcontains
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  have haddr : (kind.context s + 63 + BitVec.ofNat 64 0).toNat =
      (kind.context s).toNat + 63 := by
    rw [BitVec.add_zero]
    exact toNat_add_ofNat _ 63 (by omega)
  rcases hr with rfl | rfl
  · have he : (kind.context s + 63 + BitVec.ofNat 64 0).toNat <
        (stackPtr s).toNat - 320 + 320 := hcontains.2
    rw [haddr] at he
    omega
  · have he : (kind.context s + 63 + BitVec.ofNat 64 0).toNat <
        (kind.context s).toNat + (MemoryRoutines.rdx.read u).toNat := hcontains.2
    rw [haddr] at he
    omega

end Md5.Proofs.Buffered
