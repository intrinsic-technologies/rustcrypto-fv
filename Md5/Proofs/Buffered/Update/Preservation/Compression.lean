import Md5.Proofs.Buffered.Update.Memory
import Md5.Proofs.Buffered.FinalizeReset.CompressCall.Frame

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem FinalizeReset.CompressCall.Post.update_counter [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input blocks : ByteArray} {buffer : Standards.RFC.MD5.Buffer}
    {initial s t : RamState} (h : UpdatePre kind boundary message input initial)
    {ret : BitVec 64} (hr : FinalizeReset.CompressCall.Post boundary ret buffer blocks s t)
    (hsp : stackPtr s = stackPtr initial)
    (hdi : s.regValue .rdi = kind.context initial + 64) :
    (Operand.mem (kind.context initial + 80) : Operand 64).read t =
      (Operand.mem (kind.context initial + 80) : Operand 64).read s := by
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  have hbuf : (⟨(kind.context initial).toNat + 64, 16⟩ : MemoryRegion).Bounded := by
    change (kind.context initial).toNat + 64 + 16 < 2^32
    omega
  have hstack : stackPtr s - 320 =
      BitVec.ofNat 64 (UpdateKind.scratchRegion initial).start := by
    rw [hsp]
    change stackPtr initial - 320 = BitVec.ofNat 64 ((stackPtr initial).toNat - 320)
    have hn : (stackPtr initial - 320).toNat = (stackPtr initial).toNat - 320 :=
      BitVec.toNat_sub_of_le h.stackLow
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply memLoad_congr
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
  apply hr.agrees.memory
  intro c hc hcover
  simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · rw [hdi] at hcover
    change (Component.mem (kind.context initial + 64#64) 16).Covers _ at hcover
    have hh := Block.contains_of_mem_covers hbuf (by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcover)
    change (kind.context initial).toNat + 64 ≤ _ ∧
      _ < (kind.context initial).toNat + 64 + 16 at hh
    rw [haddr] at hh
    omega
  · rw [hstack] at hcover
    have hh := Block.contains_of_mem_covers h.scratchBounded hcover
    change (stackPtr initial).toNat - 320 ≤ _ ∧
      _ < (stackPtr initial).toNat - 320 + 320 at hh
    rw [haddr] at hh
    omega

end Md5.Proofs.Buffered
