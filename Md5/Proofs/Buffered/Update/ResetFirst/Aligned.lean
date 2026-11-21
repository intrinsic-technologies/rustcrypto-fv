import Md5.Proofs.Buffered.Update.ResetFirst.FullEntry
import Md5.Proofs.Buffered.Update.ResetFirst.CountBranch
import Md5.Proofs.Buffered.Update.ResetFirst.BatchContracts
import Md5.Proofs.Buffered.Update.ResetFirst.Arithmetic

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem aligned_ready_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (haligned : message.size % 64 = 0) :
    ∃ t, UpdateBatchReady kind boundary input s 0 (absorbedBuffer message) (message.size / 64) t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := full_entry_of_kind hk h hfull
  have hp : position_of_kind kind s = 0 := by rw [position_of_pre_of_kind h, haligned]; rfl
  have hu14 : (.reg kind.sizeRegister : Operand 64).read u = BitVec.ofNat 64 input.size :=
    (he.agrees.read (by rcases hk with rfl | rfl | rfl <;> simp [reg, UpdateKind.sizeRegister, fullEntryEffect_of_kind, prefixEffect_of_kind, Effect.components])).trans h.inputSize
  have hsize : input.size < 2^64 := by have := h.totalSize; omega
  have hrip : u.RIP = (pc kind 0x779) := by
    rw [he.rip, fullEntryEffect_of_kind, hp]
    rfl
  have hcount : 64 ≤ ((.reg kind.sizeRegister : Operand 64).read u).toNat := by
    rw [hu14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize]
    omega
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    aligned_count_nonzero_of_kind hk boundary h.boundaryOutside u hru hcu ⟨hrip, hcount⟩
  have ha := he.agrees.trans hf.agrees
  have hm : t.external = s.external := ha.external (by
    rcases hk with rfl | rfl | rfl <;> simp [reg, UpdateKind.sizeRegister, fullEntryEffect_of_kind, prefixEffect_of_kind, alignedBranchEffect_of_kind, alignedCountEffect_of_kind,
      Effect.components, Component.Covers])
  refine ⟨t, ⟨⟨fu + ft, hau.trans hat⟩, hrt, hct, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Nat.sub_zero, ite_eq_right (show ¬ input.size / 64 = 0 by omega)]
    rcases hk with rfl | rfl | rfl <;> exact hf.rip
  · apply ha.mono
    intro c hc
    simp only [fullEntryEffect_of_kind, prefixEffect_of_kind, alignedBranchEffect_of_kind, alignedCountEffect_of_kind,
      Effect.components, List.map_cons, List.map_nil, Write.component_reg,
      List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl | rfl <;> simp [reg, UpdateKind.changes, UpdateKind.workRegisters]
  · change (.reg kind.inputRegister : Operand 64).read t = (.reg kind.inputRegister : Operand 64).read s + 0
    exact (ha.read (n := 64) (r := kind.inputRegister) (by
      rcases hk with rfl | rfl | rfl <;> simp [reg, UpdateKind.inputRegister, fullEntryEffect_of_kind, prefixEffect_of_kind, alignedBranchEffect_of_kind, alignedCountEffect_of_kind,
        Effect.components])).trans (BitVec.add_zero _).symm
  · have hreg : kind.batchSizeRegister = reg kind 3 := by rcases hk with rfl | rfl | rfl <;> rfl
    change (.reg kind.batchSizeRegister : Operand 64).read t = _
    rw [hreg]
    change (.reg (reg kind 3) : Operand 64).read t = BitVec.ofNat 64 (input.size - 0)
    exact hf.writes.1.trans hu14
  · have ht : (.reg 2 : Operand 64).read t = BitVec.ofNat 64 input.size >>> 6 :=
      hf.writes.2.trans (congrArg (fun x : BitVec 64 ↦ x >>> 6) hu14)
    rw [ht, ofNat_ushiftRight 64 input.size 6 hsize]
    rfl
  · rw [hm]
    exact h.absorbed.buffer
  · simpa only [Operand.read, hm] using h.absorbed.blocks

theorem aligned_ready [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (haligned : message.size % 64 = 0) :
    ∃ t, BatchReady boundary input s 0 (absorbedBuffer message) (message.size / 64) t := by
  exact aligned_ready_of_kind (kind := .resetFirst) (Or.inl rfl) h hfull haligned

end Md5.Proofs.Buffered.ResetFirst
