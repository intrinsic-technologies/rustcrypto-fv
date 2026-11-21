import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Entry
import Md5.Proofs.Buffered.Update.Slices.Full.Machine.Branch
import Md5.Proofs.Buffered.Update.Slices.Full.Contracts

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem aligned_ready {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s v : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hprepared : Prepared variant boundary s v)
    (hfull : 64 - message.size % 64 ≤ input.size) (haligned : message.size % 64 = 0) :
    ∃ t, BatchReady variant boundary input s 0 (absorbedBuffer message) (message.size / 64) t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := full_entry h hprepared hfull
  have hp : position s = 0 := by rw [position_eq h, haligned]; rfl
  have hu3 : (.reg 3 : Operand 64).read u = BitVec.ofNat 64 input.size :=
    (he.agrees.read (by simp [fullEntryEffect, entryEffect, Effect.components])).trans (by simpa only [kind_sizeRegister] using h.inputSize)
  have hsize : input.size < 2^64 := by have := h.totalSize; omega
  have hrip : u.RIP = (pc variant 0x10041d) := by
    rw [he.rip, fullEntryEffect, hp]
    rfl
  have hcount : 64 ≤ ((.reg 3 : Operand 64).read u).toNat := by
    rw [hu3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize]
    omega
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    aligned_count_nonzero boundary h.boundaryOutside u hru hcu ⟨hrip, hcount⟩
  have ha := he.agrees.trans hf.agrees
  have hm : t.external = s.external := ha.external (by
    simp [fullEntryEffect, entryEffect, alignedBranchEffect, alignedCountEffect,
      Effect.components, Component.Covers])
  refine ⟨t, ⟨⟨fu + ft, hau.trans hat⟩, hrt, hct, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Nat.sub_zero, ite_eq_right (show ¬ input.size / 64 = 0 by omega)]
    simpa only [kind_batchEntry, alignedBranchEffect] using hf.rip
  · apply ha.mono
    intro c hc
    simp only [fullEntryEffect, entryEffect, alignedBranchEffect, alignedCountEffect,
      Effect.components, List.map_cons, List.map_nil, Write.component_reg,
      List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp [kind, UpdateKind.changes, UpdateKind.workRegisters]
  · simp only [kind_inputRegister]
    change (.reg 14 : Operand 64).read t = (.reg 14 : Operand 64).read s + 0
    exact (ha.read (n := 64) (r := 14) (by
      simp [fullEntryEffect, entryEffect, alignedBranchEffect, alignedCountEffect,
        Effect.components])).trans (BitVec.add_zero _).symm
  · simpa only [Nat.sub_zero, kind_batchSizeRegister] using hf.writes.1.trans hu3
  · have ht : (.reg 2 : Operand 64).read t = BitVec.ofNat 64 input.size >>> 6 :=
      hf.writes.2.trans (congrArg (fun x : BitVec 64 ↦ x >>> 6) hu3)
    rw [ht]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.sub_zero, Nat.mod_eq_of_lt hsize]
    change input.size / 64 = input.size / 64 % 2^64
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [hm]
    exact h.absorbed.buffer
  · simpa only [Operand.read, hm] using h.absorbed.blocks

end Md5.Proofs.Buffered.Update.Slices
