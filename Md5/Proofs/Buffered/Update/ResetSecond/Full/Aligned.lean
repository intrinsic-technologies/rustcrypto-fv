import Md5.Proofs.Buffered.Update.ResetSecond.FullEntry
import Md5.Proofs.Buffered.Update.Batch

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem aligned_ready [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 = 0) :
    ∃ t, UpdateBatchReady kind boundary input s 0 (absorbedBuffer message)
      (message.size / 64) t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := full_entry hkind h hfull
  have hp : u.RIP = (pc kind 0x100a82) := by
    rw [he.rip]
    change (if position kind s = 0 then (pc kind 0x100a82) else (pc kind 0x1009fe)) = _
    rw [position_of_pre h, hpos]
    rfl
  obtain ⟨ft, t, hat, hrt, hct, hb⟩ :=
    aligned_count_branch hkind boundary h.boundaryOutside u hru hcu hp
  have hsizeReg : (Operand.reg kind.sizeRegister : Operand 64).read u = BitVec.ofNat 64 input.size :=
    (he.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [fullEntryEffect, prefixEffect, Effect.components, positionRegister, UpdateKind.sizeRegister])).trans h.inputSize
  have hsize : input.size < 2^64 := by have := h.totalSize; omega
  have hcount : (Operand.reg kind.sizeRegister : Operand 64).read u >>> 6 =
      BitVec.ofNat 64 (input.size / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [hsizeReg]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hsize, Nat.mod_eq_of_lt (show input.size / 64 < 2^64 by omega)]
  have hzero : (Operand.reg kind.sizeRegister : Operand 64).read u >>> 6 = 0 ↔ input.size / 64 = 0 := by
    rw [hcount]
    constructor
    · intro hz
      have hn := congrArg BitVec.toNat hz
      change (input.size / 64) % 2^64 = 0 at hn
      rw [Nat.mod_eq_of_lt (show input.size / 64 < 2^64 by omega)] at hn
      exact hn
    · intro hz
      rw [hz]
      rfl
  have hag := he.agrees.trans hb.agrees
  have hmem : t.external = s.external := hag.external (by
    simp [fullEntryEffect, prefixEffect, alignedBranchEffect, alignedCountEffect,
      Effect.components, Component.Covers])
  refine ⟨t, ⟨⟨fu + ft, hau.trans hat⟩, hrt, hct, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hb.rip]
    change (if (Operand.reg kind.sizeRegister : Operand 64).read u >>> 6 = 0 then (pc kind 0x100a4a) else (pc kind 0x100a35)) =
      if (input.size - 0) / 64 = 0 then kind.tailEntry else kind.batchEntry
    simp only [hzero, Nat.sub_zero]
    rcases hkind with rfl | rfl | rfl <;> rfl
  · apply hag.mono
    intro c hc
    simp only [fullEntryEffect, prefixEffect, alignedBranchEffect, alignedCountEffect,
      Effect.components, List.map_cons, List.map_nil, Write.component_reg, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, positionRegister]
  · exact (hag.read (n := 64) (r := kind.inputRegister) (by
      rcases hkind with rfl | rfl | rfl <;> simp [fullEntryEffect, prefixEffect, alignedBranchEffect, alignedCountEffect,
        Effect.components, positionRegister, UpdateKind.inputRegister])).trans (BitVec.add_zero _).symm
  · have hbsize := hb.writes.1.trans hsizeReg
    rcases hkind with rfl | rfl | rfl <;> exact hbsize
  · exact hb.writes.2.trans hcount
  · rw [hmem]
    exact h.absorbed.buffer
  · simpa only [Operand.read, hmem] using h.absorbed.blocks

end Md5.Proofs.Buffered.ResetSecond
