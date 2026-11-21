import Sha2.Proofs.Common.SHA256.Absorb.Proof.Registers

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem bulk_registers [Bindings] {l : Layout} {sp : BitVec 64} {s u called v t : RamState}
    {boundary : ReturnBoundary} {ret : BitVec 64}
    (flow : Flow l) (setup : (Stage.bulkSetup.effect l sp s).Holds s u)
    (call : (callEffect (fun _ => 0x10b4e0) ret u).Holds u called)
    (result : CalleeResult called v boundary 32 336)
    (restore : (Stage.bulkRestore.effect l sp v).Holds v t) :
    Blocks.readReg t l.alignedSource = Blocks.readReg s l.alignedSource ∧
      Blocks.readReg t l.registers.remaining = Blocks.readReg s l.registers.remaining := by
  have nonvolatile := flow.nonvolatile l.registers.remaining (by simp)
  have remainingCall : Blocks.readReg v l.registers.remaining = Blocks.readReg u l.registers.remaining :=
    call_result_register call result
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using l.registers.remaining.isLt)
      (nonvolatile_extended nonvolatile)
  have different : l.registers.remaining.setWidth 5 ≠ l.alignedSource.setWidth 5 := by
    intro h
    have same := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] at same
    have ne := (List.pairwise_cons.mp flow.splitRegisters).1 l.registers.remaining (by simp)
    exact ne (BitVec.eq_of_toNat_eq same.symm)
  cases hs : l.bulkSave with
  | none =>
    have sourceNonvolatile := flow.bulkSaved.1 hs
    have readSetup (r : BitVec 4) (member : r ∈ ([3,5,12,13,14,15] : List (BitVec 4))) :
        Blocks.readReg u r = Blocks.readReg s r := by
      apply setup.agrees.read
      have h := nonvolatile_extended member
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simpa [Stage.effect, hs, Effect.components, Write.component, Operand.component] using
        (show r.setWidth 5 ≠ 7 ∧ r.setWidth 5 ≠ 6 from ⟨h.2.2.2.2.1, h.2.2.2.1⟩)
    have sourceCall : Blocks.readReg v l.alignedSource = Blocks.readReg u l.alignedSource :=
      call_result_register call result
        (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using l.alignedSource.isLt)
        (nonvolatile_extended sourceNonvolatile)
    have readRestore (r : BitVec 4) : Blocks.readReg t r = Blocks.readReg v r :=
      restore.agrees.read (by simp [Stage.effect, hs, Effect.components])
    exact ⟨(readRestore _).trans (sourceCall.trans (readSetup _ sourceNonvolatile)),
      (readRestore _).trans (remainingCall.trans (readSetup _ nonvolatile))⟩
  | some saved =>
    have savedFacts := flow.bulkSaved.2 saved (by simp [hs])
    have savedSet : Blocks.readReg u saved = Blocks.readReg s l.alignedSource := by
      have writes := setup.writes
      simp only [Stage.effect, hs, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append] at writes
      exact writes.2.2
    have savedCall : Blocks.readReg v saved = Blocks.readReg u saved :=
      call_result_register call result
        (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using saved.isLt)
        (nonvolatile_extended savedFacts.1)
    have sourceRestore : Blocks.readReg t l.alignedSource = Blocks.readReg v saved := by
      have writes := restore.writes
      simp only [Stage.effect, hs, Option.toList_some, List.map_cons, List.map_nil] at writes
      exact writes
    have noAlias : l.registers.remaining.setWidth 5 ≠ saved.setWidth 5 := by
      intro h
      have same := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] at same
      exact savedFacts.2 (BitVec.eq_of_toNat_eq same.symm)
    have remainingSetup : Blocks.readReg u l.registers.remaining = Blocks.readReg s l.registers.remaining := by
      apply setup.agrees.read
      have h := nonvolatile_extended nonvolatile
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simpa [Stage.effect, hs, Effect.components, Write.component, Operand.component] using
        (show l.registers.remaining.setWidth 5 ≠ 7 ∧ l.registers.remaining.setWidth 5 ≠ 6 ∧
          l.registers.remaining.setWidth 5 ≠ saved.setWidth 5 from
            ⟨h.2.2.2.2.1, h.2.2.2.1, noAlias⟩)
    have remainingRestore : Blocks.readReg t l.registers.remaining = Blocks.readReg v l.registers.remaining :=
      restore.agrees.read (by simp [Stage.effect, hs, Effect.components, Write.component,
        Operand.component, different])
    exact ⟨sourceRestore.trans (savedCall.trans savedSet),
      remainingRestore.trans (remainingCall.trans remainingSetup)⟩

end Sha2.Proofs.Common.SHA256.Absorb
