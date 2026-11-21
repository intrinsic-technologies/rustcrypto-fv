import Sha3.Proofs.Permutation.RoundMachine.Semantics

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs RoundAlgebra Sha3.Spec.Program Prelude

theorem RoundMemory.of_holds {sp : BitVec 64} {s t : RamState} {e : Effect}
    (h : RoundMemory sp s) (he : e.Holds s t) : RoundMemory sp t :=
  ⟨⟨h.readable.low, fun i hi ↦ he.agrees.grow _ (h.readable.mem i hi)⟩,
    h.tables, h.program⟩

theorem writeEffect_covers {sp next value : BitVec 64} {dst : Location}
    {flags : Option StatusFlagsOutcome} {c : Component} {address : BitVec 64}
    (hc : c ∈ (writeEffect sp next dst value flags).components) (hcov : c.Covers address) :
    (operand sp dst).component.Covers address := by
  cases flags with
  | none =>
    have hc' : c = (operand sp dst).component ∨ c = .rip := by
      simpa [writeEffect, Effect.components, Write.component] using hc
    rcases hc' with rfl | rfl
    · exact hcov
    · exact hcov.elim
  | some f =>
    have hc' : c = (operand sp dst).component ∨ c = .flags ∨ c = .rip := by
      simpa [writeEffect, Effect.components, Write.component] using hc
    rcases hc' with rfl | rfl | rfl
    · exact hcov
    · exact hcov.elim
    · exact hcov.elim

theorem validWrite_stack_end {offset : Nat} (h : ValidWrite (.stack offset)) :
    offset + 8 ≤ 216 := by
  have hm : offset % 8 = 0 := h.1.1
  have hl : offset < 216 := h.2.2.2
  omega

theorem instructionEffect_avoids {sp next rc : BitVec 64} {op : Instruction}
    {flags : Option StatusFlagsOutcome} {s : RamState}
    (hv : ValidInstruction op) (hm : RoundMemory sp s) :
    (instructionEffect sp next rc op flags s).Avoids Extracted.programImage := by
  intro byte hbyte c hc hcov
  have hc' := writeEffect_covers hc hcov
  have hw := hv.1
  generalize hd : destination op = dst at hc' hw
  cases dst with
  | reg r => exact hc'
  | stack off =>
    have hend := validWrite_stack_end hw
    obtain ⟨i, hi, heq⟩ := hc'
    change byte.1 = sp + BitVec.ofNat 64 off + BitVec.ofNat 64 i at heq
    have hi' : off + i < 216 := by omega
    apply hm.program (off + i) hi'
    refine ⟨byte.2, ?_⟩
    have haddr : sp + BitVec.ofNat 64 (off + i) = byte.1 := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact heq.symm
    rwa [haddr]

theorem writeEffect_callFrame {next value : BitVec 64} {dst : Location}
    {flags : Option StatusFlagsOutcome} {initial s t : RamState}
    (hv : ValidWrite dst) (hm : RoundMemory (frameBase initial) s)
    (hf : CallFrame initial s)
    (he : (writeEffect (frameBase initial) next dst value flags).Holds s t) :
    CallFrame initial t := by
  have read_kept (loc : Location) (hl : ValidLocation loc) (hne : loc ≠ dst) :
      (operand (frameBase initial) loc).read t =
        (operand (frameBase initial) loc).read s :=
    read_writeEffect_of_ne he hv.1 hl hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (he.agrees.scalarFrame_eq (by cases dst <;> cases flags <;> simp [writeEffect, Effect.components, operand])).trans hf.rest⟩
  · exact (read_kept (.reg 4) trivial (Ne.symm hv.2.1)).trans hf.stack
  · exact (read_kept (.stack 160) (by decide) (Ne.symm hv.2.2.1)).trans hf.pointer
  · intro i
    have hl : ValidLocation (.stack (216 + 8 * i.val)) := by
      have := i.isLt
      change (216 + 8 * i.val) % 8 = 0 ∧ 216 + 8 * i.val < 272
      omega
    have hn : Location.stack (216 + 8 * i.val) ≠ dst := by
      intro hd
      rw [← hd] at hv
      have hend := validWrite_stack_end hv
      omega
    exact (read_kept _ hl hn).trans (hf.saved i)
  · have hn : Location.stack 264 ≠ dst := by
      intro hd
      rw [← hd] at hv
      have hend := validWrite_stack_end hv
      omega
    have hkeep := read_kept (.stack 264) (by decide) hn
    change (Operand.mem (frameBase initial + 264) : Operand 64).read t =
      (Operand.mem (frameBase initial + 264) : Operand 64).read s at hkeep
    rw [show frameBase initial + 264 = initial.regValue .rsp from
      frameBase_add_frameBytes initial] at hkeep
    exact hkeep.trans hf.returnSlot
  · apply memoryWriteFrame_trans hf.memory
    intro address houtside
    apply he.agrees.byte
    intro c hc hcov
    have hc' := writeEffect_covers hc hcov
    cases dst with
    | reg r => exact hc'
    | stack off =>
      have hend := validWrite_stack_end hv
      obtain ⟨i, hi, heq⟩ := hc'
      have hlow := hm.readable.low
      apply houtside ⟨(frameBase initial).toNat, frameBytes⟩ (by simp [writeRegions])
      change (frameBase initial).toNat ≤ address.toNat ∧
        address.toNat < (frameBase initial).toNat + 264
      change address = frameBase initial + BitVec.ofNat 64 off + BitVec.ofNat 64 i at heq
      rw [heq]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
  · intro address ha
    exact he.agrees.grow address (hf.grows address ha)

theorem instructionEffect_callFrame {next rc : BitVec 64} {op : Instruction}
    {flags : Option StatusFlagsOutcome} {initial s t : RamState}
    (hv : ValidInstruction op) (hm : RoundMemory (frameBase initial) s)
    (hf : CallFrame initial s)
    (he : (instructionEffect (frameBase initial) next rc op flags s).Holds s t) :
    CallFrame initial t := writeEffect_callFrame hv.1 hm hf he

end Sha3.Proofs.Permutation.RoundMachine
