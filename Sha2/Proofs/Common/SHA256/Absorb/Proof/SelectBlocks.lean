import Sha2.Proofs.Common.SHA256.Absorb.Proof.Aligned
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Registers

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem select_blocks [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve consumed : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (data : Aligned l (l.sp initial) prior input consumed s)
    (bound : input.bytes.size < 2^61) (rip : s.RIP = l.pc .count)
    (bufferRegister : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer (l.sp initial))
    (restored : ∀ r ∈ l.bufferRestore, Blocks.readReg s r = l.buffer (l.sp initial)) :
    ∃ t, Preserved l initial before t regions ∧ Aligned l (l.sp initial) prior input consumed t ∧
      t.RIP = (if (input.bytes.size - consumed) / 64 = 0 then l.pc .splitTail else l.pc .addBlocks) ∧
      t.regValue .rdx = BitVec.ofNat 64 ((input.bytes.size - consumed) / 64) ∧
      (∀ r ∈ l.bufferRestore, Blocks.readReg t r = l.buffer (l.sp initial)) ∧
      t.external = s.external := by
  obtain ⟨u, stateU, count⟩ := run_stage ctx (Preserved.initial state.state state.rsp) .count rfl rip
    bufferRegister (by intro h; cases h)
  obtain ⟨t, stateT, branch⟩ := run_stage ctx stateU .countBranch rfl count.rip
    (stateU.buffer_register ctx.flow bufferRegister) (by intro h; cases h)
  have values := count_values data.length (by omega) count
  have readBranch (r : BitVec 5) : (.reg r : Operand 64).read t = (.reg r : Operand 64).read u :=
    branch.agrees.read (by simp [Stage.effect, branchEffect, Effect.components])
  have readCount (r : BitVec 4) (different : r.setWidth 5 ≠ 2) :
      Blocks.readReg t r = Blocks.readReg s r := by
    apply (readBranch _).trans
    exact count.agrees.read (by simpa [Stage.effect, Blocks.effect, Effect.components,
      Write.component, Operand.component, BitVec.ofNat_eq_ofNat] using different)
  have memoryU := count.agrees.external (by
    simp [Stage.effect, Blocks.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have memoryT := branch.agrees.external (by simp [Stage.effect, branchEffect, Effect.components, Component.Covers])
  have memory : t.external = s.external := memoryT.trans memoryU
  have sourceDifferent : l.alignedSource.setWidth 5 ≠ 2 := by
    intro h
    have same := congrArg (fun r : BitVec 5 => r.setWidth 4) h
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 4 ≤ 5), BitVec.setWidth_eq,
      BitVec.reduceSetWidth, ctx.flow.alignedSource] at same
    exact ctx.flow.sourceNotCount same
  have remainingDifferent : l.registers.remaining.setWidth 5 ≠ 2 := by
    have h := nonvolatile_extended (ctx.flow.nonvolatile l.registers.remaining (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact h.2.2.1
  refine ⟨t, {stateT with frame := state.frame.trans stateT.frame}, ?_, ?_,
    (readBranch 2).trans values.1, ?_, memory⟩
  · exact ⟨stateT.rsp, data.consumedBound, data.aligned,
      by simpa only [HashStateAt, memory] using data.hashWords,
      by simpa only [memory] using data.blocks,
      (readCount _ sourceDifferent).trans data.source,
      (readCount _ remainingDifferent).trans data.length⟩
  · rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then _ else _) = _
    rw [values.2]
    simp only [decide_eq_true_eq]
  · exact restored_of_stage ctx.flow (by simp) branch
      (restored_of_stage ctx.flow (by simp) count restored)

end Sha2.Proofs.Common.SHA256.Absorb
