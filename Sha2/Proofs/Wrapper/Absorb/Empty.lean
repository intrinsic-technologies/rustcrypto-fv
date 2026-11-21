import Sha2.Proofs.Wrapper.Absorb.Branch
import Sha2.Proofs.Wrapper.Absorb.Blocks.State
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem empty {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : Prepared (v := v) initial s inputs index)
    (rip : s.RIP=(v.pc 0x1ad)) (position : (prefixMessage inputs index).size%64=0) :
    ∃ t, Blocks.Input (v := v) initial t inputs index 0 ∧ t.RIP=(v.pc 0x1b0) := by
  obtain ⟨t,run,ready,effect⟩ :=
    (mov_r64_r64_effect_step (v.pc 0x1ad) 0x48 0xdd (by simp [RexWPrefix]) rfl).advances
      (supportedMachine_readyToStep input.machine)
      (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + 0x1ad) [0x48,0x89,0xdd]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (by
        change v.pc 0x1ad + BitVec.ofNat 64 3 ≠ _
        rw [Variant.pc_add]
        exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
          (Variant.pc_inProgram v (by decide : 0x1b0 < 1024)))
  have frame : AgreesExcept [.reg 5,.rip] s t := effect.agrees
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame
    (by simp [Component.Covers]) (by simp)
  refine ⟨t,⟨buffered.toPreserved,input.remaining,Nat.zero_le _,?_,?_,?_,?_,?_,?_,?_⟩,effect.rip.trans (Variant.pc_add v 0x1ad 3)⟩
  · simpa using position
  · simpa using buffered.hashWords
  · simpa using buffered.blocks
  · change t.regValue .r13 = (inputs[index]'input.remaining).address+(0#64)
    rw [BitVec.add_zero]
    exact (frame.read (n:=64) (r:=13) (by simp)).trans input.source
  · have write : t.regValue .rbp=s.regValue .rbx := effect.writes
    simpa using write.trans input.length
  · exact (frame.read (n:=64) (r:=14) (by simp)).trans input.indexRegister
  · exact (frame.read (n:=64) (r:=15) (by simp)).trans input.countRegister

end Sha2.Proofs.Wrapper.Absorb
