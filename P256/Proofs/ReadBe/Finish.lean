import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.ReadBe.Finish.Restore
import P256.Proofs.Common.Encoding.Serialize.Tail.Prepare.Encode.Immediate
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary) (state : LoopState s t input 4)
    (run : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, Result s u boundary input := by
  have code := programLoaded_codeIn state.frame.loaded
  have rip : t.RIP = 0x119170 := state.rip
  obtain ⟨t1, a1, r1, e1⟩ :=
    (mov_r32_r32_effect_step 0x119170 0xd9 rfl).advances
      (readyToStep state.frame.machine state.frame.bindingsSupported)
      (programText_slice code 0x19170 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19172 (by decide)))
  change (movR32R32Effect 0x119170 2 1 3 t).Holds t t1 at e1
  have f1 : AgreesExcept [.reg 1, .rip] t t1 := e1.agrees
  have ext1 := f1.external (by simp [Component.Covers])
  have cx1 : t1.regValue .rcx = 256 := by
    have h : t1.regValue .rcx = ((t.regValue .rbx).setWidth 32).setWidth 64 := e1.writes
    rw [state.bits] at h
    exact h
  obtain ⟨t2, a2, r2, e2⟩ :=
    (P256.Proofs.Common.Encoding.Serialize.prepare_mov_al_imm8_effect_step 0x119172 255).advances r1
      (programText_slice (code.of_external_eq ext1) 0x19172 _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19174 (by decide)))
  have f2 : AgreesExcept [.reg 0, .rip] t1 t2 := e2.agrees
  have ext2 := (f2.external (by simp [Component.Covers])).trans ext1
  have cx2 : t2.regValue .rcx = 256 := (f2.read (n := 64) (r := 1) (by simp)).trans cx1
  have al2 : (Operand.reg 0 : Operand 8).read t2 = 255 := by
    have h := congrArg (fun x : BitVec 64 => x.setWidth 8) e2.writes
    change (t2.regValue .rax).setWidth 8 = _ at h
    change (t2.regValue .rax).setWidth 8 = 255
    simpa only [P256.Proofs.Common.Encoding.Serialize.prepareMovAlImm8Effect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      show (255 : UInt8).toBitVec = (255 : BitVec 8) by decide +kernel] using h
  obtain ⟨t3, a3, r3, e3⟩ :=
    (and_r32_imm8_effect_step 0x119174 0xe1 63 rfl rfl).advances r2
      (programText_slice (code.of_external_eq ext2) 0x19174 _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19177 (by decide)))
  change (andR32Imm8Effect 0x119174 3 1 63 t2).Holds t2 t3 at e3
  have f3 : AgreesExcept [.reg 1, .flags, .rip] t2 t3 := e3.agrees
  have ext3 := (f3.external (by simp [Component.Covers])).trans ext2
  have zero : (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = true := by
    have h := e3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = (((t2.regValue .rcx).setWidth 32 &&& 63) == 0) at h
    rw [cx2] at h
    exact h
  have target : (jccEffect 0x119177 2 4 ((0x1d : BitVec 8).signExtend 64) t3).rip = 0x119196 := by
    simp [jccEffect, branchEffect, condHolds, zero, branchTarget]
  obtain ⟨u, a4, r4, e4⟩ := (jcc_rel8_effect_step 0x119177 4 0x1d).advances r3
    (programText_slice (code.of_external_eq ext3) 0x19177 _ (by decide +kernel) (by decide +kernel))
    ⟨e3.rip, by intro _; decide +kernel⟩
    (by rw [target]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19196 (by decide)))
  have f4 : AgreesExcept [.rip] t3 u := e4.agrees
  have total : AgreesExcept [.reg 0, .reg 1, .flags, .rip] t u :=
    ((f1.trans f2).trans f3).trans f4 |>.mono (by simp)
  have ext := (f4.external (by simp [Component.Covers])).trans ext3
  have frame := state.frame.of_agrees pre r4 total
    ((total.read (n := 64) (r := 4) (by simp)).trans state.frame.rsp)
    (by intro c hc a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim)
  obtain ⟨fuel, before⟩ := run
  apply restore_correct pre frame (e4.rip.trans target)
    ⟨fuel+4, before.trans (a1.trans (a2.trans (a3.trans a4)))⟩
  · exact ((f3.trans f4).read (n := 8) (r := 0) (by simp)).trans al2
  · intro j hj
    rw [ext]
    exact state.words j hj

end P256.Proofs.ReadBe
