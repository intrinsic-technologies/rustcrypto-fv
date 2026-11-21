import P256.Proofs.Nonce.Fill.Tail.State
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search

theorem retry [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Context initial s orderAddress state) (rip : s.RIP = 0x1076c3) :
    ∃ t, Advances boundary 5 s t ∧ Loop initial t orderAddress (nextState state) := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_m64_effect_step 0x1076c3 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl).advances
      (readyToStep input.machine input.bindingsSupported)
      (programText_slice (programLoaded_codeIn input.loaded) 0x76c3 _
        (by decide) (by decide +kernel))
      ⟨rip, stack_readable pre input.toFrame (offset := 64) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76c8 (by decide)))
  have f1 : AgreesExcept [.reg 7, .rip] s s1 := e1.agrees
  have c1 := input.after_registers r1 f1 (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  have rdi1 : s1.regValue .rdi = initial.regValue .rdi + 8 := by
    have value : s1.regValue .rdi = memLoad s.external (stackPtr s + 64) 64 := e1.writes
    rw [value, input.rsp]
    exact input.statePointerSlot
  obtain ⟨s2, a2, r2, e2⟩ :=
    (test_r64_r64_effect_step 0x1076c8 0x4d 0xed (by simp [RexWPrefix]) rfl).advances r1
      (programText_slice (programLoaded_codeIn c1.loaded) 0x76c8 _
        (by decide) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76cb (by decide)))
  change (testR64R64Effect 0x1076c8 13 13 s1).Holds s1 s2 at e2
  have f2 : AgreesExcept [.flags, .rip] s1 s2 := e2.agrees
  have c2 := c1.after_registers r2 f2 (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  have zf2 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = false := by
    have h := e2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      ((s1.regValue .r13 &&& s1.regValue .r13) == 0) at h
    rw [c1.r13] at h
    exact h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r64_m64_effect_step 0x1076cb 0x4c (by simp [RexWPrefix]) 4
      (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl).advances r2
      (programText_slice (programLoaded_codeIn c2.loaded) 0x76cb _
        (by decide) (by decide +kernel))
      ⟨e2.rip, stack_readable pre c2.toFrame (offset := 136) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76d3 (by decide)))
  have f3 : AgreesExcept [.reg 12, .rip] s2 s3 := e3.agrees
  have c3 := c2.after_registers r3 f3 (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  have r12 : s3.regValue .r12 = initial.regValue .rdi + 40 := by
    have value : s3.regValue .r12 = memLoad s2.external (stackPtr s2 + 136) 64 := e3.writes
    rw [value, c2.rsp]
    exact c2.valuePointerSlot
  obtain ⟨s4, a4, r4, e4⟩ :=
    (lea_r64_effect_step 0x1076d3 0x48 (by simp [RexWPrefix]) 3
      (.rip 0x15256) (by decide +kernel) rfl rfl).advances r3
      (programText_slice (programLoaded_codeIn c3.loaded) 0x76d3 _
        (by decide) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76da (by decide)))
  have f4 : AgreesExcept [.reg 3, .rip] s3 s4 := e4.agrees
  have c4 := c3.after_registers r4 f4 (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  have rbx : s4.regValue .rbx = 0x11c930 := e4.writes
  have zf4 : (StatusFlags.ofRFLAGS s4.RFLAGS).ZF = false := by
    rw [(f3.trans f4).statusFlags (by simp)]
    exact zf2
  have target : (jccEffect 0x1076da 6 5 ((0xfffffcc0 : BitVec 32).signExtend 64) s4).rip =
      0x1073a0 := by
    simp [jccEffect, branchEffect, condHolds, zf4, branchTarget]
  obtain ⟨t, a5, rt, e5⟩ := (jcc_rel32_effect_step 0x1076da 5 0xfffffcc0).advances r4
    (programText_slice (programLoaded_codeIn c4.loaded) 0x76da _
      (by decide) (by decide +kernel)) ⟨e4.rip, by intro; decide +kernel⟩
    (by
      rw [target]
      exact boundary_ne_program pre.outerBoundary
        (inProgram_of_textOffset 0x73a0 (by decide)))
  have f5 : AgreesExcept [.rip] s4 t := e5.agrees
  have final := c4.after_registers rt f5 (by simp [Component.Covers])
    (by simp) (by simp) (by simp)
  refine ⟨t, a1.trans (a2.trans (a3.trans (a4.trans a5))),
    final.toFrame, final.toSlots, e5.rip.trans target, ?_, ?_, ?_, final.generator⟩
  · exact ((((f2.trans f3).trans f4).trans f5).read (n := 64) (r := 7) (by simp)).trans rdi1
  · exact ((f4.trans f5).read (n := 64) (r := 12) (by simp)).trans r12
  · exact (f5.read (n := 64) (r := 3) (by simp)).trans rbx

end P256.Proofs.Nonce.Fill.Tail
