import P256.Proofs.Program.Code
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure EpiloguePre (s : RamState) : Prop where
  rip : s.RIP=0x11422d
  readable : ∀ i∈([152,160,168] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s+i) 8
  ret : InProgram ((Operand.mem ((Operand.reg 4 : Operand 64).read s+168) : Operand 64).read s)

def epilogueBytes : List UInt8 := [0x48,0x81,0xc4,0x98,0,0,0,0x5b,0x5d,0xc3]

theorem epilogue_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11422d epilogueBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1422d epilogueBytes
    (by decide +kernel) (by decide +kernel)

theorem epilogue [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hout : ¬InProgram boundary.rip) (ready : ReadyToStep s)
    (code : CodeIn (codeRange 0x11422d epilogueBytes) s) (pre : EpiloguePre s) :
    ∃ u, Advances boundary 4 s u ∧ ReadyToStep u ∧
      AgreesExcept [.reg 3,.reg 5,.reg 4,.flags,.rip] s u ∧
      u.RIP=(Operand.mem ((Operand.reg 4 : Operand 64).read s+168) : Operand 64).read s ∧
      stackPtr u=stackPtr s+176 ∧
      u.regValue .rbx=(Operand.mem ((Operand.reg 4 : Operand 64).read s+152) : Operand 64).read s ∧
      u.regValue .rbp=(Operand.mem ((Operand.reg 4 : Operand 64).read s+160) : Operand 64).read s := by
  obtain ⟨s1,a1,r1,e1⟩ := (add_r64_imm32_effect_step 0x11422d 0x48 0xc4 152
    (by simp [RexWPrefix]) rfl rfl).advances ready (code.mono
      (codeRange_slice_subset 0x11422d epilogueBytes 0 7)) pre.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x14234 (by decide)))
  change (addR64Imm32Effect 0x11422d 4 152 s).Holds s s1 at e1
  have sp1 : stackPtr s1=stackPtr s+152 := e1.writes
  have m1 : s1.external=s.external := e1.agrees.external (by simp [Component.Covers])
  obtain ⟨s2,a2,r2,e2⟩ := (pop_r64_effect_step 0x114234 0x5b (by decide) (by decide)).advances r1
    ((code.mono (codeRange_slice_subset 0x11422d epilogueBytes 7 1)).of_external_eq m1)
    ⟨e1.rip,by rw [sp1]; exact (pre.readable 152 (by simp)).of_external_eq m1⟩
    (boundary_ne_program hout (inProgram_of_textOffset 0x14235 (by decide)))
  change (popR64Effect 0x114234 1 3 s1).Holds s1 s2 at e2
  have sp2 : stackPtr s2=stackPtr s+160 := by
    rw [show stackPtr s2=stackPtr s1+8 from e2.writes.2,sp1,BitVec.add_assoc]; rfl
  have m2 : s2.external=s.external := (e2.agrees.external (by simp [Component.Covers])).trans m1
  have bx2 : s2.regValue .rbx=memLoad s.external (stackPtr s+152) 64 := by
    have h := e2.writes.1
    change s2.regValue .rbx=memLoad s1.external (stackPtr s1) 64 at h
    simpa only [sp1,m1] using h
  obtain ⟨s4,a4,r4,e4⟩ := (pop_r64_effect_step 0x114235 0x5d (by decide) (by decide)).advances r2
    ((code.mono (codeRange_slice_subset 0x11422d epilogueBytes 8 1)).of_external_eq m2)
    ⟨e2.rip,by rw [sp2]; exact (pre.readable 160 (by simp)).of_external_eq m2⟩
    (boundary_ne_program hout (inProgram_of_textOffset 0x14236 (by decide)))
  change (popR64Effect 0x114235 1 5 s2).Holds s2 s4 at e4
  have sp4 : stackPtr s4=stackPtr s+168 := by
    rw [show stackPtr s4=stackPtr s2+8 from e4.writes.2,sp2,BitVec.add_assoc]; rfl
  have m4 : s4.external=s.external := (e4.agrees.external (by simp [Component.Covers])).trans m2
  have bp4 : s4.regValue .rbp=memLoad s.external (stackPtr s+160) 64 := by
    have h := e4.writes.1
    change s4.regValue .rbp=memLoad s2.external (stackPtr s2) 64 at h
    simpa only [sp2,m2] using h
  have top4 : stackTop s4=memLoad s.external (stackPtr s+168) 64 := by
    change memLoad s4.external (stackPtr s4) 64=_
    rw [m4,sp4]
  obtain ⟨s5,a5,r5,e5⟩ := (ret_effect_step 0x114236).advances r4
    ((code.mono (codeRange_slice_subset 0x11422d epilogueBytes 9 1)).of_external_eq m4)
    ⟨⟨e4.rip,by rw [sp4]; exact (pre.readable 168 (by simp)).of_external_eq m4⟩,
      by change (stackTop s4).toNat<2^32; rw [top4]; exact P256.Proofs.Program.inProgram_low pre.ret⟩
    (by change stackTop s4≠boundary.rip; rw [top4]; exact boundary_ne_program hout pre.ret)
  have hag := ((e1.agrees.trans e2.agrees).trans e4.agrees).trans e5.agrees
  refine ⟨s5,((a1.trans a2).trans a4).trans a5,r5,hag.mono ?_,e5.rip.trans top4,?_,?_,?_⟩
  · simp
  · rw [show stackPtr s5=stackPtr s4+8 from e5.writes,sp4,BitVec.add_assoc]; rfl
  · exact (e4.agrees.trans e5.agrees).read (r := 3) (n := 64) (by simp) |>.trans bx2
  · exact e5.agrees.read (r := 5) (n := 64) (by simp) |>.trans bp4

end P256.Proofs.Field.Inverse
