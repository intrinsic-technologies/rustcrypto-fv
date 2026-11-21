import P256.Proofs.Program.Code
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program
open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure EpiloguePre (s : RamState) : Prop where
  rip : s.RIP = 0x1145c3
  readable : ∀ i ∈ ([544, 552, 560, 568, 576, 584] : List (BitVec 64)),
    MemReadable s (stackPtr s + i) 8
  ret : InProgram (memLoad s.external (stackPtr s + 584) 64)

def epilogueBytes : List UInt8 :=
  [0x48, 0x81, 0xc4, 0x20, 2, 0, 0, 0x5b, 0x41, 0x5c,
    0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3]

theorem epilogue_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1145c3 epilogueBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x145c3 epilogueBytes
    (by decide +kernel) (by decide +kernel)

theorem epilogue [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s)
    (code : CodeIn (codeRange 0x1145c3 epilogueBytes) s) (pre : EpiloguePre s) :
    ∃ u, Advances boundary 7 s u ∧ ReadyToStep u ∧
      AgreesExcept [.reg 3, .reg 12, .reg 14, .reg 15, .reg 5, .reg 4, .flags, .rip] s u ∧
      u.RIP = memLoad s.external (stackPtr s + 584) 64 ∧
      stackPtr u = stackPtr s + 592 ∧
      u.regValue .rbx = memLoad s.external (stackPtr s + 544) 64 ∧
      u.regValue .r12 = memLoad s.external (stackPtr s + 552) 64 ∧
      u.regValue .r14 = memLoad s.external (stackPtr s + 560) 64 ∧
      u.regValue .r15 = memLoad s.external (stackPtr s + 568) 64 ∧
      u.regValue .rbp = memLoad s.external (stackPtr s + 576) 64 := by
  obtain ⟨s1, a1, r1, e1⟩ := (add_r64_imm32_effect_step 0x1145c3 0x48 0xc4 544
    (by simp [RexWPrefix]) rfl rfl).advances ready (code.mono
      (codeRange_slice_subset 0x1145c3 epilogueBytes 0 7)) pre.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x145ca (by decide)))
  change (addR64Imm32Effect 0x1145c3 4 544 s).Holds s s1 at e1
  have sp1 : stackPtr s1 = stackPtr s + 544 := e1.writes
  have m1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  obtain ⟨s2, a2, r2, e2⟩ :=
    (pop_register_effect_step 0x1145ca 3 (by decide)).advances r1
      ((code.mono (codeRange_slice_subset 0x1145c3 epilogueBytes 7 1)).of_external_eq m1)
      ⟨e1.rip, by rw [sp1]; exact (pre.readable 544 (by simp)).of_external_eq m1⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x145cb (by decide)))
  change (popR64Effect 0x1145ca 1 3 s1).Holds s1 s2 at e2
  have sp2 : stackPtr s2 = stackPtr s + 552 := by
    rw [show stackPtr s2 = stackPtr s1 + 8 from e2.writes.2, sp1, BitVec.add_assoc]
    rfl
  have m2 : s2.external = s.external :=
    (e2.agrees.external (by simp [Component.Covers])).trans m1
  have v2 : s2.regValue .rbx = memLoad s.external (stackPtr s + 544) 64 := by
    have h : s2.regValue .rbx = memLoad s1.external (stackPtr s1) 64 := e2.writes.1
    simpa only [sp1, m1] using h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (pop_register_effect_step 0x1145cb 12 (by decide)).advances r2
      ((code.mono (codeRange_slice_subset 0x1145c3 epilogueBytes 8 2)).of_external_eq m2)
      ⟨e2.rip, by rw [sp2]; exact (pre.readable 552 (by simp)).of_external_eq m2⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x145cd (by decide)))
  change (popR64Effect 0x1145cb 2 12 s2).Holds s2 s3 at e3
  have sp3 : stackPtr s3 = stackPtr s + 560 := by
    rw [show stackPtr s3 = stackPtr s2 + 8 from e3.writes.2, sp2, BitVec.add_assoc]
    rfl
  have m3 : s3.external = s.external :=
    (e3.agrees.external (by simp [Component.Covers])).trans m2
  have v3 : s3.regValue .r12 = memLoad s.external (stackPtr s + 552) 64 := by
    have h : s3.regValue .r12 = memLoad s2.external (stackPtr s2) 64 := e3.writes.1
    simpa only [sp2, m2] using h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (pop_register_effect_step 0x1145cd 14 (by decide)).advances r3
      ((code.mono (codeRange_slice_subset 0x1145c3 epilogueBytes 10 2)).of_external_eq m3)
      ⟨e3.rip, by rw [sp3]; exact (pre.readable 560 (by simp)).of_external_eq m3⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x145cf (by decide)))
  change (popR64Effect 0x1145cd 2 14 s3).Holds s3 s4 at e4
  have sp4 : stackPtr s4 = stackPtr s + 568 := by
    rw [show stackPtr s4 = stackPtr s3 + 8 from e4.writes.2, sp3, BitVec.add_assoc]
    rfl
  have m4 : s4.external = s.external :=
    (e4.agrees.external (by simp [Component.Covers])).trans m3
  have v4 : s4.regValue .r14 = memLoad s.external (stackPtr s + 560) 64 := by
    have h : s4.regValue .r14 = memLoad s3.external (stackPtr s3) 64 := e4.writes.1
    simpa only [sp3, m3] using h
  obtain ⟨s5, a5, r5, e5⟩ :=
    (pop_register_effect_step 0x1145cf 15 (by decide)).advances r4
      ((code.mono (codeRange_slice_subset 0x1145c3 epilogueBytes 12 2)).of_external_eq m4)
      ⟨e4.rip, by rw [sp4]; exact (pre.readable 568 (by simp)).of_external_eq m4⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x145d1 (by decide)))
  change (popR64Effect 0x1145cf 2 15 s4).Holds s4 s5 at e5
  have sp5 : stackPtr s5 = stackPtr s + 576 := by
    rw [show stackPtr s5 = stackPtr s4 + 8 from e5.writes.2, sp4, BitVec.add_assoc]
    rfl
  have m5 : s5.external = s.external :=
    (e5.agrees.external (by simp [Component.Covers])).trans m4
  have v5 : s5.regValue .r15 = memLoad s.external (stackPtr s + 568) 64 := by
    have h : s5.regValue .r15 = memLoad s4.external (stackPtr s4) 64 := e5.writes.1
    simpa only [sp4, m4] using h
  obtain ⟨s6, a6, r6, e6⟩ :=
    (pop_register_effect_step 0x1145d1 5 (by decide)).advances r5
      ((code.mono (codeRange_slice_subset 0x1145c3 epilogueBytes 14 1)).of_external_eq m5)
      ⟨e5.rip, by rw [sp5]; exact (pre.readable 576 (by simp)).of_external_eq m5⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x145d2 (by decide)))
  change (popR64Effect 0x1145d1 1 5 s5).Holds s5 s6 at e6
  have sp6 : stackPtr s6 = stackPtr s + 584 := by
    rw [show stackPtr s6 = stackPtr s5 + 8 from e6.writes.2, sp5, BitVec.add_assoc]
    rfl
  have m6 : s6.external = s.external :=
    (e6.agrees.external (by simp [Component.Covers])).trans m5
  have v6 : s6.regValue .rbp = memLoad s.external (stackPtr s + 576) 64 := by
    have h : s6.regValue .rbp = memLoad s5.external (stackPtr s5) 64 := e6.writes.1
    simpa only [sp5, m5] using h
  have top : stackTop s6 = memLoad s.external (stackPtr s + 584) 64 := by
    change memLoad s6.external (stackPtr s6) 64 = _
    rw [m6, sp6]
  obtain ⟨s7, a7, r7, e7⟩ := (ret_effect_step 0x1145d2).advances r6
    ((code.mono (codeRange_slice_subset 0x1145c3 epilogueBytes 15 1)).of_external_eq m6)
    ⟨⟨e6.rip, by rw [sp6]; exact (pre.readable 584 (by simp)).of_external_eq m6⟩,
      by change (stackTop s6).toNat < 2^32; rw [top]; exact inProgram_low pre.ret⟩
    (by change stackTop s6 ≠ boundary.rip; rw [top]; exact boundary_ne_program hout pre.ret)
  have agrees := (((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans
    e5.agrees).trans e6.agrees).trans e7.agrees
  refine ⟨s7, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7,
    r7, agrees.mono ?_, e7.rip.trans top, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [show stackPtr s7 = stackPtr s6 + 8 from e7.writes, sp6, BitVec.add_assoc]
    rfl
  · exact (((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).read (r := 3) (n := 64) (by simp)).trans v2
  · exact ((((e4.agrees.trans e5.agrees).trans e6.agrees).trans e7.agrees).read (r := 12) (n := 64) (by simp)).trans v3
  · exact (((e5.agrees.trans e6.agrees).trans e7.agrees).read (r := 14) (n := 64) (by simp)).trans v4
  · exact ((e6.agrees.trans e7.agrees).read (r := 15) (n := 64) (by simp)).trans v5
  · exact (e7.agrees.read (r := 5) (n := 64) (by simp)).trans v6

end P256.Proofs.Sec1.SquareRoot
