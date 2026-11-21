import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Tail.Instructions
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem epilogue_test_advances [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002f1)
    (hStack0 : MemReadable s (stackPtr s) 8)
    (hStack8 : MemReadable s (stackPtr s + 8) 8)
    (hStack16 : MemReadable s (stackPtr s + 16) 8)
    (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (Operand.reg 6 : Operand 16).read s = 0 then 0x100300 else 0x1002fa) ∧
      t.regValue .rbx = (Operand.mem (stackPtr s) : Operand 64).read s ∧
      t.regValue .r14 = (Operand.mem (stackPtr s + 8) : Operand 64).read s ∧
      t.regValue .rbp = (Operand.mem (stackPtr s + 16) : Operand 64).read s ∧
      stackPtr t = stackPtr s + 24 ∧
      AgreesExcept [.reg 3, .reg 14, .reg 5, .reg 4, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ := (test_si_si_effect_step 0x1002f1).advances hReady
    (program_text_slice hCode 0x2f1 3 (by decide +kernel)) hRip
    (outsideMixed_ne (pc := 0x1002f4) hOutside (by decide) (by decide))
  have c1 := e1.codeIn (Effect.Avoids.of_noMem (by
    simp [testSiEffect, Effect.components, Component.Covers]) _) hCode
  have f1 : AgreesExcept [.flags, .rip] s s1 := e1.agrees
  have sp1 : stackPtr s1 = stackPtr s := f1.read (n := 64) (r := 4) (by simp)
  have mem1 : s1.external = s.external := f1.external (by simp [Component.Covers])
  have rd2 : MemReadable s1 (stackPtr s1) 8 := by
    rw [sp1]
    exact hStack0.of_external_eq mem1
  obtain ⟨s2, a2, r2, e2⟩ := (pop_r64_effect_step 0x1002f4 0x5b (by decide) (by decide)).advances r1
    (program_text_slice c1 0x2f4 1 (by decide +kernel)) ⟨e1.rip, rd2⟩
    (outsideMixed_ne (pc := 0x1002f5) hOutside (by decide) (by decide))
  change (popR64Effect 0x1002f4 1 3 s1).Holds s1 s2 at e2
  have c2 := e2.codeIn (popR64Effect_avoids _ _ _ _ _) c1
  have sp2 : stackPtr s2 = stackPtr s + 8 := by
    have h := e2.writes.2
    change stackPtr s2 = stackPtr s1 + 8 at h
    simpa only [sp1, BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 from rfl, show (16 : BitVec 64) + 8 = 24 from rfl] using h
  have mem2 : s2.external = s.external :=
    (e2.agrees.external (by simp [popR64Effect, Effect.components, Component.Covers])).trans mem1
  have val2 : s2.regValue .rbx =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
    have h := e2.writes.1
    change s2.regValue .rbx = memLoad s1.external (stackPtr s1) 64 at h
    rw [sp1, mem1] at h
    exact h
  have rd3 : MemReadable s2 (stackPtr s2) 8 := by
    rw [sp2]
    exact hStack8.of_external_eq mem2
  obtain ⟨s3, a3, r3, e3⟩ := (pop_r64_rex_effect_step 0x1002f5 0x41 0x5e (by simp [RexPrefix]) (by decide) (by decide)).advances r2
    (program_text_slice c2 0x2f5 2 (by decide +kernel)) ⟨e2.rip, rd3⟩
    (outsideMixed_ne (pc := 0x1002f7) hOutside (by decide) (by decide))
  change (popR64Effect 0x1002f5 2 14 s2).Holds s2 s3 at e3
  have c3 := e3.codeIn (popR64Effect_avoids _ _ _ _ _) c2
  have sp3 : stackPtr s3 = stackPtr s + 16 := by
    have h := e3.writes.2
    change stackPtr s3 = stackPtr s2 + 8 at h
    simpa only [sp2, BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 from rfl, show (16 : BitVec 64) + 8 = 24 from rfl] using h
  have mem3 : s3.external = s.external :=
    (e3.agrees.external (by simp [popR64Effect, Effect.components, Component.Covers])).trans mem2
  have val3 : s3.regValue .r14 =
      (Operand.mem (stackPtr s + 8) : Operand 64).read s := by
    have h := e3.writes.1
    change s3.regValue .r14 = memLoad s2.external (stackPtr s2) 64 at h
    rw [sp2, mem2] at h
    exact h
  have rd4 : MemReadable s3 (stackPtr s3) 8 := by
    rw [sp3]
    exact hStack16.of_external_eq mem3
  obtain ⟨s4, a4, r4, e4⟩ := (pop_r64_effect_step 0x1002f7 0x5d (by decide) (by decide)).advances r3
    (program_text_slice c3 0x2f7 1 (by decide +kernel)) ⟨e3.rip, rd4⟩
    (outsideMixed_ne (pc := 0x1002f8) hOutside (by decide) (by decide))
  change (popR64Effect 0x1002f7 1 5 s3).Holds s3 s4 at e4
  have c4 := e4.codeIn (popR64Effect_avoids _ _ _ _ _) c3
  have sp4 : stackPtr s4 = stackPtr s + 24 := by
    have h := e4.writes.2
    change stackPtr s4 = stackPtr s3 + 8 at h
    simpa only [sp3, BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 from rfl, show (16 : BitVec 64) + 8 = 24 from rfl] using h
  have mem4 : s4.external = s.external :=
    (e4.agrees.external (by simp [popR64Effect, Effect.components, Component.Covers])).trans mem3
  have val4 : s4.regValue .rbp =
      (Operand.mem (stackPtr s + 16) : Operand 64).read s := by
    have h := e4.writes.1
    change s4.regValue .rbp = memLoad s3.external (stackPtr s3) 64 at h
    rw [sp3, mem3] at h
    exact h
  have hz : (StatusFlags.ofRFLAGS s4.RFLAGS).ZF =
      ((Operand.reg 6 : Operand 16).read s == 0) := by
    rw [(e2.agrees.trans (e3.agrees.trans e4.agrees)).rflags (by simp) (by simp)]
    exact e1.flags.2.2.2.1
  have next : (jccEffect 0x1002f8 2 4 ((0x06 : BitVec 8).signExtend 64) s4).rip =
      (if (Operand.reg 6 : Operand 16).read s = 0 then 0x100300 else 0x1002fa) := by
    change (if (StatusFlags.ofRFLAGS s4.RFLAGS).ZF then (0x100300 : BitVec 64)
      else 0x1002fa) = _
    rw [hz]
    simp only [beq_iff_eq]
  obtain ⟨t, a5, r5, e5⟩ := (jcc_rel8_effect_step 0x1002f8 4 0x06).advances r4
    (program_text_slice c4 0x2f8 2 (by decide +kernel))
    ⟨e4.rip, fun _ ↦ by decide⟩ (by
      rw [next]; split <;> exact outsideMixed_ne hOutside (by decide) (by decide))
  refine ⟨t, a1.trans (a2.trans (a3.trans (a4.trans a5))), r5,
    e5.agrees.codeIn (by simp [jccEffect, branchEffect, Effect.components, Component.Covers]) c4, e5.rip.trans next, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((e3.agrees.trans e4.agrees).trans e5.agrees).read (n := 64) (r := 3) (by simp [popR64Effect, jccEffect, branchEffect, Effect.components]) |>.trans val2
  · exact (e4.agrees.trans e5.agrees).read (n := 64) (r := 14) (by simp [popR64Effect, jccEffect, branchEffect, Effect.components]) |>.trans val3
  · exact e5.agrees.read (n := 64) (r := 5) (by simp [ jccEffect, branchEffect, Effect.components]) |>.trans val4
  · exact e5.agrees.read (n := 64) (r := 4) (by simp [ jccEffect, branchEffect, Effect.components]) |>.trans sp4
  · exact ((((f1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).mono
      (by simp [popR64Effect, jccEffect, branchEffect, Effect.components])
theorem epilogue_advances [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002ec)
    (hStack0 : MemReadable s (stackPtr s) 8)
    (hStack8 : MemReadable s (stackPtr s + 8) 8)
    (hStack16 : MemReadable s (stackPtr s + 16) 8)
    (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (Operand.reg 6 : Operand 16).read s = 0 then 0x100300 else 0x1002fa) ∧
      t.regValue .rax = 2 ∧
      t.regValue .rbx = (Operand.mem (stackPtr s) : Operand 64).read s ∧
      t.regValue .r14 = (Operand.mem (stackPtr s + 8) : Operand 64).read s ∧
      t.regValue .rbp = (Operand.mem (stackPtr s + 16) : Operand 64).read s ∧
      stackPtr t = stackPtr s + 24 ∧
      AgreesExcept [.reg 0, .reg 3, .reg 14, .reg 5, .reg 4, .flags, .rip] s t := by
  obtain ⟨a, ra, readyA, ea⟩ := (mov_r32_imm32_effect_step 0x1002ec 0xb8 (by decide) 2).advances
    hReady (program_text_slice hCode 0x2ec 5 (by decide +kernel)) hRip
    (outsideMixed_ne (pc := 0x1002f1) hOutside (by decide) (by decide))
  have fa : AgreesExcept [.reg 0, .rip] s a := ea.agrees
  have ca := fa.codeIn (by simp [Component.Covers]) hCode
  have spA : stackPtr a = stackPtr s := fa.read (n := 64) (r := 4) (by simp)
  have memA := fa.external (by simp [Component.Covers])
  obtain ⟨t, rt, readyT, codeT, ripT, bxT, r14T, bpT, spT, ft⟩ := epilogue_test_advances
    readyA ca ea.rip
    (by rw [spA]; exact hStack0.of_external_eq memA)
    (by rw [spA]; exact hStack8.of_external_eq memA)
    (by rw [spA]; exact hStack16.of_external_eq memA) hOutside
  refine ⟨t, ra.trans rt, readyT, codeT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fa.read (n := 16) (r := 6) (by simp)] at ripT
    exact ripT
  · exact (ft.read (n := 64) (r := 0) (by simp)).trans ea.writes
  · simpa only [spA, Operand.read, memA] using bxT
  · simpa only [spA, Operand.read, memA] using r14T
  · simpa only [spA, Operand.read, memA] using bpT
  · simpa only [spA] using spT
  · exact (fa.trans ft).mono (by simp [or_left_comm, or_comm])
end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
