import P256.Proofs.Field.Montgomery.Reduction.Blocks


set_option autoImplicit false

open P256.Proofs.Program (programSections_fetchByte_of_mem programText_slice)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def registerClobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip]

def scratchComponents (s : RamState) : List Component :=
  registerClobbers ++ [.mem (stackPtr s) 8]

structure BodyPre (s : RamState) : Prop where
  rip : s.RIP = 0x113c1b
  low : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8
  high : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 2 : Operand 64).read s + i) 8
  scratch : MemWritable s (stackPtr s) 8
  avoids : ∀ a, (Component.mem (stackPtr s) 8).Covers a → ¬ InProgram a

def BodyTrace (s t : RamState) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10,
    (firstSetupEffect s).Holds s s1 ∧
    (firstCarryEffect s1).Holds s1 s2 ∧
    (firstHighEffect s2).Holds s2 s3 ∧
    (secondRoundEffect s3).Holds s3 s4 ∧
    (thirdRoundEffect s4).Holds s4 s5 ∧
    (fourthRoundEffect s5).Holds s5 s6 ∧
    (borrowLowEffect s6).Holds s6 s7 ∧
    (borrowMiddleEffect s7).Holds s7 s8 ∧
    (borrowHighEffect s8).Holds s8 s9 ∧
    (borrowTopEffect s9).Holds s9 s10 ∧
    (correctionEffect s10).Holds s10 t

theorem scratch_codeIn {s t : RamState} (pre : BodyPre s)
    (h : AgreesExcept (scratchComponents s) s t)
    (code : CodeIn Extracted.programSections.toCodeMap s) :
    CodeIn Extracted.programSections.toCodeMap t := by
  apply CodeIn.of_agreesExcept h ?_ code
  intro x hx c hc hv
  simp only [scratchComponents, registerClobbers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact hv.elim
  exact pre.avoids _ hv ⟨x.2, programSections_fetchByte_of_mem hx⟩

theorem body_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s)
    (code : CodeIn Extracted.programSections.toCodeMap s) (pre : BodyPre s) :
    ∃ t, (∃ fuel, Advances boundary fuel s t) ∧ ReadyToStep t ∧
      t.RIP = 0x113dea ∧ AgreesExcept (scratchComponents s) s t ∧ BodyTrace s t := by
  have pre1 : FirstSetupPre s := by
    refine ⟨pre.rip, ?_⟩
    exact pre.low 0 (by simp)
  obtain ⟨fuel1, s1, run1, ready1, _, e1⟩ :=
    first_setup boundary hout s ready
      (programText_slice code 0x13c1b firstSetupBytes (by decide) (by decide +kernel)) pre1
  have frame1 : AgreesExcept (scratchComponents s) s s1 := by
    apply e1.agrees.mono
    simp [scratchComponents, registerClobbers, firstSetupEffect, Effect.components]
  have code1 := scratch_codeIn pre frame1 code
  have m1 : s1.external = s.external := (e1.agrees.external (by simp [firstSetupEffect, Effect.components, Component.Covers]))
  have low1 : ((Operand.reg 6 : Operand 64).read s1) = ((Operand.reg 6 : Operand 64).read s) := (e1.agrees.read (by simp [firstSetupEffect, Effect.components]))
  have high1 : ((Operand.reg 1 : Operand 64).read s1) = ((Operand.reg 2 : Operand 64).read s) := e1.writes.1
  have sp1 : stackPtr s1 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s1 = (Operand.reg 4 : Operand 64).read s
    exact frame1.read (by simp [scratchComponents, registerClobbers])
  have writable1 : MemWritable s1 (stackPtr s) 8 := MemWritable.of_holds e1 pre.scratch
  have pre2 : FirstCarryPre s1 := by
    refine ⟨e1.rip, ?_⟩
    rw [low1]
    exact (pre.low 8 (by simp)).of_external_eq m1
  obtain ⟨fuel2, s2, run2, ready2, _, e2⟩ :=
    first_carry boundary hout s1 ready1
      (programText_slice code1 0x13c32 firstCarryBytes (by decide) (by decide +kernel)) pre2
  have frame2 : AgreesExcept (scratchComponents s) s s2 := by
    apply (frame1.trans e2.agrees).mono
    simp [scratchComponents, registerClobbers, firstCarryEffect, Effect.components]
  have code2 := scratch_codeIn pre frame2 code
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [firstCarryEffect, Effect.components, Component.Covers])).trans m1
  have low2 : ((Operand.reg 6 : Operand 64).read s2) = ((Operand.reg 6 : Operand 64).read s) := (e2.agrees.read (by simp [firstCarryEffect, Effect.components])).trans low1
  have high2 : ((Operand.reg 1 : Operand 64).read s2) = ((Operand.reg 2 : Operand 64).read s) := (e2.agrees.read (by simp [firstCarryEffect, Effect.components])).trans high1
  have sp2 : stackPtr s2 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s2 = (Operand.reg 4 : Operand 64).read s
    exact frame2.read (by simp [scratchComponents, registerClobbers])
  have writable2 : MemWritable s2 (stackPtr s) 8 := MemWritable.of_holds e2 writable1
  have pre3 : FirstHighPre s2 := by
    refine ⟨e2.rip, ?_, ?_, ?_⟩
    · rw [low2]
      exact (pre.low 24 (by simp)).of_external_eq m2
    · rw [low2]
      exact (pre.low 16 (by simp)).of_external_eq m2
    · rw [high2]
      exact (pre.high 8 (by simp)).of_external_eq m2
  obtain ⟨fuel3, s3, run3, ready3, _, e3⟩ :=
    firstHigh_correct boundary hout s2 ready2
      (programText_slice code2 0x13c43 firstHighBytes (by decide) (by decide +kernel)) pre3
  have frame3 : AgreesExcept (scratchComponents s) s s3 := by
    apply (frame2.trans e3.agrees).mono
    simp [scratchComponents, registerClobbers, firstHighEffect, Effect.components]
  have code3 := scratch_codeIn pre frame3 code
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [firstHighEffect, Effect.components, Component.Covers])).trans m2
  have high3 : ((Operand.reg 1 : Operand 64).read s3) = ((Operand.reg 2 : Operand 64).read s) := (e3.agrees.read (by simp [firstHighEffect, Effect.components])).trans high2
  have sp3 : stackPtr s3 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s3 = (Operand.reg 4 : Operand 64).read s
    exact frame3.read (by simp [scratchComponents, registerClobbers])
  have writable3 : MemWritable s3 (stackPtr s) 8 := MemWritable.of_holds e3 writable2
  have pre4 : SecondRoundPre s3 := by
    refine ⟨e3.rip, ?_⟩
    rw [high3]
    exact (pre.high 0 (by simp)).of_external_eq m3
  obtain ⟨fuel4, s4, run4, ready4, _, e4⟩ :=
    secondRound_correct boundary hout s3 ready3
      (programText_slice code3 0x13c71 secondRoundBytes (by decide) (by decide +kernel)) pre4
  have frame4 : AgreesExcept (scratchComponents s) s s4 := by
    apply (frame3.trans e4.agrees).mono
    simp [scratchComponents, registerClobbers, secondRoundEffect, Effect.components]
  have code4 := scratch_codeIn pre frame4 code
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [secondRoundEffect, Effect.components, Component.Covers])).trans m3
  have high4 : ((Operand.reg 1 : Operand 64).read s4) = ((Operand.reg 2 : Operand 64).read s) := (e4.agrees.read (by simp [secondRoundEffect, Effect.components])).trans high3
  have sp4 : stackPtr s4 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s4 = (Operand.reg 4 : Operand 64).read s
    exact frame4.read (by simp [scratchComponents, registerClobbers])
  have writable4 : MemWritable s4 (stackPtr s) 8 := MemWritable.of_holds e4 writable3
  have pre5 : ThirdRoundPre s4 := by
    refine ⟨e4.rip, ?_⟩
    rw [high4]
    exact (pre.high 16 (by simp)).of_external_eq m4
  obtain ⟨fuel5, s5, run5, ready5, _, e5⟩ :=
    thirdRound_correct boundary hout s4 ready4
      (programText_slice code4 0x13ca7 thirdRoundBytes (by decide) (by decide +kernel)) pre5
  have frame5 : AgreesExcept (scratchComponents s) s s5 := by
    apply (frame4.trans e5.agrees).mono
    simp [scratchComponents, registerClobbers, thirdRoundEffect, Effect.components]
  have code5 := scratch_codeIn pre frame5 code
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [thirdRoundEffect, Effect.components, Component.Covers])).trans m4
  have high5 : ((Operand.reg 1 : Operand 64).read s5) = ((Operand.reg 2 : Operand 64).read s) := (e5.agrees.read (by simp [thirdRoundEffect, Effect.components])).trans high4
  have sp5 : stackPtr s5 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s5 = (Operand.reg 4 : Operand 64).read s
    exact frame5.read (by simp [scratchComponents, registerClobbers])
  have writable5 : MemWritable s5 (stackPtr s) 8 := MemWritable.of_holds e5 writable4
  have pre6 : FourthRoundPre s5 := by
    refine ⟨e5.rip, ?_⟩
    rw [high5]
    exact (pre.high 24 (by simp)).of_external_eq m5
  obtain ⟨fuel6, s6, run6, ready6, _, e6⟩ :=
    fourthRound_correct boundary hout s5 ready5
      (programText_slice code5 0x13ce1 fourthRoundBytes (by decide) (by decide +kernel)) pre6
  have frame6 : AgreesExcept (scratchComponents s) s s6 := by
    apply (frame5.trans e6.agrees).mono
    simp [scratchComponents, registerClobbers, fourthRoundEffect, Effect.components]
  have code6 := scratch_codeIn pre frame6 code
  have m6 : s6.external = s.external := (e6.agrees.external (by simp [fourthRoundEffect, Effect.components, Component.Covers])).trans m5
  have sp6 : stackPtr s6 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s6 = (Operand.reg 4 : Operand 64).read s
    exact frame6.read (by simp [scratchComponents, registerClobbers])
  have writable6 : MemWritable s6 (stackPtr s) 8 := MemWritable.of_holds e6 writable5
  have pre7 : BorrowSlotPre 0x113d10 s6 := by
    refine ⟨e6.rip, ?_, ?_⟩
    · rw [sp6]
      exact writable6
    · rw [sp6]
      exact pre.avoids
  obtain ⟨fuel7, s7, run7, ready7, _, e7⟩ :=
    borrowLow_correct boundary hout s6 ready6
      (programText_slice code6 0x13d10 borrowLowBytes (by decide) (by decide +kernel)) pre7
  have frame7 : AgreesExcept (scratchComponents s) s s7 := by
    apply (frame6.trans e7.agrees).mono
    simp [scratchComponents, registerClobbers, borrowLowEffect, Effect.components, sp6]
  have code7 := scratch_codeIn pre frame7 code
  have sp7 : stackPtr s7 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s7 = (Operand.reg 4 : Operand 64).read s
    exact frame7.read (by simp [scratchComponents, registerClobbers])
  have writable7 : MemWritable s7 (stackPtr s) 8 := MemWritable.of_holds e7 writable6
  have pre8 : BorrowSlotPre 0x113d38 s7 := by
    refine ⟨e7.rip, ?_, ?_⟩
    · rw [sp7]
      exact writable7
    · rw [sp7]
      exact pre.avoids
  obtain ⟨fuel8, s8, run8, ready8, _, e8⟩ :=
    borrowMiddle_correct boundary hout s7 ready7
      (programText_slice code7 0x13d38 borrowMiddleBytes (by decide) (by decide +kernel)) pre8
  have frame8 : AgreesExcept (scratchComponents s) s s8 := by
    apply (frame7.trans e8.agrees).mono
    simp [scratchComponents, registerClobbers, borrowMiddleEffect, Effect.components, sp7]
  have code8 := scratch_codeIn pre frame8 code
  have sp8 : stackPtr s8 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s8 = (Operand.reg 4 : Operand 64).read s
    exact frame8.read (by simp [scratchComponents, registerClobbers])
  have writable8 : MemWritable s8 (stackPtr s) 8 := MemWritable.of_holds e8 writable7
  have pre9 : BorrowSlotPre 0x113d5a s8 := by
    refine ⟨e8.rip, ?_, ?_⟩
    · rw [sp8]
      exact writable8
    · rw [sp8]
      exact pre.avoids
  obtain ⟨fuel9, s9, run9, ready9, _, e9⟩ :=
    borrowHigh_correct boundary hout s8 ready8
      (programText_slice code8 0x13d5a borrowHighBytes (by decide) (by decide +kernel)) pre9
  have frame9 : AgreesExcept (scratchComponents s) s s9 := by
    apply (frame8.trans e9.agrees).mono
    simp [scratchComponents, registerClobbers, borrowHighEffect, Effect.components, sp8]
  have code9 := scratch_codeIn pre frame9 code
  have sp9 : stackPtr s9 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s9 = (Operand.reg 4 : Operand 64).read s
    exact frame9.read (by simp [scratchComponents, registerClobbers])
  have writable9 : MemWritable s9 (stackPtr s) 8 := MemWritable.of_holds e9 writable8
  have pre10 : BorrowSlotPre 0x113d8f s9 := by
    refine ⟨e9.rip, ?_, ?_⟩
    · rw [sp9]
      exact writable9
    · rw [sp9]
      exact pre.avoids
  obtain ⟨fuel10, s10, run10, ready10, _, e10⟩ :=
    borrowTop_correct boundary hout s9 ready9
      (programText_slice code9 0x13d8f borrowTopBytes (by decide) (by decide +kernel)) pre10
  have frame10 : AgreesExcept (scratchComponents s) s s10 := by
    apply (frame9.trans e10.agrees).mono
    simp [scratchComponents, registerClobbers, borrowTopEffect, Effect.components, sp9]
  have code10 := scratch_codeIn pre frame10 code
  have sp10 : stackPtr s10 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s10 = (Operand.reg 4 : Operand 64).read s
    exact frame10.read (by simp [scratchComponents, registerClobbers])
  have writable10 : MemWritable s10 (stackPtr s) 8 := MemWritable.of_holds e10 writable9
  have pre11 : CorrectionPre s10 := by
    exact ⟨e10.rip⟩
  obtain ⟨fuel11, s11, run11, ready11, _, e11⟩ :=
    correction_correct boundary hout s10 ready10
      (programText_slice code10 0x13dc6 correctionBytes (by decide) (by decide +kernel)) pre11
  have frame11 : AgreesExcept (scratchComponents s) s s11 := by
    apply (frame10.trans e11.agrees).mono
    simp [scratchComponents, registerClobbers, correctionEffect, Effect.components]
  have code11 := scratch_codeIn pre frame11 code
  have sp11 : stackPtr s11 = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read s11 = (Operand.reg 4 : Operand 64).read s
    exact frame11.read (by simp [scratchComponents, registerClobbers])
  have writable11 : MemWritable s11 (stackPtr s) 8 := MemWritable.of_holds e11 writable10
  exact ⟨s11, ⟨fuel1+fuel2+fuel3+fuel4+fuel5+fuel6+fuel7+fuel8+fuel9+fuel10+fuel11, ((((((((((run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11⟩, ready11, e11.rip, frame11, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩

end P256.Proofs.Field.Montgomery.Reduction
