import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.State
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.PrepareX
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.PrepareY
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.PrepareZ
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.PrepareCopy

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectX5Site : StackCallSite 0x114380 32 128 :=
  { codeOffset := 0x4713
    disp := 0xfc68
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x14380 (by decide)
    layout := ⟨368,344,248,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    stack := rfl
    outputSaved := by decide }

def selectY5Site : StackCallSite 0x114380 32 128 :=
  { codeOffset := 0x472e
    disp := 0xfc4d
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x14380 (by decide)
    layout := ⟨368,312,216,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    stack := rfl
    outputSaved := by decide }

def selectZ5Site : StackCallSite 0x114380 32 128 :=
  { codeOffset := 0x4747
    disp := 0xfc34
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x14380 (by decide)
    layout := ⟨368,280,184,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    stack := rfl
    outputSaved := by decide }

set_option maxHeartbeats 1600000 in
theorem round5 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {digit : BitVec 8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (input : TableAt s (s.regValue .rsi) table) (state : RoundState s t table digit 5) :
    ∃ fuel u, Advances boundary fuel t u ∧ RoundState s u table digit 6 := by
  let selected := decide (digitMagnitude digit = 6)
  let point := scanPrefix table (digitMagnitude digit) 5
  have bp0 : t.regValue .rbp = stackPtr s - 280 := state.rbp
  have r140 : t.regValue .r14 = stackPtr s - 344 := state.r14
  have r130 : t.regValue .r13 = s.regValue .rsi := state.r13 (by decide)
  have r120 : t.regValue .r12 = stackPtr s - 248 := state.r12 (by decide)
  have digit0 := state.digit
  have output0 := state.output
  have magnitude0 := state.magnitude
  have point0 : ProjectiveAt t (stackPtr s - 344) point := state.value
  obtain ⟨n1,t1,run1,f1,e1,mem1⟩ := registers state.toFrameState 0x46f2
    (choiceBytes 6) (choiceEffect 0x1046f2 6) (by decide) (by decide +kernel)
    (choice_prefix boundary 0x1046f2 6 (by
      intro k hk
      apply boundary_ne_program pre.outerBoundary
      have h := inProgram_of_textOffset (0x46f2+k) (by omega)
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress, BitVec.reduceAdd] at h
      exact h))
    (by intro v; simp [choiceEffect, Effect.components, Component.Covers])
    (by intro v; simp [choiceEffect, Effect.components]) state.rip
  have choice1 : t1.regValue .rdi = if selected then 1 else 0 := by
    have h := e1.writes
    change t1.regValue .rdi = (if (t.regValue .r15).setWidth 8 = 6#8 then 1 else 0) at h
    rw [magnitude0] at h
    exact h.trans (digit_choice digit (5 : Fin 8))
  have rbp1 := (e1.agrees.read (n := 64) (r := 5) (by simp [choiceEffect, Effect.components])).trans bp0
  change t1.regValue .rbp = _ at rbp1
  have r141 := (e1.agrees.read (n := 64) (r := 14) (by simp [choiceEffect, Effect.components])).trans r140
  change t1.regValue .r14 = _ at r141
  have r131 := (e1.agrees.read (n := 64) (r := 13) (by simp [choiceEffect, Effect.components])).trans r130
  change t1.regValue .r13 = _ at r131
  have r121 := (e1.agrees.read (n := 64) (r := 12) (by simp [choiceEffect, Effect.components])).trans r120
  change t1.regValue .r12 = _ at r121
  have magnitude1 : (t1.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) :=
    (congrArg (BitVec.setWidth 8) (e1.agrees.read (n := 64) (r := 15) (by simp [choiceEffect, Effect.components]))).trans magnitude0
  have point1 := projective_mem point0 mem1
  have digit1 : (Operand.mem (stackPtr s - 348) : Operand 32).read t1 = (s.regValue .rdx).setWidth 32 := by
    change memLoad t1.external _ _ = _
    rw [mem1]; exact digit0
  have output1 : (Operand.mem (stackPtr s - 152) : Operand 64).read t1 = s.regValue .rdi := by
    change memLoad t1.external _ _ = _
    rw [mem1]; exact output0
  obtain ⟨n2,t2,run2,f2,rip2,rax2,regs2,mem2⟩ := choice_call pre f1
    0x46fc 0x1496f (by decide) (by decide +kernel) (by decide +kernel) e1.rip
  have choice2 : t2.regValue .rax = if selected then 1 else 0 := by
    rw [rax2, choice1]; cases selected <;> rfl
  have rbp2 := (regs2 .rbp (by simp)).trans rbp1
  have r142 := (regs2 .r14 (by simp)).trans r141
  have r132 := (regs2 .r13 (by simp)).trans r131
  have r122 := (regs2 .r12 (by simp)).trans r121
  have magnitude2 : (t2.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) := by
    rw [regs2 .r15 (by simp)]; exact magnitude1
  have point2 := point1.of_bytes_eq (mem2 344 96 (by decide) (by decide))
  have digit2 := (read_bytes (mem2 348 4 (by decide) (by decide))).trans digit1
  have output2 := (read_bytes (mem2 152 8 (by decide) (by decide))).trans output1
  obtain ⟨n3,t3,run3,f3,e3,mem3⟩ := registers f2 0x4701
    (prepareX5Bytes) (prepareX5Effect) (by decide) (by decide +kernel)
    (prepareX5_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareX5Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareX5Effect, Effect.components]) rip2
  have w3 := e3.writes
  simp only [prepareX5Effect, Write.AllHold] at w3
  have rbp3 := (e3.agrees.read (n := 64) (r := 5) (by simp [prepareX5Effect, Effect.components])).trans rbp2
  change t3.regValue .rbp = _ at rbp3
  have r143 := (e3.agrees.read (n := 64) (r := 14) (by simp [prepareX5Effect, Effect.components])).trans r142
  change t3.regValue .r14 = _ at r143
  have r133 := (e3.agrees.read (n := 64) (r := 13) (by simp [prepareX5Effect, Effect.components])).trans r132
  change t3.regValue .r13 = _ at r133
  have r123 := (e3.agrees.read (n := 64) (r := 12) (by simp [prepareX5Effect, Effect.components])).trans r122
  change t3.regValue .r12 = _ at r123
  have magnitude3 : (t3.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) :=
    (congrArg (BitVec.setWidth 8) (e3.agrees.read (n := 64) (r := 15) (by simp [prepareX5Effect, Effect.components]))).trans magnitude2
  have w3_2 := w3.1
  change t3.regValue .rdx = _ at w3_2
  have w3_3 := w3.2.1
  change t3.regValue .rbx = _ at w3_3
  have w3_7 := w3.2.2.1
  change t3.regValue .rdi = _ at w3_7
  have w3_6 := w3.2.2.2.1
  change t3.regValue .rsi = _ at w3_6
  have w3_1 := w3.2.2.2.2
  change t3.regValue .rcx = _ at w3_1
  have rbx3 : t3.regValue .rbx = if selected then 1 else 0 := by
    change t3.regValue .rbx = _ at w3_3
    rw [choice2] at w3_3
    exact w3_3.trans (by cases selected <;> rfl)
  have point3 := projective_mem point2 mem3
  have digit3 : (Operand.mem (stackPtr s - 348) : Operand 32).read t3 = (s.regValue .rdx).setWidth 32 := by
    change memLoad t3.external _ _ = _
    rw [mem3]; exact digit2
  have output3 : (Operand.mem (stackPtr s - 152) : Operand 64).read t3 = s.regValue .rdi := by
    change memLoad t3.external _ _ = _
    rw [mem3]; exact output2
  have dst3 : t3.regValue .rdi = stackPtr s - 248 := by
    exact w3_7.trans r122
  have src3 : t3.regValue .rsi = stackPtr s - 344 := by
    exact w3_6.trans r142
  have right3 : t3.regValue .rdx = s.regValue .rsi + 480 := by
    simpa [r132] using w3_2
  have choice3 : t3.regValue .rcx = if selected then 1 else 0 := by
    rw [choice2] at w3_1
    exact w3_1.trans (by cases selected <;> rfl)
  have left3 : MontgomeryAt t3 (stackPtr s - 344) point.x := by
    have h := point3.1
    exact h
  have table3 : MontgomeryAt s (s.regValue .rsi + 480) (table (5 : Fin 8)).x := by
    have h := (input (5 : Fin 8)).1
    change MontgomeryAt s (s.regValue .rsi + 480#64) (table (5 : Fin 8)).x at h
    try simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  obtain ⟨n4,t4,run4,f4,rip4,value4,regs4,mem4⟩ :=
    select_call pre f3 selectX5Site 480 (by decide) e3.rip
      src3 right3 dst3 left3 table3 choice3
  change MontgomeryAt t4 (stackPtr s - 248) _ at value4
  have rbp4 := (regs4 .rbp (by simp)).trans rbp3
  have r144 := (regs4 .r14 (by simp)).trans r143
  have r134 := (regs4 .r13 (by simp)).trans r133
  have r124 := (regs4 .r12 (by simp)).trans r123
  have rbx4 := (regs4 .rbx (by simp)).trans rbx3
  have magnitude4 : (t4.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) := by
    rw [regs4 .r15 (by simp)]; exact magnitude3
  have point4 := point3.of_bytes_eq (mem4 344 96 (by decide) (by decide) (by decide))
  have digit4 := (read_bytes (mem4 348 4 (by decide) (by decide) (by decide))).trans digit3
  have output4 := (read_bytes (mem4 152 8 (by decide) (by decide) (by decide))).trans output3
  obtain ⟨n5,t5,run5,f5,e5,mem5⟩ := registers f4 0x4718
    (prepareY5Bytes) (prepareY5Effect) (by decide) (by decide +kernel)
    (prepareY5_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareY5Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareY5Effect, Effect.components]) rip4
  have w5 := e5.writes
  simp only [prepareY5Effect, Write.AllHold] at w5
  have rbp5 := (e5.agrees.read (n := 64) (r := 5) (by simp [prepareY5Effect, Effect.components])).trans rbp4
  change t5.regValue .rbp = _ at rbp5
  have r145 := (e5.agrees.read (n := 64) (r := 14) (by simp [prepareY5Effect, Effect.components])).trans r144
  change t5.regValue .r14 = _ at r145
  have r135 := (e5.agrees.read (n := 64) (r := 13) (by simp [prepareY5Effect, Effect.components])).trans r134
  change t5.regValue .r13 = _ at r135
  have r125 := (e5.agrees.read (n := 64) (r := 12) (by simp [prepareY5Effect, Effect.components])).trans r124
  change t5.regValue .r12 = _ at r125
  have rbx5 := (e5.agrees.read (n := 64) (r := 3) (by simp [prepareY5Effect, Effect.components])).trans rbx4
  change t5.regValue .rbx = _ at rbx5
  have magnitude5 : (t5.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) :=
    (congrArg (BitVec.setWidth 8) (e5.agrees.read (n := 64) (r := 15) (by simp [prepareY5Effect, Effect.components]))).trans magnitude4
  have w5_2 := w5.1
  change t5.regValue .rdx = _ at w5_2
  have w5_7 := w5.2.1
  change t5.regValue .rdi = _ at w5_7
  have w5_6 := w5.2.2.1
  change t5.regValue .rsi = _ at w5_6
  have w5_1 := w5.2.2.2
  change t5.regValue .rcx = _ at w5_1
  have point5 := projective_mem point4 mem5
  have digit5 : (Operand.mem (stackPtr s - 348) : Operand 32).read t5 = (s.regValue .rdx).setWidth 32 := by
    change memLoad t5.external _ _ = _
    rw [mem5]; exact digit4
  have output5 : (Operand.mem (stackPtr s - 152) : Operand 64).read t5 = s.regValue .rdi := by
    change memLoad t5.external _ _ = _
    rw [mem5]; exact output4
  have x5 := montgomery_mem value4 mem5
  have dst5 : t5.regValue .rdi = stackPtr s - 216 := by
    exact w5_7.trans (stack_address f4.rsp (by decide))
  have src5 : t5.regValue .rsi = stackPtr s - 312 := by
    exact w5_6.trans (stack_address f4.rsp (by decide))
  have right5 : t5.regValue .rdx = s.regValue .rsi + 512 := by
    simpa [r134] using w5_2
  have choice5 : t5.regValue .rcx = if selected then 1 else 0 := by
    rw [rbx4] at w5_1
    exact w5_1.trans (by cases selected <;> rfl)
  have left5 : MontgomeryAt t5 (stackPtr s - 312) point.y := by
    have h := point5.2.1
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have table5 : MontgomeryAt s (s.regValue .rsi + 512) (table (5 : Fin 8)).y := by
    have h := (input (5 : Fin 8)).2.1
    change MontgomeryAt s (s.regValue .rsi + 480#64 + 32#64) (table (5 : Fin 8)).y at h
    try simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  obtain ⟨n6,t6,run6,f6,rip6,value6,regs6,mem6⟩ :=
    select_call pre f5 selectY5Site 512 (by decide) e5.rip
      src5 right5 dst5 left5 table5 choice5
  change MontgomeryAt t6 (stackPtr s - 216) _ at value6
  have rbp6 := (regs6 .rbp (by simp)).trans rbp5
  have r146 := (regs6 .r14 (by simp)).trans r145
  have r136 := (regs6 .r13 (by simp)).trans r135
  have r126 := (regs6 .r12 (by simp)).trans r125
  have rbx6 := (regs6 .rbx (by simp)).trans rbx5
  have magnitude6 : (t6.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) := by
    rw [regs6 .r15 (by simp)]; exact magnitude5
  have point6 := point5.of_bytes_eq (mem6 344 96 (by decide) (by decide) (by decide))
  have digit6 := (read_bytes (mem6 348 4 (by decide) (by decide) (by decide))).trans digit5
  have output6 := (read_bytes (mem6 152 8 (by decide) (by decide) (by decide))).trans output5
  have x6 := Field.MontgomeryAt.of_bytes_eq x5 (mem6 248 32 (by decide) (by decide) (by decide))
  obtain ⟨n7,t7,run7,f7,e7,mem7⟩ := registers f6 0x4733
    (prepareZ5Bytes) (prepareZ5Effect) (by decide) (by decide +kernel)
    (prepareZ5_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareZ5Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareZ5Effect, Effect.components]) rip6
  have w7 := e7.writes
  simp only [prepareZ5Effect, Write.AllHold] at w7
  have rbp7 := (e7.agrees.read (n := 64) (r := 5) (by simp [prepareZ5Effect, Effect.components])).trans rbp6
  change t7.regValue .rbp = _ at rbp7
  have r147 := (e7.agrees.read (n := 64) (r := 14) (by simp [prepareZ5Effect, Effect.components])).trans r146
  change t7.regValue .r14 = _ at r147
  have r137 := (e7.agrees.read (n := 64) (r := 13) (by simp [prepareZ5Effect, Effect.components])).trans r136
  change t7.regValue .r13 = _ at r137
  have r127 := (e7.agrees.read (n := 64) (r := 12) (by simp [prepareZ5Effect, Effect.components])).trans r126
  change t7.regValue .r12 = _ at r127
  have rbx7 := (e7.agrees.read (n := 64) (r := 3) (by simp [prepareZ5Effect, Effect.components])).trans rbx6
  change t7.regValue .rbx = _ at rbx7
  have magnitude7 : (t7.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) :=
    (congrArg (BitVec.setWidth 8) (e7.agrees.read (n := 64) (r := 15) (by simp [prepareZ5Effect, Effect.components]))).trans magnitude6
  have w7_2 := w7.1
  change t7.regValue .rdx = _ at w7_2
  have w7_7 := w7.2.1
  change t7.regValue .rdi = _ at w7_7
  have w7_6 := w7.2.2.1
  change t7.regValue .rsi = _ at w7_6
  have w7_1 := w7.2.2.2
  change t7.regValue .rcx = _ at w7_1
  have point7 := projective_mem point6 mem7
  have digit7 : (Operand.mem (stackPtr s - 348) : Operand 32).read t7 = (s.regValue .rdx).setWidth 32 := by
    change memLoad t7.external _ _ = _
    rw [mem7]; exact digit6
  have output7 : (Operand.mem (stackPtr s - 152) : Operand 64).read t7 = s.regValue .rdi := by
    change memLoad t7.external _ _ = _
    rw [mem7]; exact output6
  have x7 := montgomery_mem x6 mem7
  have y7 := montgomery_mem value6 mem7
  have dst7 : t7.regValue .rdi = stackPtr s - 184 := by
    exact w7_7.trans (stack_address f6.rsp (by decide))
  have src7 : t7.regValue .rsi = stackPtr s - 280 := by
    exact w7_6.trans rbp6
  have right7 : t7.regValue .rdx = s.regValue .rsi + 544 := by
    simpa [r136] using w7_2
  have choice7 : t7.regValue .rcx = if selected then 1 else 0 := by
    rw [rbx6] at w7_1
    exact w7_1.trans (by cases selected <;> rfl)
  have left7 : MontgomeryAt t7 (stackPtr s - 280) point.z := by
    have h := point7.2.2
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have table7 : MontgomeryAt s (s.regValue .rsi + 544) (table (5 : Fin 8)).z := by
    have h := (input (5 : Fin 8)).2.2
    change MontgomeryAt s (s.regValue .rsi + 480#64 + 64#64) (table (5 : Fin 8)).z at h
    try simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  obtain ⟨n8,t8,run8,f8,rip8,value8,regs8,mem8⟩ :=
    select_call pre f7 selectZ5Site 544 (by decide) e7.rip
      src7 right7 dst7 left7 table7 choice7
  change MontgomeryAt t8 (stackPtr s - 184) _ at value8
  have rbp8 := (regs8 .rbp (by simp)).trans rbp7
  have r148 := (regs8 .r14 (by simp)).trans r147
  have r138 := (regs8 .r13 (by simp)).trans r137
  have r128 := (regs8 .r12 (by simp)).trans r127
  have rbx8 := (regs8 .rbx (by simp)).trans rbx7
  have magnitude8 : (t8.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) := by
    rw [regs8 .r15 (by simp)]; exact magnitude7
  have point8 := point7.of_bytes_eq (mem8 344 96 (by decide) (by decide) (by decide))
  have digit8 := (read_bytes (mem8 348 4 (by decide) (by decide) (by decide))).trans digit7
  have output8 := (read_bytes (mem8 152 8 (by decide) (by decide) (by decide))).trans output7
  have x8 := Field.MontgomeryAt.of_bytes_eq x7 (mem8 248 32 (by decide) (by decide) (by decide))
  have y8 := Field.MontgomeryAt.of_bytes_eq y7 (mem8 216 32 (by decide) (by decide) (by decide))
  obtain ⟨n9,t9,run9,f9,e9,mem9⟩ := registers f8 0x474c
    (prepareCopy5Bytes) (prepareCopy5Effect) (by decide) (by decide +kernel)
    (prepareCopy5_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareCopy5Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareCopy5Effect, Effect.components]) rip8
  have w9 := e9.writes
  simp only [prepareCopy5Effect, Write.AllHold] at w9
  have rbp9 := (e9.agrees.read (n := 64) (r := 5) (by simp [prepareCopy5Effect, Effect.components])).trans rbp8
  change t9.regValue .rbp = _ at rbp9
  have r149 := (e9.agrees.read (n := 64) (r := 14) (by simp [prepareCopy5Effect, Effect.components])).trans r148
  change t9.regValue .r14 = _ at r149
  have r139 := (e9.agrees.read (n := 64) (r := 13) (by simp [prepareCopy5Effect, Effect.components])).trans r138
  change t9.regValue .r13 = _ at r139
  have r129 := (e9.agrees.read (n := 64) (r := 12) (by simp [prepareCopy5Effect, Effect.components])).trans r128
  change t9.regValue .r12 = _ at r129
  have rbx9 := (e9.agrees.read (n := 64) (r := 3) (by simp [prepareCopy5Effect, Effect.components])).trans rbx8
  change t9.regValue .rbx = _ at rbx9
  have magnitude9 : (t9.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit) :=
    (congrArg (BitVec.setWidth 8) (e9.agrees.read (n := 64) (r := 15) (by simp [prepareCopy5Effect, Effect.components]))).trans magnitude8
  have w9_1 := w9.1
  change t9.regValue .rcx = _ at w9_1
  have w9_7 := w9.2.1
  change t9.regValue .rdi = _ at w9_7
  have w9_6 := w9.2.2
  change t9.regValue .rsi = _ at w9_6
  have point9 := projective_mem point8 mem9
  have digit9 : (Operand.mem (stackPtr s - 348) : Operand 32).read t9 = (s.regValue .rdx).setWidth 32 := by
    change memLoad t9.external _ _ = _
    rw [mem9]; exact digit8
  have output9 : (Operand.mem (stackPtr s - 152) : Operand 64).read t9 = s.regValue .rdi := by
    change memLoad t9.external _ _ = _
    rw [mem9]; exact output8
  have x9 := montgomery_mem x8 mem9
  have y9 := montgomery_mem y8 mem9
  have z9 := montgomery_mem value8 mem9
  have src9 : t9.regValue .rsi = stackPtr s - 248 := w9_6.trans r128
  have dst9 : t9.regValue .rdi = stackPtr s - 344 := w9_7.trans r148
  have selected9 : ProjectiveAt t9 (stackPtr s - 248) (if selected then table (5 : Fin 8) else point) := by
    apply selected_point x9
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using y9
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using z9
  have readable : MemReadable t9 (t9.regValue .rsi) 96 := by
    rw [src9]
    have h := stack_readable pre f9 (offset := 112) (len := 96) (by decide)
    have a : stackPtr t9 + 112 = stackPtr s - 248 := stack_address f9.rsp (by decide)
    exact a ▸ h
  obtain ⟨u,run10,f10,rip10,point10,agr10⟩ := copy_to_stack pre f9
    0x4757 (by decide) (by decide +kernel) e9.rip
    344 (by decide) (by decide) dst9 w9_1 readable
    (stack_sources_disjoint pre (by decide) (by decide) src9 dst9 (by decide))
    (src9 ▸ selected9)
  refine ⟨n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + 12, u, ?_, f10, rip10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10)
  · have h := scanPrefix_step table (digitMagnitude digit) (5 : Fin 8)
    change (if digitMagnitude digit = 6 then table (5 : Fin 8) else point) = scanPrefix table (digitMagnitude digit) 6 at h
    have value : ProjectiveAt u (stackPtr s - 344) (if digitMagnitude digit = 6 then table (5 : Fin 8) else point) := by
      simp only [selected, decide_eq_true_eq] at point10
      exact point10
    exact h ▸ value
  · exact (congrArg (BitVec.setWidth 8) (agr10.read (n := 64) (r := 15) (by simp))).trans magnitude9
  · intro h; exact (agr10.read (n := 64) (r := 13) (by simp)).trans r139
  · exact (agr10.read (n := 64) (r := 5) (by simp)).trans rbp9
  · exact (agr10.read (n := 64) (r := 14) (by simp)).trans r149
  · intro h; exact (agr10.read (n := 64) (r := 12) (by simp)).trans r129
  · apply Eq.trans (read_bytes (t := t9) ?_) digit9
    intro i hi
    apply agr10.byte
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨j,hj,he⟩
    apply OffsetsApart.ne (c₁ := -344) (len₁ := 96) (c₂ := -348) (len₂ := 4)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa [BitVec.sub_eq_add_neg] using he.symm
  · apply Eq.trans (read_bytes (t := t9) ?_) output9
    intro i hi
    apply agr10.byte
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨j,hj,he⟩
    apply OffsetsApart.ne (c₁ := -344) (len₁ := 96) (c₂ := -152) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa [BitVec.sub_eq_add_neg] using he.symm

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
