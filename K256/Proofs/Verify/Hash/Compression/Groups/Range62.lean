import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group62_step : GroupStep b_l121930_62 b_l121930_63 group62 registers62 registers63 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers62, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_16 := stackWords 16 (by decide) (by decide)
  have load32_96 := stackWords 96 (by decide) (by decide)
  compression_group [group62, Values.Program.part19, List.cons_append, List.nil_append] registers63 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_16, ← load32_96]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group63_step : GroupStep b_l121930_63 b_l121930_64 group63 registers63 registers64 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers63, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group63, Values.Program.part19, List.cons_append, List.nil_append] registers64 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group64_step : GroupStep b_l121930_64 b_l121930_65 group64 registers64 registers65 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers64, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_36 := stackWords 36 (by decide) (by decide)
  compression_group [group64, Values.Program.part20, List.cons_append, List.nil_append] registers65 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_36]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group65_step : GroupStep b_l121930_65 b_l121930_66 group65 registers65 registers66 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers65, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_52 := stackWords 52 (by decide) (by decide)
  compression_group [group65, Values.Program.part20, List.cons_append, List.nil_append] registers66 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_52]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group66_step : GroupStep b_l121930_66 b_l121930_67 group66 registers66 registers67 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers66, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group66, Values.Program.part20, List.cons_append, List.nil_append] registers67 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group67_step : GroupStep b_l121930_67 b_l121930_68 group67 registers67 registers68 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers67, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp only [BitVec.add_zero] at load32_0
  have load32_4 := stackWords 4 (by decide) (by decide)
  compression_group [group67, Values.Program.part20, Values.Program.part21, List.cons_append, List.nil_append] registers68 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0, ← load32_4]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group68_step : GroupStep b_l121930_68 b_l121930_69 group68 registers68 registers69 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers68, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group68, Values.Program.part21, List.cons_append, List.nil_append] registers69 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group69_step : GroupStep b_l121930_69 b_l121930_70 group69 registers69 registers70 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers69, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group69, Values.Program.part21, List.cons_append, List.nil_append] registers70 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group70_step : GroupStep b_l121930_70 b_l121930_71 group70 registers70 registers71 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers70, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_136 := stackWords 136 (by decide) (by decide)
  have load32_140 := stackWords 140 (by decide) (by decide)
  compression_group [group70, Values.Program.part21, Values.Program.part22, List.cons_append, List.nil_append] registers71 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_136, ← load32_140]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group71_step : GroupStep b_l121930_71 b_l121930_72 group71 registers71 registers72 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers71, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_40 := stackWords.load64 40 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_40
  compression_group [group71, Values.Program.part22, List.cons_append, List.nil_append] registers72 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_40]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group72_step : GroupStep b_l121930_72 b_l121930_73 group72 registers72 registers73 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers72, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_12 := stackWords 12 (by decide) (by decide)
  compression_group [group72, Values.Program.part22, List.cons_append, List.nil_append] registers73 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_12]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group73_step : GroupStep b_l121930_73 b_l121930_74 group73 registers73 registers74 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers73, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_100 := stackWords 100 (by decide) (by decide)
  compression_group [group73, Values.Program.part22, Values.Program.part23, List.cons_append, List.nil_append] registers74 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_100]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group74_step : GroupStep b_l121930_74 b_l121930_75 group74 registers74 registers75 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers74, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group74, Values.Program.part23, List.cons_append, List.nil_append] registers75 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group75_step : GroupStep b_l121930_75 b_l121930_76 group75 registers75 registers76 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers75, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_8 := stackWords 8 (by decide) (by decide)
  have load32_16 := stackWords 16 (by decide) (by decide)
  compression_group [group75, Values.Program.part23, List.cons_append, List.nil_append] registers76 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_8, ← load32_16]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group76_step : GroupStep b_l121930_76 b_l121930_77 group76 registers76 registers77 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers76, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group76, Values.Program.part23, Values.Program.part24, List.cons_append, List.nil_append] registers77 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group77_step : GroupStep b_l121930_77 b_l121930_78 group77 registers77 registers78 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers77, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group77, Values.Program.part24, List.cons_append, List.nil_append] registers78 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group78_step : GroupStep b_l121930_78 b_l121930_79 group78 registers78 registers79 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers78, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_36 := stackWords 36 (by decide) (by decide)
  have load32_56 := stackWords 56 (by decide) (by decide)
  compression_group [group78, Values.Program.part24, List.cons_append, List.nil_append] registers79 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_36, ← load32_56]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group79_step : GroupStep b_l121930_79 b_l121930_80 group79 registers79 registers80 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers79, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group79, Values.Program.part24, List.cons_append, List.nil_append] registers80 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group80_step : GroupStep b_l121930_80 b_l121930_81 group80 registers80 registers81 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers80, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group80, Values.Program.part25, List.cons_append, List.nil_append] registers81 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group81_step : GroupStep b_l121930_81 b_l121930_82 group81 registers81 registers82 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers81, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_4 := stackWords 4 (by decide) (by decide)
  have load32_80 := stackWords 80 (by decide) (by decide)
  compression_group [group81, Values.Program.part25, List.cons_append, List.nil_append] registers82 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_4, ← load32_80]

def range62 := group62 ++ group63 ++ group64 ++ group65 ++ group66 ++ group67 ++ group68 ++ group69 ++ group70 ++ group71 ++ group72 ++ group73 ++ group74 ++ group75 ++ group76 ++ group77 ++ group78 ++ group79 ++ group80 ++ group81

theorem range62_step : GroupStep b_l121930_62 b_l121930_82 range62 registers62 registers82 spilledInput :=
  (group62_step.chain
    (group63_step.chain
    (group64_step.chain
    (group65_step.chain
    (group66_step.chain
    (group67_step.chain
    (group68_step.chain
    (group69_step.chain
    (group70_step.chain
    (group71_step.chain
    (group72_step.chain
    (group73_step.chain
    (group74_step.chain
    (group75_step.chain
    (group76_step.chain
    (group77_step.chain
    (group78_step.chain
    (group79_step.chain
    (group80_step.chain
    group81_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
