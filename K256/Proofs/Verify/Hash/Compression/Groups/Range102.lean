import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group102_step : GroupStep b_l121930_102 b_l121930_103 group102 registers102 registers103 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers102, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_88 := stackWords 88 (by decide) (by decide)
  compression_group [group102, Values.Program.part31, Values.Program.part32, List.cons_append, List.nil_append] registers103 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_88]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group103_step : GroupStep b_l121930_103 b_l121930_104 group103 registers103 registers104 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers103, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_20 := stackWords 20 (by decide) (by decide)
  compression_group [group103, Values.Program.part32, List.cons_append, List.nil_append] registers104 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_20]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group104_step : GroupStep b_l121930_104 b_l121930_105 group104 registers104 registers105 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers104, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group104, Values.Program.part32, List.cons_append, List.nil_append] registers105 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group105_step : GroupStep b_l121930_105 b_l121930_106 group105 registers105 registers106 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers105, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_16 := stackWords 16 (by decide) (by decide)
  have load32_72 := stackWords 72 (by decide) (by decide)
  compression_group [group105, Values.Program.part32, Values.Program.part33, List.cons_append, List.nil_append] registers106 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_16, ← load32_72]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group106_step : GroupStep b_l121930_106 b_l121930_107 group106 registers106 registers107 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers106, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group106, Values.Program.part33, List.cons_append, List.nil_append] registers107 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group107_step : GroupStep b_l121930_107 b_l121930_108 group107 registers107 registers108 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers107, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group107, Values.Program.part33, List.cons_append, List.nil_append] registers108 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group108_step : GroupStep b_l121930_108 b_l121930_109 group108 registers108 registers109 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers108, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_36 := stackWords 36 (by decide) (by decide)
  have load32_112 := stackWords 112 (by decide) (by decide)
  compression_group [group108, Values.Program.part33, Values.Program.part34, List.cons_append, List.nil_append] registers109 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_36, ← load32_112]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group109_step : GroupStep b_l121930_109 b_l121930_110 group109 registers109 registers110 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers109, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group109, Values.Program.part34, List.cons_append, List.nil_append] registers110 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group110_step : GroupStep b_l121930_110 b_l121930_111 group110 registers110 registers111 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers110, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_4 := stackWords 4 (by decide) (by decide)
  compression_group [group110, Values.Program.part34, List.cons_append, List.nil_append] registers111 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_4]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group111_step : GroupStep b_l121930_111 b_l121930_112 group111 registers111 registers112 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers111, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp only [BitVec.add_zero] at load32_0
  compression_group [group111, Values.Program.part34, List.cons_append, List.nil_append] registers112 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group112_step : GroupStep b_l121930_112 b_l121930_113 group112 registers112 registers113 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers112, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group112, Values.Program.part35, List.cons_append, List.nil_append] registers113 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group113_step : GroupStep b_l121930_113 b_l121930_114 group113 registers113 registers114 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers113, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_64 := stackWords 64 (by decide) (by decide)
  compression_group [group113, Values.Program.part35, List.cons_append, List.nil_append] registers114 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_64]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group114_step : GroupStep b_l121930_114 b_l121930_115 group114 registers114 registers115 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers114, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_128 := stackWords 128 (by decide) (by decide)
  compression_group [group114, Values.Program.part35, List.cons_append, List.nil_append] registers115 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_128]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group115_step : GroupStep b_l121930_115 b_l121930_116 group115 registers115 registers116 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers115, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group115, Values.Program.part35, Values.Program.part36, List.cons_append, List.nil_append] registers116 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group116_step : GroupStep b_l121930_116 b_l121930_117 group116 registers116 registers117 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers116, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_40 := stackWords.load64 40 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_40
  compression_group [group116, Values.Program.part36, List.cons_append, List.nil_append] registers117 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_40]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group117_step : GroupStep b_l121930_117 b_l121930_118 group117 registers117 registers118 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers117, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_88 := stackWords 88 (by decide) (by decide)
  compression_group [group117, Values.Program.part36, List.cons_append, List.nil_append] registers118 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_88]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group118_step : GroupStep b_l121930_118 b_l121930_119 group118 registers118 registers119 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers118, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group118, Values.Program.part36, Values.Program.part37, List.cons_append, List.nil_append] registers119 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group119_step : GroupStep b_l121930_119 b_l121930_120 group119 registers119 registers120 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers119, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_12 := stackWords 12 (by decide) (by decide)
  compression_group [group119, Values.Program.part37, List.cons_append, List.nil_append] registers120 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_12]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group120_step : GroupStep b_l121930_120 b_l121930_121 group120 registers120 registers121 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers120, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group120, Values.Program.part37, List.cons_append, List.nil_append] registers121 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group121_step : GroupStep b_l121930_121 b_l121930_122 group121 registers121 registers122 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers121, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_8 := stackWords 8 (by decide) (by decide)
  compression_group [group121, Values.Program.part37, Values.Program.part38, List.cons_append, List.nil_append] registers122 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_8]

def range102 := group102 ++ group103 ++ group104 ++ group105 ++ group106 ++ group107 ++ group108 ++ group109 ++ group110 ++ group111 ++ group112 ++ group113 ++ group114 ++ group115 ++ group116 ++ group117 ++ group118 ++ group119 ++ group120 ++ group121

theorem range102_step : GroupStep b_l121930_102 b_l121930_122 range102 registers102 registers122 spilledInput :=
  (group102_step.chain
    (group103_step.chain
    (group104_step.chain
    (group105_step.chain
    (group106_step.chain
    (group107_step.chain
    (group108_step.chain
    (group109_step.chain
    (group110_step.chain
    (group111_step.chain
    (group112_step.chain
    (group113_step.chain
    (group114_step.chain
    (group115_step.chain
    (group116_step.chain
    (group117_step.chain
    (group118_step.chain
    (group119_step.chain
    (group120_step.chain
    group121_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
