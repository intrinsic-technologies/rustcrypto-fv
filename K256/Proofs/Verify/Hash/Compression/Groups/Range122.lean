import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group122_step : GroupStep b_l121930_122 b_l121930_123 group122 registers122 registers123 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers122, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_36 := stackWords 36 (by decide) (by decide)
  compression_group [group122, Values.Program.part38, List.cons_append, List.nil_append] registers123 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_36]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group123_step : GroupStep b_l121930_123 b_l121930_124 group123 registers123 registers124 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers123, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group123, Values.Program.part38, List.cons_append, List.nil_append] registers124 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group124_step : GroupStep b_l121930_124 b_l121930_125 group124 registers124 registers125 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers124, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_80 := stackWords 80 (by decide) (by decide)
  compression_group [group124, Values.Program.part38, Values.Program.part39, List.cons_append, List.nil_append] registers125 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_80]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group125_step : GroupStep b_l121930_125 b_l121930_126 group125 registers125 registers126 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers125, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_4 := stackWords 4 (by decide) (by decide)
  compression_group [group125, Values.Program.part39, List.cons_append, List.nil_append] registers126 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_4]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group126_step : GroupStep b_l121930_126 b_l121930_127 group126 registers126 registers127 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers126, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group126, Values.Program.part39, List.cons_append, List.nil_append] registers127 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group127_step : GroupStep b_l121930_127 b_l121930_128 group127 registers127 registers128 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers127, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_56 := stackWords.load64 56 (by decide) (by decide)
  have load32_120 := stackWords 120 (by decide) (by decide)
  compression_group [group127, Values.Program.part39, List.cons_append, List.nil_append] registers128 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_56, ← load32_120]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group128_step : GroupStep b_l121930_128 b_l121930_129 group128 registers128 registers129 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers128, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_64 := stackWords 64 (by decide) (by decide)
  compression_group [group128, Values.Program.part40, List.cons_append, List.nil_append] registers129 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_64]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group129_step : GroupStep b_l121930_129 b_l121930_130 group129 registers129 registers130 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers129, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group129, Values.Program.part40, List.cons_append, List.nil_append] registers130 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group130_step : GroupStep b_l121930_130 b_l121930_131 group130 registers130 registers131 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers130, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_20 := stackWords 20 (by decide) (by decide)
  have load64_40 := stackWords.load64 40 (by decide) (by decide)
  compression_group [group130, Values.Program.part40, List.cons_append, List.nil_append,
      Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false] registers131 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_20, ← load64_40]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group131_step : GroupStep b_l121930_131 b_l121930_132 group131 registers131 registers132 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers131, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group131, Values.Program.part40, Values.Program.part41, List.cons_append, List.nil_append] registers132 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group132_step : GroupStep b_l121930_132 b_l121930_133 group132 registers132 registers133 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers132, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_112 := stackWords 112 (by decide) (by decide)
  compression_group [group132, Values.Program.part41, List.cons_append, List.nil_append] registers133 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_112]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group133_step : GroupStep b_l121930_133 b_l121930_134 group133 registers133 registers134 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers133, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_12 := stackWords 12 (by decide) (by decide)
  have load32_72 := stackWords 72 (by decide) (by decide)
  compression_group [group133, Values.Program.part41, List.cons_append, List.nil_append] registers134 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_12, ← load32_72]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group134_step : GroupStep b_l121930_134 b_l121930_135 group134 registers134 registers135 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers134, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_56 := stackWords.load64 56 (by decide) (by decide)
  compression_group [group134, Values.Program.part41, Values.Program.part42, List.cons_append, List.nil_append] registers135 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_56]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group135_step : GroupStep b_l121930_135 b_l121930_136 group135 registers135 registers136 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers135, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_8 := stackWords 8 (by decide) (by decide)
  compression_group [group135, Values.Program.part42, List.cons_append, List.nil_append] registers136 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_8]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group136_step : GroupStep b_l121930_136 b_l121930_137 group136 registers136 registers137 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers136, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group136, Values.Program.part42, List.cons_append, List.nil_append] registers137 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group137_step : GroupStep b_l121930_137 b_l121930_138 group137 registers137 registers138 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers137, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_80 := stackWords 80 (by decide) (by decide)
  have load32_104 := stackWords 104 (by decide) (by decide)
  compression_group [group137, Values.Program.part42, Values.Program.part43, List.cons_append, List.nil_append] registers138 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_80, ← load32_104]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group138_step : GroupStep b_l121930_138 b_l121930_139 group138 registers138 registers139 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers138, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group138, Values.Program.part43, List.cons_append, List.nil_append] registers139 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group139_step : GroupStep b_l121930_139 b_l121930_140 group139 registers139 registers140 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers139, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_128 := stackWords 128 (by decide) (by decide)
  compression_group [group139, Values.Program.part43, List.cons_append, List.nil_append] registers140 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_128]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group140_step : GroupStep b_l121930_140 b_l121930_141 group140 registers140 registers141 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers140, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_120 := stackWords 120 (by decide) (by decide)
  compression_group [group140, Values.Program.part43, Values.Program.part44, List.cons_append, List.nil_append] registers141 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_120]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group141_step : GroupStep b_l121930_141 b_l121930_142 group141 registers141 registers142 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers141, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_88 := stackWords 88 (by decide) (by decide)
  compression_group [group141, Values.Program.part44, List.cons_append, List.nil_append] registers142 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11,
      ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_88]

def range122 := group122 ++ group123 ++ group124 ++ group125 ++ group126 ++ group127 ++ group128 ++ group129 ++ group130 ++ group131 ++ group132 ++ group133 ++ group134 ++ group135 ++ group136 ++ group137 ++ group138 ++ group139 ++ group140 ++ group141

theorem range122_step : GroupStep b_l121930_122 b_l121930_142 range122 registers122 registers142 spilledInput :=
  (group122_step.chain
    (group123_step.chain
    (group124_step.chain
    (group125_step.chain
    (group126_step.chain
    (group127_step.chain
    (group128_step.chain
    (group129_step.chain
    (group130_step.chain
    (group131_step.chain
    (group132_step.chain
    (group133_step.chain
    (group134_step.chain
    (group135_step.chain
    (group136_step.chain
    (group137_step.chain
    (group138_step.chain
    (group139_step.chain
    (group140_step.chain
    group141_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
