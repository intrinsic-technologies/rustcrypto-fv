import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group82_step : GroupStep b_l121930_82 b_l121930_83 group82 registers82 registers83 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers82, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group82, Values.Program.part25, List.cons_append, List.nil_append] registers83 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group83_step : GroupStep b_l121930_83 b_l121930_84 group83 registers83 registers84 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers83, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_120 := stackWords 120 (by decide) (by decide)
  compression_group [group83, Values.Program.part25, Values.Program.part26, List.cons_append, List.nil_append] registers84 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_120]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group84_step : GroupStep b_l121930_84 b_l121930_85 group84 registers84 registers85 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers84, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_140 := stackWords 140 (by decide) (by decide)
  compression_group [group84, Values.Program.part26, List.cons_append, List.nil_append] registers85 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_140]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group85_step : GroupStep b_l121930_85 b_l121930_86 group85 registers85 registers86 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers85, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group85, Values.Program.part26, List.cons_append, List.nil_append] registers86 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group86_step : GroupStep b_l121930_86 b_l121930_87 group86 registers86 registers87 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers86, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_12 := stackWords 12 (by decide) (by decide)
  have load32_104 := stackWords 104 (by decide) (by decide)
  compression_group [group86, Values.Program.part26, Values.Program.part27, List.cons_append, List.nil_append] registers87 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_12, ← load32_104]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group87_step : GroupStep b_l121930_87 b_l121930_88 group87 registers87 registers88 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers87, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group87, Values.Program.part27, List.cons_append, List.nil_append] registers88 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group88_step : GroupStep b_l121930_88 b_l121930_89 group88 registers88 registers89 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers88, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group88, Values.Program.part27, List.cons_append, List.nil_append] registers89 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group89_step : GroupStep b_l121930_89 b_l121930_90 group89 registers89 registers90 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers89, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_8 := stackWords 8 (by decide) (by decide)
  have load32_20 := stackWords 20 (by decide) (by decide)
  compression_group [group89, Values.Program.part27, Values.Program.part28, List.cons_append, List.nil_append] registers90 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_8, ← load32_20]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group90_step : GroupStep b_l121930_90 b_l121930_91 group90 registers90 registers91 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers90, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group90, Values.Program.part28, List.cons_append, List.nil_append] registers91 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group91_step : GroupStep b_l121930_91 b_l121930_92 group91 registers91 registers92 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers91, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_72 := stackWords 72 (by decide) (by decide)
  compression_group [group91, Values.Program.part28, List.cons_append, List.nil_append] registers92 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_72]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group92_step : GroupStep b_l121930_92 b_l121930_93 group92 registers92 registers93 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers92, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_56 := stackWords 56 (by decide) (by decide)
  compression_group [group92, Values.Program.part28, Values.Program.part29, List.cons_append, List.nil_append] registers93 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_56]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group93_step : GroupStep b_l121930_93 b_l121930_94 group93 registers93 registers94 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers93, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group93, Values.Program.part29, List.cons_append, List.nil_append] registers94 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group94_step : GroupStep b_l121930_94 b_l121930_95 group94 registers94 registers95 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers94, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_112 := stackWords 112 (by decide) (by decide)
  compression_group [group94, Values.Program.part29, List.cons_append, List.nil_append] registers95 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_112]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group95_step : GroupStep b_l121930_95 b_l121930_96 group95 registers95 registers96 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers95, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_80 := stackWords 80 (by decide) (by decide)
  compression_group [group95, Values.Program.part29, List.cons_append, List.nil_append] registers96 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_80]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group96_step : GroupStep b_l121930_96 b_l121930_97 group96 registers96 registers97 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers96, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group96, Values.Program.part30, List.cons_append, List.nil_append] registers97 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group97_step : GroupStep b_l121930_97 b_l121930_98 group97 registers97 registers98 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers97, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at load32_0
  have load32_120 := stackWords 120 (by decide) (by decide)
  compression_group [group97, Values.Program.part30, List.cons_append, List.nil_append] registers98 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0, ← load32_120]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group98_step : GroupStep b_l121930_98 b_l121930_99 group98 registers98 registers99 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers98, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group98, Values.Program.part30, List.cons_append, List.nil_append] registers99 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group99_step : GroupStep b_l121930_99 b_l121930_100 group99 registers99 registers100 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers99, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_128 := stackWords 128 (by decide) (by decide)
  compression_group [group99, Values.Program.part30, Values.Program.part31, List.cons_append, List.nil_append] registers100 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_128]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group100_step : GroupStep b_l121930_100 b_l121930_101 group100 registers100 registers101 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers100, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_104 := stackWords 104 (by decide) (by decide)
  compression_group [group100, Values.Program.part31, List.cons_append, List.nil_append] registers101 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_104]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group101_step : GroupStep b_l121930_101 b_l121930_102 group101 registers101 registers102 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers101, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group101, Values.Program.part31, List.cons_append, List.nil_append] registers102 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

def range82 := group82 ++ group83 ++ group84 ++ group85 ++ group86 ++ group87 ++ group88 ++ group89 ++ group90 ++ group91 ++ group92 ++ group93 ++ group94 ++ group95 ++ group96 ++ group97 ++ group98 ++ group99 ++ group100 ++ group101

theorem range82_step : GroupStep b_l121930_82 b_l121930_102 range82 registers82 registers102 spilledInput :=
  (group82_step.chain
    (group83_step.chain
    (group84_step.chain
    (group85_step.chain
    (group86_step.chain
    (group87_step.chain
    (group88_step.chain
    (group89_step.chain
    (group90_step.chain
    (group91_step.chain
    (group92_step.chain
    (group93_step.chain
    (group94_step.chain
    (group95_step.chain
    (group96_step.chain
    (group97_step.chain
    (group98_step.chain
    (group99_step.chain
    (group100_step.chain
    group101_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
