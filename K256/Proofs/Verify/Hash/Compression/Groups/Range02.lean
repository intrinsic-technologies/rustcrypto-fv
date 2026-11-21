import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group02_step : GroupStep b_l121930_2 b_l121930_3 group02 registers02 registers03 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers02, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group02, Values.Program.part00, List.cons_append, List.nil_append] registers03 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group03_step : GroupStep b_l121930_3 b_l121930_4 group03 registers03 registers04 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers03, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group03, Values.Program.part00, Values.Program.part01, List.cons_append, List.nil_append] registers04 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group04_step : GroupStep b_l121930_4 b_l121930_5 group04 registers04 registers05 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers04, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group04, Values.Program.part01, List.cons_append, List.nil_append] registers05 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group05_step : GroupStep b_l121930_5 b_l121930_6 group05 registers05 registers06 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers05, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 8 (by decide)
  compression_group [group05, Values.Program.part01, List.cons_append, List.nil_append] registers06 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group06_step : GroupStep b_l121930_6 b_l121930_7 group06 registers06 registers07 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers06, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group06, Values.Program.part01, Values.Program.part02, List.cons_append, List.nil_append] registers07 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group07_step : GroupStep b_l121930_7 b_l121930_8 group07 registers07 registers08 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers07, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 12 (by decide)
  compression_group [group07, Values.Program.part02, List.cons_append, List.nil_append] registers08 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group08_step : GroupStep b_l121930_8 b_l121930_9 group08 registers08 registers09 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers08, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group08, Values.Program.part02, List.cons_append, List.nil_append] registers09 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group09_step : GroupStep b_l121930_9 b_l121930_10 group09 registers09 registers10 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers09, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 16 (by decide)
  compression_group [group09, Values.Program.part02, Values.Program.part03, List.cons_append, List.nil_append] registers10 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group10_step : GroupStep b_l121930_10 b_l121930_11 group10 registers10 registers11 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers10, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group10, Values.Program.part03, List.cons_append, List.nil_append] registers11 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group11_step : GroupStep b_l121930_11 b_l121930_12 group11 registers11 registers12 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers11, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 20 (by decide)
  compression_group [group11, Values.Program.part03, List.cons_append, List.nil_append] registers12 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group12_step : GroupStep b_l121930_12 b_l121930_13 group12 registers12 registers13 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers12, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group12, Values.Program.part03, Values.Program.part04, List.cons_append, List.nil_append] registers13 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group13_step : GroupStep b_l121930_13 b_l121930_14 group13 registers13 registers14 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers13, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 24 (by decide)
  compression_group [group13, Values.Program.part04, List.cons_append, List.nil_append] registers14 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group14_step : GroupStep b_l121930_14 b_l121930_15 group14 registers14 registers15 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers14, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group14, Values.Program.part04, List.cons_append, List.nil_append] registers15 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group15_step : GroupStep b_l121930_15 b_l121930_16 group15 registers15 registers16 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers15, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 28 (by decide)
  compression_group [group15, Values.Program.part04, List.cons_append, List.nil_append] registers16 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group16_step : GroupStep b_l121930_16 b_l121930_17 group16 registers16 registers17 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers16, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group16, Values.Program.part05, List.cons_append, List.nil_append] registers17 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group17_step : GroupStep b_l121930_17 b_l121930_18 group17 registers17 registers18 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers17, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 32 (by decide)
  compression_group [group17, Values.Program.part05, List.cons_append, List.nil_append] registers18 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group18_step : GroupStep b_l121930_18 b_l121930_19 group18 registers18 registers19 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers18, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group18, Values.Program.part05, List.cons_append, List.nil_append] registers19 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group19_step : GroupStep b_l121930_19 b_l121930_20 group19 registers19 registers20 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers19, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 36 (by decide)
  compression_group [group19, Values.Program.part05, Values.Program.part06, List.cons_append, List.nil_append] registers20 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group20_step : GroupStep b_l121930_20 b_l121930_21 group20 registers20 registers21 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers20, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group20, Values.Program.part06, List.cons_append, List.nil_append] registers21 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group21_step : GroupStep b_l121930_21 b_l121930_22 group21 registers21 registers22 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers21, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 40 (by decide)
  compression_group [group21, Values.Program.part06, List.cons_append, List.nil_append] registers22 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

def range02 := group02 ++ group03 ++ group04 ++ group05 ++ group06 ++ group07 ++ group08 ++ group09 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 ++ group16 ++ group17 ++ group18 ++ group19 ++ group20 ++ group21

theorem range02_step : GroupStep b_l121930_2 b_l121930_22 range02 registers02 registers22 spilledInput :=
  (group02_step.chain
    (group03_step.chain
    (group04_step.chain
    (group05_step.chain
    (group06_step.chain
    (group07_step.chain
    (group08_step.chain
    (group09_step.chain
    (group10_step.chain
    (group11_step.chain
    (group12_step.chain
    (group13_step.chain
    (group14_step.chain
    (group15_step.chain
    (group16_step.chain
    (group17_step.chain
    (group18_step.chain
    (group19_step.chain
    (group20_step.chain
    group21_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
