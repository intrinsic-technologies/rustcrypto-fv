import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group22_step : GroupStep b_l121930_22 b_l121930_23 group22 registers22 registers23 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers22, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group22, Values.Program.part06, Values.Program.part07, List.cons_append, List.nil_append] registers23 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group23_step : GroupStep b_l121930_23 b_l121930_24 group23 registers23 registers24 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers23, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 44 (by decide)
  compression_group [group23, Values.Program.part07, List.cons_append, List.nil_append] registers24 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group24_step : GroupStep b_l121930_24 b_l121930_25 group24 registers24 registers25 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers24, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group24, Values.Program.part07, List.cons_append, List.nil_append] registers25 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group25_step : GroupStep b_l121930_25 b_l121930_26 group25 registers25 registers26 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers25, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 48 (by decide)
  compression_group [group25, Values.Program.part07, Values.Program.part08, List.cons_append, List.nil_append] registers26 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group26_step : GroupStep b_l121930_26 b_l121930_27 group26 registers26 registers27 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers26, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group26, Values.Program.part08, List.cons_append, List.nil_append] registers27 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group27_step : GroupStep b_l121930_27 b_l121930_28 group27 registers27 registers28 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers27, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 52 (by decide)
  compression_group [group27, Values.Program.part08, List.cons_append, List.nil_append] registers28 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group28_step : GroupStep b_l121930_28 b_l121930_29 group28 registers28 registers29 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers28, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group28, Values.Program.part08, Values.Program.part09, List.cons_append, List.nil_append] registers29 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group29_step : GroupStep b_l121930_29 b_l121930_30 group29 registers29 registers30 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers29, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 56 (by decide)
  compression_group [group29, Values.Program.part09, List.cons_append, List.nil_append] registers30 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group30_step : GroupStep b_l121930_30 b_l121930_31 group30 registers30 registers31 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers30, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group30, Values.Program.part09, List.cons_append, List.nil_append] registers31 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group31_step : GroupStep b_l121930_31 b_l121930_32 group31 registers31 registers32 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers31, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have ip : memLoad m (ctx.stackPointer + 24) 64 = ctx.inputPointer := load64_24.trans ptr
  have word := inputWords 60 (by decide)
  compression_group [group31, Values.Program.part09, List.cons_append, List.nil_append] registers32 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp, ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← word]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group32_step : GroupStep b_l121930_32 b_l121930_33 group32 registers32 registers33 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers32, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_56 := stackWords.load64 56 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_56
  compression_group [group32, Values.Program.part10, List.cons_append, List.nil_append] registers33 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_56]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group33_step : GroupStep b_l121930_33 b_l121930_34 group33 registers33 registers34 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers33, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_8 := stackWords 8 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_8
  have load64_80 := stackWords.load64 80 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_80
  compression_group [group33, Values.Program.part10, List.cons_append, List.nil_append, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false] registers34 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_8, ← load64_80]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group34_step : GroupStep b_l121930_34 b_l121930_35 group34 registers34 registers35 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers34, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group34, Values.Program.part10, List.cons_append, List.nil_append] registers35 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group35_step : GroupStep b_l121930_35 b_l121930_36 group35 registers35 registers36 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers35, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_104 := stackWords.load64 104 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_104
  compression_group [group35, Values.Program.part10, Values.Program.part11, List.cons_append, List.nil_append] registers36 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_104]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group36_step : GroupStep b_l121930_36 b_l121930_37 group36 registers36 registers37 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers36, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_12 := stackWords 12 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_12
  compression_group [group36, Values.Program.part11, List.cons_append, List.nil_append] registers37 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_12]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group37_step : GroupStep b_l121930_37 b_l121930_38 group37 registers37 registers38 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers37, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group37, Values.Program.part11, List.cons_append, List.nil_append] registers38 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group38_step : GroupStep b_l121930_38 b_l121930_39 group38 registers38 registers39 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers38, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_72 := stackWords.load64 72 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_72
  have load32_96 := stackWords 96 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_96
  compression_group [group38, Values.Program.part11, Values.Program.part12, List.cons_append, List.nil_append] registers39 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_72, ← load32_96]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group39_step : GroupStep b_l121930_39 b_l121930_40 group39 registers39 registers40 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers39, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_8 := stackWords 8 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_8
  have load32_12 := stackWords 12 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_12
  have load64_88 := stackWords.load64 88 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_88
  compression_group [group39, Values.Program.part12, List.cons_append, List.nil_append] registers40 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_8, ← load32_12, ← load64_88]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group40_step : GroupStep b_l121930_40 b_l121930_41 group40 registers40 registers41 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers40, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_0
  have load32_4 := stackWords 4 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_4
  have load32_16 := stackWords 16 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_16
  have load32_52 := stackWords 52 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_52
  compression_group [group40, Values.Program.part12, List.cons_append, List.nil_append] registers41 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0, ← load32_4, ← load32_16, ← load32_52]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group41_step : GroupStep b_l121930_41 b_l121930_42 group41 registers41 registers42 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers41, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_80 := stackWords.load64 80 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_80
  have load32_100 := stackWords 100 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_100
  compression_group [group41, Values.Program.part12, Values.Program.part13, List.cons_append, List.nil_append, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false] registers42 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_80, ← load32_100]

def range22 := group22 ++ group23 ++ group24 ++ group25 ++ group26 ++ group27 ++ group28 ++ group29 ++ group30 ++ group31 ++ group32 ++ group33 ++ group34 ++ group35 ++ group36 ++ group37 ++ group38 ++ group39 ++ group40 ++ group41

theorem range22_step : GroupStep b_l121930_22 b_l121930_42 range22 registers22 registers42 spilledInput :=
  (group22_step.chain
    (group23_step.chain
    (group24_step.chain
    (group25_step.chain
    (group26_step.chain
    (group27_step.chain
    (group28_step.chain
    (group29_step.chain
    (group30_step.chain
    (group31_step.chain
    (group32_step.chain
    (group33_step.chain
    (group34_step.chain
    (group35_step.chain
    (group36_step.chain
    (group37_step.chain
    (group38_step.chain
    (group39_step.chain
    (group40_step.chain
    group41_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
