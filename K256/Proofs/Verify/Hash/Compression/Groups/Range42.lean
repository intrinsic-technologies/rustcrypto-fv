import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group42_step : GroupStep b_l121930_42 b_l121930_43 group42 registers42 registers43 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers42, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_40 := stackWords 40 (by decide) (by decide)
  have load32_64 := stackWords 64 (by decide) (by decide)
  compression_group [group42, Values.Program.part13, List.cons_append, List.nil_append] registers43 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_40, ← load32_64]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group43_step : GroupStep b_l121930_43 b_l121930_44 group43 registers43 registers44 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers43, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_36 := stackWords 36 (by decide) (by decide)
  compression_group [group43, Values.Program.part13, List.cons_append, List.nil_append] registers44 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_36]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group44_step : GroupStep b_l121930_44 b_l121930_45 group44 registers44 registers45 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers44, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp only [BitVec.add_zero] at load32_0
  have load32_8 := stackWords 8 (by decide) (by decide)
  have load32_12 := stackWords 12 (by decide) (by decide)
  have load32_52 := stackWords 52 (by decide) (by decide)
  have load64_104 := stackWords.load64 104 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_104
  have load32_156 := stackWords 156 (by decide) (by decide)
  compression_group [group44, Values.Program.part13, Values.Program.part14, List.cons_append, List.nil_append,
    Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false] registers45 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0, ← load32_8, ← load32_12, ← load32_52, ← load64_104, ← load32_156]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group45_step : GroupStep b_l121930_45 b_l121930_46 group45 registers45 registers46 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers45, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_56 := stackWords.load64 56 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_56
  have load32_96 := stackWords 96 (by decide) (by decide)
  have load32_160 := stackWords 160 (by decide) (by decide)
  have load32_164 := stackWords 164 (by decide) (by decide)
  compression_group [group45, Values.Program.part14, List.cons_append, List.nil_append,
    Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false] registers46 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_56, ← load32_96, ← load32_160, ← load32_164]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group46_step : GroupStep b_l121930_46 b_l121930_47 group46 registers46 registers47 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers46, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_20 := stackWords 20 (by decide) (by decide)
  have load64_88 := stackWords.load64 88 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_88
  have load32_180 := stackWords 180 (by decide) (by decide)
  have load32_184 := stackWords 184 (by decide) (by decide)
  compression_group [group46, Values.Program.part14, List.cons_append, List.nil_append,
    Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false] registers47 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_20, ← load64_88, ← load32_180, ← load32_184]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group47_step : GroupStep b_l121930_47 b_l121930_48 group47 registers47 registers48 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers47, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_112 := stackWords.load64 112 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_112
  have load64_128 := stackWords.load64 128 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_128
  have load64_208 := stackWords.load64 208 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_208
  have load64_224 := stackWords.load64 224 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_224
  compression_group [group47, Values.Program.part14, List.cons_append, List.nil_append] registers48 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_112, ← load64_128, ← load64_208, ← load64_224]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group48_step : GroupStep b_l121930_48 b_l121930_49 group48 registers48 registers49 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers48, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_120 := stackWords.load64 120 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_120
  have load64_216 := stackWords.load64 216 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_216
  compression_group [group48, Values.Program.part15, List.cons_append, List.nil_append] registers49 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_120, ← load64_216]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group49_step : GroupStep b_l121930_49 b_l121930_50 group49 registers49 registers50 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers49, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_52 := stackWords 52 (by decide) (by decide)
  have load64_72 := stackWords.load64 72 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_72
  compression_group [group49, Values.Program.part15, List.cons_append, List.nil_append, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false]
    registers50 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_52, ← load64_72]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group50_step : GroupStep b_l121930_50 b_l121930_51 group50 registers50 registers51 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers50, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_128 := stackWords.load64 128 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_128
  compression_group [group50, Values.Program.part15, List.cons_append, List.nil_append] registers51 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_128]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group51_step : GroupStep b_l121930_51 b_l121930_52 group51 registers51 registers52 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers51, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_112 := stackWords.load64 112 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_112
  have load64_120 := stackWords.load64 120 (by decide) (by decide)
  simp only [Nat.reduceAdd] at load64_120
  have load32_144 := stackWords 144 (by decide) (by decide)
  compression_group [group51, Values.Program.part15, Values.Program.part16, List.cons_append, List.nil_append]
    registers52 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_112, ← load64_120, ← load32_144]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group52_step : GroupStep b_l121930_52 b_l121930_53 group52 registers52 registers53 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers52, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp only [BitVec.add_zero] at load32_0
  have load32_148 := stackWords 148 (by decide) (by decide)
  have load32_152 := stackWords 152 (by decide) (by decide)
  compression_group [group52, Values.Program.part16, List.cons_append, List.nil_append] registers53 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0, ← load32_148, ← load32_152]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group53_step : GroupStep b_l121930_53 b_l121930_54 group53 registers53 registers54 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers53, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group53, Values.Program.part16, List.cons_append, List.nil_append] registers54 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group54_step : GroupStep b_l121930_54 b_l121930_55 group54 registers54 registers55 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers54, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group54, Values.Program.part16, Values.Program.part17, List.cons_append, List.nil_append]
    registers55 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group55_step : GroupStep b_l121930_55 b_l121930_56 group55 registers55 registers56 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers55, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_168 := stackWords 168 (by decide) (by decide)
  have load32_172 := stackWords 172 (by decide) (by decide)
  have load32_176 := stackWords 176 (by decide) (by decide)
  compression_group [group55, Values.Program.part17, List.cons_append, List.nil_append] registers56 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_168, ← load32_172, ← load32_176]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group56_step : GroupStep b_l121930_56 b_l121930_57 group56 registers56 registers57 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers56, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_64 := stackWords 64 (by decide) (by decide)
  have load32_136 := stackWords 136 (by decide) (by decide)
  compression_group [group56, Values.Program.part17, List.cons_append, List.nil_append] registers57 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_64, ← load32_136]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group57_step : GroupStep b_l121930_57 b_l121930_58 group57 registers57 registers58 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers57, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group57, Values.Program.part17, Values.Program.part18, List.cons_append, List.nil_append]
    registers58 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group58_step : GroupStep b_l121930_58 b_l121930_59 group58 registers58 registers59 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers58, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_20 := stackWords 20 (by decide) (by decide)
  compression_group [group58, Values.Program.part18, List.cons_append, List.nil_append] registers59 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_20]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group59_step : GroupStep b_l121930_59 b_l121930_60 group59 registers59 registers60 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers59, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_40 := stackWords 40 (by decide) (by decide)
  have load32_100 := stackWords 100 (by decide) (by decide)
  compression_group [group59, Values.Program.part18, List.cons_append, List.nil_append] registers60 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_40, ← load32_100]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group60_step : GroupStep b_l121930_60 b_l121930_61 group60 registers60 registers61 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers60, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group60, Values.Program.part18, Values.Program.part19, List.cons_append, List.nil_append]
    registers61 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group61_step : GroupStep b_l121930_61 b_l121930_62 group61 registers61 registers62 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers61, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group61, Values.Program.part19, List.cons_append, List.nil_append] registers62 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

def range42 := group42 ++ group43 ++ group44 ++ group45 ++ group46 ++ group47 ++ group48 ++ group49 ++ group50 ++ group51 ++ group52 ++ group53 ++ group54 ++ group55 ++ group56 ++ group57 ++ group58 ++ group59 ++ group60 ++ group61

theorem range42_step : GroupStep b_l121930_42 b_l121930_62 range42 registers42 registers62 spilledInput :=
  (group42_step.chain
    (group43_step.chain
    (group44_step.chain
    (group45_step.chain
    (group46_step.chain
    (group47_step.chain
    (group48_step.chain
    (group49_step.chain
    (group50_step.chain
    (group51_step.chain
    (group52_step.chain
    (group53_step.chain
    (group54_step.chain
    (group55_step.chain
    (group56_step.chain
    (group57_step.chain
    (group58_step.chain
    (group59_step.chain
    (group60_step.chain
    group61_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
