import K256.Proofs.Verify.Hash.Compression.Groups.Chain

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group142_step : GroupStep b_l121930_142 b_l121930_143 group142 registers142 registers143 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers142, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_20 := stackWords 20 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_20
  compression_group [group142, Values.Program.part44, List.cons_append, List.nil_append] registers143 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_20]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group143_step : GroupStep b_l121930_143 b_l121930_144 group143 registers143 registers144 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers143, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group143, Values.Program.part44, List.cons_append, List.nil_append] registers144 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group144_step : GroupStep b_l121930_144 b_l121930_145 group144 registers144 registers145 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers144, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_16 := stackWords 16 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_16
  have load32_72 := stackWords 72 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_72
  compression_group [group144, Values.Program.part45, List.cons_append, List.nil_append] registers145 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_16, ← load32_72]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group145_step : GroupStep b_l121930_145 b_l121930_146 group145 registers145 registers146 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers145, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group145, Values.Program.part45, List.cons_append, List.nil_append] registers146 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group146_step : GroupStep b_l121930_146 b_l121930_147 group146 registers146 registers147 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers146, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_0
  have load32_112 := stackWords 112 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_112
  compression_group [group146, Values.Program.part45, List.cons_append, List.nil_append] registers147 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0, ← load32_112]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group147_step : GroupStep b_l121930_147 b_l121930_148 group147 registers147 registers148 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers147, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group147, Values.Program.part45, Values.Program.part46, List.cons_append, List.nil_append] registers148 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group148_step : GroupStep b_l121930_148 b_l121930_149 group148 registers148 registers149 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers148, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_4 := stackWords 4 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_4
  have load32_104 := stackWords 104 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_104
  compression_group [group148, Values.Program.part46, List.cons_append, List.nil_append] registers149 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_4, ← load32_104]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group149_step : GroupStep b_l121930_149 b_l121930_150 group149 registers149 registers150 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers149, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group149, Values.Program.part46, List.cons_append, List.nil_append] registers150 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group150_step : GroupStep b_l121930_150 b_l121930_151 group150 registers150 registers151 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers150, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_64 := stackWords.load64 64 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_64
  compression_group [group150, Values.Program.part46, Values.Program.part47, List.cons_append, List.nil_append] registers151 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_64]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group151_step : GroupStep b_l121930_151 b_l121930_152 group151 registers151 registers152 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers151, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_128 := stackWords 128 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_128
  compression_group [group151, Values.Program.part47, List.cons_append, List.nil_append] registers152 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_128]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group152_step : GroupStep b_l121930_152 b_l121930_153 group152 registers152 registers153 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers152, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group152, Values.Program.part47, List.cons_append, List.nil_append] registers153 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group153_step : GroupStep b_l121930_153 b_l121930_154 group153 registers153 registers154 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers153, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_40 := stackWords.load64 40 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_40
  have load32_88 := stackWords 88 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_88
  compression_group [group153, Values.Program.part47, Values.Program.part48, List.cons_append, List.nil_append] registers154 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_40, ← load32_88]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group154_step : GroupStep b_l121930_154 b_l121930_155 group154 registers154 registers155 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers154, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group154, Values.Program.part48, List.cons_append, List.nil_append] registers155 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group155_step : GroupStep b_l121930_155 b_l121930_156 group155 registers155 registers156 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers155, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group155, Values.Program.part48, List.cons_append, List.nil_append] registers156 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group156_step : GroupStep b_l121930_156 b_l121930_157 group156 registers156 registers157 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers156, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group156, Values.Program.part48, Values.Program.part49, List.cons_append, List.nil_append] registers157 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group157_step : GroupStep b_l121930_157 b_l121930_158 group157 registers157 registers158 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers157, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_0 := stackWords 0 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_0
  compression_group [group157, Values.Program.part49, List.cons_append, List.nil_append] registers158 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_0]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group158_step : GroupStep b_l121930_158 b_l121930_159 group158 registers158 registers159 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers158, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group158, Values.Program.part49, List.cons_append, List.nil_append] registers159 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group159_step : GroupStep b_l121930_159 b_l121930_160 group159 registers159 registers160 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers159, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load32_4 := stackWords 4 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_4
  compression_group [group159, Values.Program.part49, List.cons_append, List.nil_append] registers160 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load32_4]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group160_step : GroupStep b_l121930_160 b_l121930_161 group160 registers160 registers161 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers160, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group160, Values.Program.part50, List.cons_append, List.nil_append] registers161 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group161_step : GroupStep b_l121930_161 b_l121930_162 group161 registers161 registers162 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers161, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group161, Values.Program.part50, List.cons_append, List.nil_append] registers162 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group162_step : GroupStep b_l121930_162 b_l121930_163 group162 registers162 registers163 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers162, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_64 := stackWords.load64 64 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_64
  compression_group [group162, Values.Program.part50, List.cons_append, List.nil_append] registers163 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_64]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group163_step : GroupStep b_l121930_163 b_l121930_164 group163 registers163 registers164 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers163, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group163, Values.Program.part50, Values.Program.part51, List.cons_append, List.nil_append] registers164 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group164_step : GroupStep b_l121930_164 b_l121930_165 group164 registers164 registers165 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers164, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_40 := stackWords.load64 40 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_40
  compression_group [group164, Values.Program.part51, List.cons_append, List.nil_append] registers165 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_40]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem group165_step : GroupStep b_l121930_165 b_l121930_166 group165 registers165 registers166 spilledInput := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ptr regs saved
  simp only [registers165, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have load64_24 := stackWords.load64 24 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load64_24
  have load32_232 := stackWords 232 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_232
  have load32_248 := stackWords 248 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_248
  have load32_264 := stackWords 264 (by decide) (by decide)
  simp -failIfUnchanged only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at load32_264
  compression_group [group165, Values.Program.part51, List.cons_append, List.nil_append] registers166 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← load64_24, ← load32_232, ← load32_248, ← load32_264]

def range142 := group142 ++ group143 ++ group144 ++ group145 ++ group146 ++ group147 ++ group148 ++ group149 ++ group150 ++ group151 ++ group152 ++ group153 ++ group154 ++ group155 ++ group156 ++ group157 ++ group158 ++ group159 ++ group160 ++ group161 ++ group162 ++ group163 ++ group164 ++ group165

theorem range142_step : GroupStep b_l121930_142 b_l121930_166 range142 registers142 registers166 spilledInput :=
  (group142_step.chain
    (group143_step.chain
    (group144_step.chain
    (group145_step.chain
    (group146_step.chain
    (group147_step.chain
    (group148_step.chain
    (group149_step.chain
    (group150_step.chain
    (group151_step.chain
    (group152_step.chain
    (group153_step.chain
    (group154_step.chain
    (group155_step.chain
    (group156_step.chain
    (group157_step.chain
    (group158_step.chain
    (group159_step.chain
    (group160_step.chain
    (group161_step.chain
    (group162_step.chain
    (group163_step.chain
    (group164_step.chain
    group165_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end K256.Proofs.Verify.Hash.Compression
