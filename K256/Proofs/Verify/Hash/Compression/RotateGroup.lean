import K256.Proofs.Verify.Hash.Compression.Groups

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

def group01 := (Values.Program.part00.drop 20).take 20

def registers02 : List (Fin 127 × BitVec 5) := [(112,0), (121,1), (116,2), (3,3), (4,4), (5,5), (125,6), (118,7), (8,8), (61,9), (10,10), (58,11), (12,12), (76,13), (56,14), (54,15)]

set_option maxHeartbeats 850000 in
set_option linter.unusedSimpArgs false in
theorem group01_step : GroupStep b_l121930_1 b_l121930_2 group01 firstRegisters registers02
    (fun _ _ => True) := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp _ regs saved
  simp only [firstRegisters, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  compression_group [group01, Values.Program.part00] registers02 cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp]
    [sp]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← r11, ← r12, ← r13, ← r14, ← r15, ← sp]

end K256.Proofs.Verify.Hash.Compression
