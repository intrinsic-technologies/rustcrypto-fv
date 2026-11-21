import P256.Proofs.Common.Encoding.Parser.TagOps.Instructions
import P256.Proofs.Common.Instructions.ShiftLeft.Operation

open P256.Proofs.Common.Instructions.ShiftLeft (shlOracleAF shlOracleBits shlSpec shl_operation)

namespace P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def clCount (s : RamState) : Nat :=
  shiftCount 64 ((Operand.reg 1 : Operand 8).read s)

theorem clCount_eq_mod (s : RamState) : clCount s = s.GPR[gprIndex 1].toNat % 64 := by
  simp only [clCount, shiftCount, ↓reduceIte, Operand.read, BitVec.toNat_setWidth,
    Nat.reducePow]
  omega

theorem shr_r64_cl_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHR_GPRv_CL ip ctx rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := clCount s
      (.ok (), writeOutputs s dst (shrSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shrOracleAF s.oracle c) c (dst.read s)) (shrOracleBits c) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHR_GPRv_CL
  simp only [writeOutputs, Operand.write_reg64, clCount, Operand.read]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.SHR => shr_operation _ 64 (by decide) _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem shl_r64_cl_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPRv_CL_D3r4 ip ctx rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := clCount s
      (.ok (), writeOutputs s dst (shlSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shlOracleAF s.oracle c) c (dst.read s)) (shlOracleBits c) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPRv_CL_D3r4
  simp only [writeOutputs, Operand.write_reg64, clCount, Operand.read]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.SHL => shl_operation _ 64 (by decide) _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount
