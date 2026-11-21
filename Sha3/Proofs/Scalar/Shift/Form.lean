import Sha3.Proofs.Scalar.Shift.Operation
import X86Proofs.Core.Operand

namespace X86Proofs

open X86 X86.Helpers

theorem shl_r64_cl_form [X86.Machine.Bindings] (s : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPRv_CL_D3r4 ip ctx rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 64 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (shlSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shlOracleAF s.oracle c) c (dst.read s)) (shlOracleBits c) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPRv_CL_D3r4
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  have hcl : (CL (σ := X86.Machine.Ram)).run s =
      (.ok ((Operand.reg 1 : Operand 8).read s), s) := by
    rfl
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    CL => hcl,
    X86.Instructions.Operations.SHL => shl_operation _ 64 (by decide) _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
