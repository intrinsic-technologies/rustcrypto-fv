import X86Proofs.Core.Operand
import P256.Proofs.Common.Instructions.Sar.Operation

namespace P256.Proofs.Common.Instructions

open X86 X86.Helpers X86Proofs

theorem sar_r_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SAR_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 64 count
      (.ok (), writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read s)) (sarOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SAR_GPRv_IMMb
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SAR => sar_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Common.Instructions
