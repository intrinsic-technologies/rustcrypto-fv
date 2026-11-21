import X86Proofs.Core.Operand
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleOperation

namespace P256.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shld_r64_r64_one_form [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok 1, t))
    (htmode : In64BitMode t) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHLD_GPRv_GPRv_IMMb ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs t dst (shldOneSpec (oracleBit t.oracle) (dst.read s) (src.read s))
        1 (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHLD_GPRv_GPRv_IMMb
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHLD => shld_one_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Common.Instructions.ShiftLeft
