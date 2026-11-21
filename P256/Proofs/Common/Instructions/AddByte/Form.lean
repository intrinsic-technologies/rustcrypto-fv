import P256.Proofs.Common.Instructions.Setb.Form
import X86Proofs.Instructions.Add.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_r8_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t))
    (htmode : In64BitMode t) :
    (X86.Instructions.ADD_GPR8_IMMb_80r0 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (addSpec (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_GPR8_IMMb_80r0
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => X86Proofs.writeGPR8_run_of_rex _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Common.Instructions.AddByte
