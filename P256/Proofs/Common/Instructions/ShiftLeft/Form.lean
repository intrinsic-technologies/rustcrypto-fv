import X86Proofs.Core.Operand
import P256.Proofs.Common.Instructions.ShiftLeft.Operation

namespace P256.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shl_r_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPRv_IMMb_C1r4 ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount n count
      (.ok (), writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shlOracleAF t.oracle c) c (dst.read s)) (shlOracleBits c)
        (BitVec.add ip 1#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHL_GPRv_IMMb_C1r4
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.SHL => shl_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHL_GPRv_IMMb_C1r4
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.SHL => shl_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Common.Instructions.ShiftLeft
