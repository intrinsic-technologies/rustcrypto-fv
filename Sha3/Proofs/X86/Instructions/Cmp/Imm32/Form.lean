import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Cmp.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cmp_r_imm32_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 32) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 32).run s = (.ok imm, t)) :
    (X86.Instructions.CMP_GPRv_IMMz ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t (cmpSpec (dst.read s) (imm.signExtend n)) 0
        (BitVec.add ip 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.CMP_GPRv_IMMz
    simp only [Operand.read_reg64, writeFlagsOutputs, oracleSkip_zero]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.CMP => cmp_operation _ 64 (by decide) _ _]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.CMP_GPRv_IMMz
    simp only [Operand.read_reg32, writeFlagsOutputs, oracleSkip_zero]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.CMP => cmp_operation _ 32 (by decide) _ _]

end X86Proofs
