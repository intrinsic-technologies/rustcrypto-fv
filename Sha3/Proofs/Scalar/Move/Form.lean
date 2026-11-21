import Sha3.Proofs.X86.Instructions.MovzxLoad.Operation
import X86Proofs.Instructions.Branch.Cond
import X86Proofs.Program.ReadWrite.WriteResult

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movzx_r32_r8_rex_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) (hrex : ctx.rex_prefix_present = true) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      (.ok (), writeResult s (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 8).read s))
        ip) := by
  have hcontext :
      {ctx with operand_size := 32, lock_prefix_present := false, rex_prefix_present := true} =
        ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.write_reg32, Operand.read]
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readGPR8_run_of_rex _ _ hmode)).trans ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_rfl
  refine (specM_bind_run _ _ (movzx_operation _ 32 (.inr rfl) _)).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  rw [writeGPR32_run _ _ _ ?hm]
  · rfl
  · exact hmode.of_cs_lma_eq rfl rfl

theorem cmovb_operation {σ : Type} (s : X86.State σ) (a b : BitVec 64) :
    (X86.Instructions.Operations.CMOVcc 64 a b 2).run s =
      (.ok (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then b else a), s) := by
  unfold X86.Instructions.Operations.CMOVcc
  spec_run [Condition_Holds => conditionHolds_run _ _]
  change ((if (StatusFlags.ofRFLAGS s.RFLAGS).CF then pure b else pure a) :
    Runtime.SpecM Exception (State σ) (BitVec 64)).run s = _
  cases (StatusFlags.ofRFLAGS s.RFLAGS).CF <;> rfl

theorem cmovb_r64_r64_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMOVB_GPRv_GPRv ip ctx reg rm 0x42).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read s else dst.read s) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMOVB_GPRv_GPRv
  simp only [writeResult, Operand.write_reg64, Operand.read_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CMOVcc => cmovb_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
