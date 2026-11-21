import Sha2.Proofs.Common.Instructions.Imul.Operation

set_option autoImplicit false

open X86Proofs

namespace Sha2.Proofs.Common.Instructions

open X86 X86.Helpers

theorem imul_r64_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ]
    (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.IMUL_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (imulSpec64 s.oracle (dst.read s) (src.read s)) 4 ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.IMUL_GPRv_GPRv
  simp only [writeOutputs, Operand.read_reg64, Operand.write_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.IMUL_SINGLE => imul64_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end Sha2.Proofs.Common.Instructions
