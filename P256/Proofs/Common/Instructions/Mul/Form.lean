import P256.Proofs.Common.Instructions.Mul.Operation

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Helpers

theorem mul_r64_form {σ : Type} (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MUL_GPRv ip ctx rm).run s =
      (.ok (), mulResult64 {s with Next_IP := ip}
        s.GPR[gprIndex (gprNumber ctx.rex_b4 ctx.rex_b3 rm)]) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MUL_GPRv
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.MUL => mul64_operation _ _]

end P256.Proofs.Common.Instructions
