import Sha3.Proofs.Scalar.Condition.Sete.LowByte
import X86Proofs.Instructions.Branch.Cond

namespace X86Proofs

open X86 X86.Helpers

def setccSpec (cc : BitVec 4) (flags : StatusFlags) : BitVec 8 :=
  if condHolds cc flags then 1 else 0

theorem setcc_operation {σ : Type} (s : X86.State σ) (cc : BitVec 4) :
    (X86.Instructions.Operations.SETcc cc).run s =
      (.ok (setccSpec cc (StatusFlags.ofRFLAGS s.RFLAGS)), s) := by
  unfold X86.Instructions.Operations.SETcc
  rw [specM_bind_run _ _ (conditionHolds_run s cc)]
  cases hc : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) <;>
    simp only [setccSpec, hc, ↓reduceIte] <;> rfl

theorem sete_low_form {σ : Type} [Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (hlock : ctx.lock_prefix_present = false)
    (hlow : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.SETZ_GPR8 ip ctx rm 0x94).run s =
      (.ok (), writeResult s (.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm))
        (setccSpec 4 (StatusFlags.ofRFLAGS s.RFLAGS)) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SETZ_GPR8
  simp only [writeResult, Operand.write]
  spec_run [X86.Instructions.Operations.SETcc => setcc_operation _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ hlow _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
