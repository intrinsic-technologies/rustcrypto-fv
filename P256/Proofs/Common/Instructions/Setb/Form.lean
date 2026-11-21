import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Branch.Cond

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open scoped X86.Runtime.Syntax

def setccValue (cc : BitVec 4) (s : RamState) : BitVec 8 :=
  if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then 1 else 0

theorem setcc_operation (s : RamState) (cc : BitVec 4) :
    (X86.Instructions.Operations.SETcc cc).run s = (.ok (setccValue cc s), s) := by
  unfold X86.Instructions.Operations.SETcc
  rw [specM_bind_run _ _ (conditionHolds_run s cc)]
  unfold setccValue
  cases condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) <;> rfl

theorem setb_r_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (opcode : BitVec 8) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false)
    (hlow : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
        ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.SETB_GPR8 ip ctx rm opcode).run s =
      (.ok (), writeResult s (.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 8)
        (setccValue (opcode.extractLsb' 0 4) s) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SETB_GPR8
  rcases hlow with hrex | hsmall
  · simp only [writeResult, Operand.write]
    spec_run [
      X86.Instructions.Operations.SETcc => setcc_operation _ _,
      Write_GPR8 => by rw [hrex]; exact writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · simp only [writeResult, Operand.write]
    spec_run [
      X86.Instructions.Operations.SETcc => setcc_operation _ _,
      Write_GPR8 => writeGPR8_run_of_low _ _ hsmall _ _ (hmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Common.Instructions.Setb
