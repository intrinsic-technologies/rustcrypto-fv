import X86Proofs.Core.Operand
import X86Proofs.Instructions.Add.Operation

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem writeGPR8_run_of_rex {σ : Type} (s : X86.State σ) (r : BitVec 5)
    (value : BitVec 8) (hmode : In64BitMode s) :
    (Write_GPR8 r true value).run s =
      (.ok (), {s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r])}) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ hmode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> rfl

theorem add_r8_r8_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ADD_GPR8_GPR8_00 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (addSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_GPR8_GPR8_00
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end Hkdf.Proofs.Common.Instructions.AddByte
