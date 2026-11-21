import X86Proofs.Step.Address
import X86Proofs.Instructions.And.Generated.RR.Triple

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem and_r_m_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.AND_GPRv_MEMv ip ctx mod reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let u := dataAccess t "load"
      (.ok (), writeOutputs u dst
        (andSpec (oracleBit u.oracle) (dst.read t) ((Operand.mem addr : Operand n).read t)) 1
        next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read (.inl rfl)
      hlow hmem
    unfold X86.Instructions.AND_GPRv_MEMv
    simp only [writeOutputs, Operand.write_reg64, Operand.read_reg64]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) rfl).trans ?_
    refine (specM_bind_run _ _ (s := t) rfl).trans ?_
    refine (specM_bind_run _ _ (readGPR64_run _ _ hmode)).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.AND => and_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext :
        {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run t ht isStack addr 32 (by decide) .Memory_Read (.inl rfl)
      hlow hmem
    unfold X86.Instructions.AND_GPRv_MEMv
    simp only [writeOutputs, Operand.write_reg32, Operand.read_reg32]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) rfl).trans ?_
    refine (specM_bind_run _ _ (s := t) rfl).trans ?_
    refine (specM_bind_run _ _ (readGPR32_run _ _ hmode)).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ hread).trans ?_
    spec_bind_rfl
    refine (specM_bind_run _ _ (and_operation _ 32 (by decide) _ _)).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    rw [writeGPR32_run _ _ _ ?hm]
    · rfl
    · exact hmode.of_cs_lma_eq rfl rfl

end P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad
