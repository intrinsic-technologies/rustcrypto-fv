import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.WriteResult
import Sha3.Proofs.X86.Instructions.MovzxLoad.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movzx_r_m8_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVZX_GPRv_MEMb_1 ip ctx mod reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movzxSpec n ((Operand.mem addr : Operand 8).read t)) next) := by
  have hread := logicalMemRead_run t ht isStack addr 8 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVZX_GPRv_MEMb_1
    simp only [writeResult, Operand.write_reg64]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ hread).trans ?_
    spec_bind_rfl
    refine (specM_bind_run _ _ (movzx_operation _ 64 (.inl rfl) _)).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    rw [writeGPR64_run _ _ _ ?hm]
    · rfl
    · exact hmode.of_cs_lma_eq rfl rfl
  · have hcontext :
        {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOVZX_GPRv_MEMb_1
    simp only [writeResult, Operand.write_reg32]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ hread).trans ?_
    spec_bind_rfl
    refine (specM_bind_run _ _ (movzx_operation _ 32 (.inr rfl) _)).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    rw [writeGPR32_run _ _ _ ?hm]
    all_goals first | exact hmode.of_cs_lma_eq rfl rfl | rfl

end X86Proofs
