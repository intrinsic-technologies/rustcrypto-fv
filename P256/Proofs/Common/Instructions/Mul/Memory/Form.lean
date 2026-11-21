import X86Proofs.Step.Address
import P256.Proofs.Common.Instructions.Mul.Operation

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mul_m64_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MUL_MEMv ip ctx mod rm).run s =
      (.ok (), mulResult64 {dataAccess t "load" with Next_IP := next}
        ((Operand.mem addr : Operand 64).read t)) := by
  have hcontext :
      {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  unfold X86.Instructions.MUL_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread, X86.Instructions.Operations.MUL => mul64_operation _ _]

end P256.Proofs.Common.Instructions
