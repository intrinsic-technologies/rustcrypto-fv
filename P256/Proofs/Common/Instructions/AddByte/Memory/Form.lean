import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Add.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_m8_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64) = .ok addr)
    (hu : DataReady u)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.ADD_MEMb_IMMb_80r0 ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs u addr (addSpec
        ((Operand.mem addr : Operand 8).read u) (imm.signExtend 8)) 0 (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 8 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 8) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess u "load") f 0 (BitVec.add next 1#64))
    ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hu.tables) isStack addr 8 (by decide) v hlow
      hmem
  have hcontext : {ctx with address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_MEMb_IMMb_80r0
  simp only [writeRmwOutputs, writeFlagsOutputs]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _]

end P256.Proofs.Common.Instructions.AddByte
