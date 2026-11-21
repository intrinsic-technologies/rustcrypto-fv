import X86Proofs.Instructions.Xor.Generated.MR.Form
import X86Proofs.Instructions.Xor.Generated.M8R8.Form
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Form
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Form
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter.Operation

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Counter

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_m64_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (off nextAddress addr : BitVec 64) (isStack isRip : Bool) (imm : BitVec 8)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, nextAddress, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch nextAddress 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add nextAddress 1#64) = .ok addr)
    (hu : DataReady u)
    (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.ADD_MEMv_IMMb ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs u addr (addSpec
        ((Operand.mem addr : Operand 64).read u) (imm.signExtend 64)) 0 (BitVec.add nextAddress 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 64 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess u "load") f 0 (BitVec.add nextAddress 1#64))
    ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hu.tables) isStack addr 64 (by decide) v hlow hmem
  have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_MEMv_IMMb
  simp only [writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address 64 isRip off (BitVec.add nextAddress 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.ADD => add_operation _ 64 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _]


theorem adc_m64_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (off nextAddress addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, nextAddress, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch nextAddress 8).run t = (.ok 0, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add nextAddress 1#64) = .ok addr)
    (hu : DataReady u)
    (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.ADC_MEMv_IMMb ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs u addr (addSpec
        ((Operand.mem addr : Operand 64).read u) (BitVec.ofNat 64 (u.RFLAGS.getLsbD 0).toNat)) 0 (BitVec.add nextAddress 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 64 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess u "load") f 0 (BitVec.add nextAddress 1#64))
    ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hu.tables) isStack addr 64 (by decide) v hlow hmem
  have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADC_MEMv_IMMb
  simp only [writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address 64 isRip off (BitVec.add nextAddress 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.ADC => adc_zero_operation _ _,
    Logical_Mem_Write => hwrite _ _]


end Sha2.Proofs.Wrapper512.Absorb.Large.Counter
