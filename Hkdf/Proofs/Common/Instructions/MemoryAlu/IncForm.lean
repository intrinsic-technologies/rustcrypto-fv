import X86Proofs.Instructions.Xor.Generated.MR.Form
import X86Proofs.Instructions.Xor.Generated.M8R8.Form
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Form
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Form
import X86Proofs.Instructions.Inc.Operation

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions.MemoryAlu

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem inc_m64_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t)
    (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.INC_MEMv ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs t addr (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        ((Operand.mem addr : Operand 64).read t)) 0 next) := by
  have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl ht.tables) isStack addr 64 (by decide) v hlow hmem
  unfold X86.Instructions.INC_MEMv
  simp only [writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.INC => inc_operation _ 64 (by decide) _,
    Logical_Mem_Write => hwrite _ _]

end Hkdf.Proofs.Common.Instructions.MemoryAlu
