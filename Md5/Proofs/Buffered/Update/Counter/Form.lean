import Md5.Proofs.Memory.Basic
import X86Proofs.Instructions.Xor.Generated.MR.Form
import X86Proofs.Instructions.Xor.Generated.M8R8.Form
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Form
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Form
import X86Proofs.Instructions.Inc.Operation
import X86Proofs.Instructions.Add.Operation

namespace Md5.Proofs.Buffered.Update.Counter

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem inc_m64_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hw : Md5.Proofs.Memory.MemWritable t addr 8) :
    (X86.Instructions.INC_MEMv ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs t addr
        (incSpec (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand 64).read t))
        0 next) := by
  have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hw.low hw.bytes
  have hwrite (f : StatusFlags) (v : BitVec 64) := Md5.Proofs.Memory.logicalMemWrite_run
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl ht.tables) isStack addr 64 (by decide) v hw.low hw.bytes
  unfold X86.Instructions.INC_MEMv
  simp only [writeRmwOutputs, writeFlagsOutputs]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.INC => inc_operation _ 64 (by decide) _,
    Logical_Mem_Write => hwrite _ _]

theorem add_m64_r64_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hw : Md5.Proofs.Memory.MemWritable t addr 8) :
    (X86.Instructions.ADD_MEMv_GPRv ip ctx mod reg rm).run s =
      let src : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeRmwOutputs t addr
        (addSpec ((Operand.mem addr : Operand 64).read t) (src.read t)) 0 next) := by
  have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hw.low hw.bytes
  have hwrite (f : StatusFlags) (v : BitVec 64) := Md5.Proofs.Memory.logicalMemWrite_run
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl ht.tables) isStack addr 64 (by decide) v hw.low hw.bytes
  unfold X86.Instructions.ADD_MEMv_GPRv
  simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg64]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (readGPR64_run _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.ADD => add_operation _ 64 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _]

end Md5.Proofs.Buffered.Update.Counter
