import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Store
import P256.Proofs.Common.Instructions.Setb.Form

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem setcc_m8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (opcode : BitVec 8)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hw : MemWritable t addr 1) :
    (X86.Instructions.SETB_MEMb ip ctx mod rm opcode).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand 8)
        (setccValue (opcode.extractLsb' 0 4) t) next) := by
  have hcontext : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run _ (ht.withNextIP next) isStack addr 8 (by decide)
    (setccValue (opcode.extractLsb' 0 4) t) hw.low hw.mem
  unfold X86.Instructions.SETB_MEMb
  spec_bind_rfl
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.Instructions.Operations.SETcc => setcc_operation _ _,
    Logical_Mem_Write => hwrite]

end P256.Proofs.Common.Instructions.Setb
