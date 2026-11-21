import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov
import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Load

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

def cmovR32M32Value (cc : BitVec 4) (dst : BitVec 5) (addr : BitVec 64)
    (s : RamState) : BitVec 32 :=
  if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then
    (Operand.mem addr : Operand 32).read s
  else
    (Operand.reg dst : Operand 32).read s

theorem cmov_r32_m32_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hsize : ctx.operand_size = 32) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hread : MemReadable t addr 4) :
    (X86.Instructions.CMOVB_GPRv_MEMv ip ctx mod reg rm opcode).run s =
      let dst := gprNumber ctx.rex_r4 ctx.rex_r3 reg
      (.ok (), writeResult (dataAccess t "load") (.reg dst : Operand 32)
        (cmovR32M32Value (opcode.extractLsb' 0 4) dst addr t) next) := by
  have hcontext :
      {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hmem := logicalMemRead_run t ht isStack addr 32 (by decide) .Memory_Read (.inl rfl)
    hread.low hread.mem
  unfold X86.Instructions.CMOVB_GPRv_MEMv
  simp only [writeResult, Operand.write_reg32, cmovR32M32Value, Operand.read_reg32]
  spec_bind_rfl
  spec_bind_with hea
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (readGPR32_run _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hmem,
    X86.Instructions.Operations.CMOVcc => cmov32_operation _ _ _ _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end P256.Proofs.Common.Instructions
