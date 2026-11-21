import X86Proofs.Instructions.MovLoad.Form
import X86Proofs.Instructions.Cmp.Operation
import X86Proofs.Program.ReadWrite.Load

set_option autoImplicit false

namespace Sha2.Proofs.Common.Encoding.Parser.LengthCheck

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmp_r64_m64_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hread : MemReadable t addr 8) :
    (X86.Instructions.CMP_GPRv_MEMv ip ctx mod reg rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t)
          ((Operand.mem addr : Operand 64).read t)) 0 next) := by
  have hcontext :
      {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hload := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hread.low hread.mem
  unfold X86.Instructions.CMP_GPRv_MEMv
  simp only [writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  simp only [hrip]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    Logical_Mem_Read => hload,
    X86.Instructions.Operations.CMP => cmp_operation _ 64 (by decide) _ _]

end Sha2.Proofs.Common.Encoding.Parser.LengthCheck
