import Base16ct.Proofs.Copied.Md5.Proofs.Memory.Basic
import X86Proofs.Instructions.MovStore.Form

namespace Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem mov_m_r_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable t addr (n / 8)) :
    (X86.Instructions.MOV_MEMv_GPRv_1 ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (src.read t))
        next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := Base16ct.Proofs.Copied.Md5.Proofs.Memory.logicalMemWrite_run _ (ht.withNextIP next) isStack addr 64 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t) hw.low hw.bytes
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR64_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := Base16ct.Proofs.Copied.Md5.Proofs.Memory.logicalMemWrite_run _ (ht.withNextIP next) isStack addr 32 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32).read t) hw.low hw.bytes
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR32_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]

end Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores
