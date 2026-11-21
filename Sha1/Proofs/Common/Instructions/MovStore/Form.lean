import Sha1.Proofs.Common.Instructions.StorePre
import Sha1.Proofs.Common.Instructions.MemoryWrite
import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Mov.Operation



namespace Sha1.Proofs.Common.Instructions.MovStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs


theorem mov_m_r_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable t lin (n / 8)) :
    (X86.Instructions.MOV_MEMv_GPRv_1 ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand n) (movSpec (src.read t))
        next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 64 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR64_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 32 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR32_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]


theorem mov_m16_r16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable t lin 2) :
    (X86.Instructions.MOV_MEMv_GPRv_1 ip ctx mod reg rm).run s =
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 16) (movSpec (src.read t))
        next) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 16 (by decide)
    ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 16).read t) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMv_GPRv_1
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR16_run _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]


theorem mov_m_imm32_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 32)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 32).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable u lin (n / 8)) :
    (X86.Instructions.MOV_MEMv_IMMz_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem lin : Operand n)
        (movSpec (imm.signExtend n)) (BitVec.add next 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 4#64)) seg addr lin
      hseg 64
      (by decide) (imm.signExtend 64) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_IMMz_1
    have hrip' : ∀ X, X = BitVec.add next 4#64 →
        Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with hfetch
    iterate 3 spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 4#64)) seg addr lin
      hseg 32
      (by decide) (imm.signExtend 32) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_IMMz_1
    have hrip' : ∀ X, X = BitVec.add next 4#64 →
        Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with hfetch
    iterate 3 spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]


theorem mov_m_imm16_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 16) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 16)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 16).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 2#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable u lin 2) :
    (X86.Instructions.MOV_MEMv_IMMz_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem lin : Operand 16)
        (movSpec (imm.signExtend 16)) (BitVec.add next 2#64)) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 2#64)) seg addr lin
    hseg 16
    (by decide) (imm.signExtend 16) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMv_IMMz_1
  have hrip' : ∀ X, X = BitVec.add next 2#64 →
      Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with hfetch
  iterate 3 spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]


theorem mov_m8_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable u lin 1) :
    (X86.Instructions.MOV_MEMb_IMMb_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem lin : Operand 8)
        (movSpec (imm.signExtend 8)) (BitVec.add next 1#64)) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 1#64)) seg addr lin
    hseg 8
    (by decide) (imm.signExtend 8) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMb_IMMb_1
  have hrip' : ∀ X, X = BitVec.add next 1#64 →
      Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with hfetch
  iterate 2 spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

end Sha1.Proofs.Common.Instructions.MovStore
