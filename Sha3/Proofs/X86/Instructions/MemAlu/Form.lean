import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Operation
import X86Proofs.Instructions.Cmp.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xor_m_r_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XOR_MEMv_GPRv ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand n).read t) (src.read t)) 1 next) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read_Modify_Write
      (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run
      (writeFlagsOutputs (dataAccess t "load") f 1 next)
      ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl rfl rfl rfl ht.tables) isStack addr 64 (by decide) v hlow hmem
    unfold X86.Instructions.XOR_MEMv_GPRv
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg64]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR64_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.XOR => xor_operation _ 64 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]
  · have hcontext : {ctx with operand_size := 32, address_size := 64} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run t ht isStack addr 32 (by decide) .Memory_Read_Modify_Write
      (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (v : BitVec 32) := logicalMemWrite_run
      (writeFlagsOutputs (dataAccess t "load") f 1 next)
      ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl rfl rfl rfl ht.tables) isStack addr 32 (by decide) v hlow hmem
    unfold X86.Instructions.XOR_MEMv_GPRv
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg32]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR32_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.XOR => xor_operation _ 32 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]

theorem xor_m8_r8_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XOR_MEMb_GPR8 ip ctx mod reg rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand 8).read t) (src.read t)) 1 next) := by
  have hread := logicalMemRead_run t ht isStack addr 8 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 8) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess t "load") f 1 next)
    ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl ht.tables) isStack addr 8 (by decide) v hlow hmem
  rcases hreg with hrex | hlow4
  · have hcontext : {ctx with address_size := 64, rex_prefix_present := true} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.XOR_MEMb_GPR8
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR8_run_of_rex _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.XOR => xor_operation _ 8 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]
  · have hcontext : {ctx with address_size := 64} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.XOR_MEMb_GPR8
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR8_run_of_low _ _ hlow4 _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.XOR => xor_operation _ 8 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]

theorem xor_m8_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip : Bool) (imm : BitVec 8)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64) = .ok addr)
    (hu : DataReady u)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XOR_MEMb_IMMb_80r6 ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs u addr (xorSpec (oracleBit (dataAccess u "load").oracle)
        ((Operand.mem addr : Operand 8).read u) (imm.signExtend 8)) 1 (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 8 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 8) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess u "load") f 1 (BitVec.add next 1#64))
    ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hu.tables) isStack addr 8 (by decide) v hlow hmem
  have hcontext : {ctx with address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XOR_MEMb_IMMb_80r6
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
    X86.Instructions.Operations.XOR => xor_operation _ 8 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _]

theorem cmp_m8_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) (imm : BitVec 8)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64) = .ok addr)
    (hu : DataReady u) (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.CMP_MEMb_IMMb_80r7 ip ctx mod rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess u "load")
        (cmpSpec ((Operand.mem addr : Operand 8).read u) (imm.signExtend 8)) 0
        (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 8 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  have hcontext : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_MEMb_IMMb_80r7
  simp only [writeFlagsOutputs, oracleSkip_zero]
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
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

end X86Proofs
