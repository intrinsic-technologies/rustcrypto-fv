import Sha3.Proofs.Permutation.LoadStore.Memory
import Sha3.Proofs.X86.Instructions.MemAlu.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xor_m_r_form_of_readable [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
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
    have hwrite (f : StatusFlags) (v : BitVec 64) := Sha3.Proofs.logicalMemWrite_run_any
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
    have hwrite (f : StatusFlags) (v : BitVec 32) := Sha3.Proofs.logicalMemWrite_run_any
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

theorem xor_m_r_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x31 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t ↦
      writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand n).read t) (src.read t)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x31 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x31 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_31_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x31 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [xor_m_r_form_of_readable _ t _ _ _ _ _ n hn hsize haddr _ _ _ _ _ hea hrip (memAlu_dataReady h _) hmode
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x31 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem xor_m64_r64_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x31 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemReadable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t ↦
      writeRmwOutputs t (am.addrAt s (3 + am.tail.length))
        (xorSpec (oracleBit (dataAccess t "load").oracle)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read t) (src.read t)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have hr := hrex.rexPrefix
  have hstep := xor_m_r_step_of_readable s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode hlow
    hw
  simp only [scanContext_rex _ _ hr] at hstep
  exact hstep

theorem ReadyToStep.afterStep_rmw_of_readable [Bindings] {s : RamState}
    (h : ReadyToStep s) (length : Nat) {n : Nat} (addr : BitVec 64)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64)
    (havoid : ∀ i, i < n / 8 →
      ¬ Sha3.Spec.Program.InPageTables (addr + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦ writeRmwOutputs t addr (out t) oracleUsed nextIP) := by
  apply h.of_agreesExcept (AgreesExcept.afterStep_rmw s length addr out oracleUsed nextIP)
  rw [afterStep_rmw_external]
  exact identityPageTableMemory_memStore_of_notInPageTables s addr _ h.memory.tables havoid

theorem xor_m64_r64_effect_step_of_readable [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (StorePreReadable p (fun s ↦ am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x31 :: am.modrm reg :: am.tail))
      (xorMREffect p (3 + am.tail.length) 64
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  obtain ⟨⟨hp, hw⟩, havoid⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, xor_m64_r64_step_of_readable s h rex hrex reg am hv hx hb hcode.bytesAt hlow hw,
    ReadyToStep.afterStep_rmw_of_readable h _ _ _ _ _ havoid,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

end X86Proofs
