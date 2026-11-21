import Md5.Proofs.Memory.Basic
import X86Proofs.Instructions.Push.Triple

namespace Md5.Proofs.Block

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem pushStack_run [Bindings] (s : RamState) (h : DataReady s) (hss : s.SS = userStackSegment)
    (rsp v : BitVec 64) (hw : MemReadable s (rsp - 8) 8) :
    (Push_Stack s.SS rsp s.CS 64 64 v).run s =
      (.ok (rsp - 8 : BitVec 64),
        (Operand.mem (rsp - 8) : Operand 64).write (stackAccess s) v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 336 }
  have ht : DataReady t := h.oracle _
  have hcan := isCanonicalWrtPagingMode_run s (rsp - 8) 8 h.cr0 h.cr4 h.efer.lme
    h.lam (by have := hw.low; omega) hw.low
  let linear : Address_Translation :=
    { (linearAddressFromOracle s.oracle s.DS s.CPL (rsp - 8)).1 with
      translation_cpl := X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) }
  have htr := translateLinearToPhysical_run_of_dataReady t ht linear
    .Memory_Write 8 rfl (by decide) rfl hw.low
  have hcpl : 0 ≤ X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ∧
      X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ≤ 3 := by decide
  have hphys := Memory.physicalMemWrite_dataPhysical_run linear (rsp - 8) rfl
    64 (by decide) rfl v t ht.smrr hcpl hw.mem
  unfold Push_Stack
  rw [hss, h.cs]
  spec_run [MonadState.get => get_run _,
    Is_64Bit_Code_Segment => is64BitCodeSegment_userCodeSegment_run _ h.efer.lma,
    Is_Canonical_Wrt_Paging_Mode => hcan,
    Create_Linear_Address => createLinearAddress64_run _ _ h.efer.lma,
    Is_Alignment_Checking_Enabled => isAlignmentCheckingEnabled_run _ ht.cr0,
    Check_Write_Permission => checkWritePermission_run _ _ ht.cs ht.efer.lma,
    Check_Data_Write_Breakpoint => checkDataWriteBreakpoint_run _ _ _ ht.debug,
    Translate_Linear_To_Physical.interpreted => htr,
    Physical_Mem_Write => hphys]

theorem push_operation [Bindings] (t : RamState) (h : DataReady t) (hss : t.SS = userStackSegment)
    (v : BitVec 64) (hw : MemReadable t (pushAddr t) 8) :
    (X86.Instructions.Operations.PUSH 64 v).run t = (.ok (), pushState t v) := by
  unfold X86.Instructions.Operations.PUSH
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack_run t h hss (stackPtr t) v hw, RSP_write => rspWrite_run _ _]

theorem push_r_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (opcode : BitVec 8) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : MemReadable t (pushAddr t) 8) :
    (X86.Instructions.PUSH_GPRv_50_0 ip ctx opcode).run t =
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), pushState { t with Next_IP := ip } (src.read t)) := by
  have hpush := push_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
  simp only [Operand.read_reg64]

  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_GPRv_50_0
    spec_run [Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.PUSH => hpush _ (hw.of_external_eq rfl)]

private theorem push_start [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) ∧
      (afterFetches (beforeFetch s) k).SS = userStackSegment :=
  ⟨h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables, h.cpu.ss⟩

theorem push_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : PushOpcode op) (hcode : BytesAt s s.RIP [op]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hw : MemReadable s (pushAddr s) 8) :
    let src : Operand 64 := .reg (gprNumber 0 0 (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 1 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 1#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_push s h op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 2) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := push_start h 2
  rw [push_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h op [] hop.legacyOpcode hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem push_r64_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) (hcode : BytesAt s s.RIP [rex, op])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hw : MemReadable s (pushAddr s) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 2#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_rex_push s h rex op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := push_start h 3
  rw [push_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op [] hrex hop.legacyOpcode hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

structure PushPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  write : Memory.MemWritable s (pushAddr s) 8

theorem readyToStep_afterStep_push [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (v nextIP : BitVec 64)
    (htables : ∀ i < 8, ¬ Md5.Spec.Program.InPageTables
      (pushAddr s + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦ pushState { t with Next_IP := nextIP } v) :=
  h.of_agreesExcept (AgreesExcept.afterStep_push s length v nextIP) (by
    rw [afterStep_push_external]
    exact Memory.identityPageTableMemory_memStore h.memory.tables _ v htables)

theorem stepEffect_of_push [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (v : RamState → BitVec 64)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PushPre p s →
      X86.Machine.step s = some (.next (afterStep s len fun t ↦
        pushState { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } (v s)))) :
    StepEffect (PushPre p) (codeRange p bytes)
      (pushEffect (fun _ ↦ p + BitVec.ofNat 64 len) v) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    readyToStep_afterStep_push h _ _ _ hpre.write.tables,
    ⟨afterStep_push_rip h _ _ _, ⟨Operand.read_afterStep_push_rsp _ _ _ _,
      Operand.read_afterStep_push_mem _ _ _ _⟩, trivial,
      (pushEffect_components _ v s).symm ▸ AgreesExcept.afterStep_push _ _ _ _⟩⟩

theorem push_r64_effect_step [Bindings] (p : BitVec 64) (op : UInt8) (hop : PushOpcode op) :
    StepEffect (PushPre p) (codeRange p [op])
      (pushR64Effect p 1 (gprNumber 0 0 (opcodeReg op))) := by
  refine stepEffect_of_push _ fun s h hcode hpre ↦ ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_step s h op hop hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write.readable

theorem push_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) :
    StepEffect (PushPre p) (codeRange p [rex, op])
      (pushR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))) := by
  refine stepEffect_of_push _ fun s h hcode hpre ↦ ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_rex_step s h rex op hrex hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write.readable

end Md5.Proofs.Block
