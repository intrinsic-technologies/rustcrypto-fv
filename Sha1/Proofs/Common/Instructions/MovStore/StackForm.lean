import Sha1.Proofs.Common.Instructions.MovStore.Form
import X86Proofs.Instructions.Push.Form
import X86Proofs.Instructions.Call.Form

namespace Sha1.Proofs.Common.Instructions.MovStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem pushStack_run [Bindings] (s : RamState) (h : DataReady s) (hss : s.SS = userStackSegment)
    (rsp v : BitVec 64) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (rsp - 8) 8) :
    (Push_Stack s.SS rsp s.CS 64 64 v).run s =
      (.ok (rsp - 8 : BitVec 64),
        (Operand.mem (rsp - 8) : Operand 64).write (stackAccess s) v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 336 }
  have ht : DataReady t := h.oracle _
  have hcan := isCanonicalWrtPagingMode_run s (rsp - 8) 8 h.cr0 h.cr4 h.efer.lme h.lam (by have := hw.low; omega) hw.low
  let linear : Address_Translation :=
    { (linearAddressFromOracle s.oracle s.DS s.CPL (rsp - 8)).1 with
      translation_cpl := X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) }
  have htr := translateLinearToPhysical_run_of_dataReady t ht linear .Memory_Write 8 rfl (by decide) rfl hw.low
  have hcpl : 0 ≤ X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ∧
      X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ≤ 3 := by decide
  have hphys := physicalMemWrite_dataPhysical_run linear (rsp - 8) rfl 64 (by decide) rfl v t
    ht.smrr hcpl hw.mem
  unfold Push_Stack
  rw [hss, h.cs]
  spec_run [MonadState.get => get_run _, Is_64Bit_Code_Segment => is64BitCodeSegment_userCodeSegment_run _ h.efer.lma,
    Is_Canonical_Wrt_Paging_Mode => hcan,
    Create_Linear_Address => createLinearAddress64_run _ _ h.efer.lma,
    Is_Alignment_Checking_Enabled => isAlignmentCheckingEnabled_run _ ht.cr0,
    Check_Write_Permission => checkWritePermission_run _ _ ht.cs ht.efer.lma,
    Check_Data_Write_Breakpoint => checkDataWriteBreakpoint_run _ _ _ ht.debug,
    Translate_Linear_To_Physical.interpreted => htr,
    Physical_Mem_Write => hphys]

theorem push_operation [Bindings] (t : RamState) (h : DataReady t) (hss : t.SS = userStackSegment)
    (v : BitVec 64) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable t (pushAddr t) 8) :
    (X86.Instructions.Operations.PUSH 64 v).run t = (.ok (), pushState t v) := by
  unfold X86.Instructions.Operations.PUSH
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack_run t h hss (stackPtr t) v hw, RSP_write => rspWrite_run _ _]

theorem push_r_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (opcode : BitVec 8) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable t (pushAddr t) 8) :
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

theorem call_operation_rel [Bindings] (t : RamState) (ctx : Instruction_Context) (off : BitVec 64)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hmode : In64BitMode t)
    (htarget : (BitVec.add t.Next_IP off).toNat < 2^32) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable t (pushAddr t) 8) :
    (X86.Instructions.Operations.CALL_NEAR 64 ctx off true false false).run t =
      (.ok (), callState t t.Next_IP (BitVec.add t.Next_IP off)) := by
  have hb := h.branchReady
  have hend := isEndBranchEnabledAndNotSuppressed_run
    ({ (Operand.reg 4 : Operand 64).write ((Operand.mem (stackPtr t - 8) : Operand 64).write
      (stackAccess t) t.Next_IP)
      (stackPtr t - 8) with RIP := BitVec.add t.Next_IP off, Branch_Taken := true } : RamState)
    (by dsimp only [Operand.write, stackAccess]; exact h.cpl)
    (by dsimp only [Operand.write, stackAccess]; exact h.cr4)
  unfold X86.Instructions.Operations.CALL_NEAR
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (signExtend64_run off t)
  spec_bind_with (relativeBranchWrap_run t _ _ hmode)
  repeat spec_bind_rfl
  spec_bind_with (isShadowStackEnabled_run t h.cpl h.cr4)
  spec_bind_rfl
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.not_false, ↓reduceIte]
  spec_bind_with (get_run t)
  spec_bind_with (checkNewRIP_run t _ hb htarget)
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (get_run t)
  refine (specM_bind_run _ _ (s := t) (t := t) (value := t.Next_IP)
    ((specM_bind_run _ _ rfl).trans ((specM_bind_run _ _ (get_run t)).trans
      (checkedSliceRead_full_run t t.Next_IP)))).trans ?_
  spec_bind_with (pushStack_run t h hss (stackPtr t) t.Next_IP hw)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (rspWrite_run _ _)
  spec_bind_with (branchNear_run _ _)
  spec_bind_with (get_run _)
  spec_bind_with hend
  rfl

theorem call_rel32_form [Bindings] (u v : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (disp : BitVec 32) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 32).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (h : DataReady v) (hss : v.SS = userStackSegment)
    (htarget : (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64)).toNat < 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable v (pushAddr v) 8) :
    (X86.Instructions.CALL_NEAR_RELBRd ip ctx).run u =
      (.ok (), callState (withNextIP v (BitVec.add ip 4#64)) (BitVec.add ip 4#64)
        (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.CALL_NEAR_RELBRd
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 4)) _ (s := v)
    (value := BitVec.add ip 4#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 4#64)) (value := ()) rfl).trans ?_
  exact call_operation_rel _ ctx _ (h.withNextIP _) hss (hmode.of_cs_lma_eq rfl rfl) htarget
    (hw.of_external_eq rfl)

end Sha1.Proofs.Common.Instructions.MovStore
