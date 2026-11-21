import Sha1.Proofs.Buffered.DigestPrepare.Geometry
import Sha1.Proofs.Buffered.DigestPrepare.Branch
import Sha1.Proofs.Common.Instructions.MovStore.Stack
import Sha1.Proofs.MemoryRoutines.Memcpy
import Sha1.Proofs.Buffered.Update.Calls
import Sha1.Proofs.Buffered.Update.SiteCalls
import Sha1.Proofs.Buffered.Update.Rodata
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

abbrev SlotWritable (s : RamState) : Prop :=
  Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (pushAddr s) 8

theorem callMem_operation [Bindings] (t : RamState) (ctx : Instruction_Context)
    (target : BitVec 64) (noTrack : Bool)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (htarget : target.toNat < 2^32) (hw : SlotWritable t) :
    (X86.Instructions.Operations.CALL_NEAR 64 ctx target false true noTrack).run t =
      (.ok (), callState t t.Next_IP target) := by
  have hb := h.branchReady
  have hend := isEndBranchEnabledAndNotSuppressed_run
    ({ (Operand.reg 4 : Operand 64).write ((Operand.mem (stackPtr t - 8) : Operand 64).write
      (stackAccess t) t.Next_IP)
      (stackPtr t - 8) with RIP := target, Branch_Taken := true } : RamState)
    (by dsimp only [Operand.write, stackAccess]; exact h.cpl)
    (by dsimp only [Operand.write, stackAccess]; exact h.cr4)
  unfold X86.Instructions.Operations.CALL_NEAR
  spec_bind_rfl
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (zeroExtend_full_run t target)
  spec_bind_with (get_run t)
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
  spec_bind_with (Sha1.Proofs.Common.Instructions.MovStore.pushStack_run t h hss (stackPtr t)
    t.Next_IP hw)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (rspWrite_run _ _)
  spec_bind_with (branchNear_run _ _)
  spec_bind_with (get_run _)
  spec_bind_with hend
  simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem callMem_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hmode64 : ctx.is_mode64 = true) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hread : MemReadable t addr 8)
    (htarget : ((Operand.mem addr : Operand 64).read t).toNat < 2^32)
    (hw : SlotWritable t) :
    (X86.Instructions.CALL_NEAR_MEMv ip ctx mod rm).run s =
      (.ok (), callState (withNextIP (dataAccess t "load") next) next
        ((Operand.mem addr : Operand 64).read t)) := by
  have hcontext :
      ({ ctx with is_mode64 := true, address_size := 64, lock_prefix_present := false } :
        Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea
  rw [← hcontext]
  have hread' := logicalMemRead_run t h isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hread.low hread.mem
  have hd : DataReady (withNextIP (dataAccess t "load") next) :=
    h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables
  unfold X86.Instructions.CALL_NEAR_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread',
    X86.Instructions.Operations.CALL_NEAR => callMem_operation _ _ _ _ hd hss htarget
      (hw.of_external_eq rfl)]

theorem callMem_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 2 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 8)
    (htarget : ((Operand.mem (am.addrAt s (pre.length + 2 + am.tail.length)) :
      Operand 64).read s).toNat < 2^32)
    (hw : SlotWritable s) :
    let L := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s L fun t =>
      callState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 L)))
        (BitVec.add s.RIP (BitVec.ofNat 64 L))
        ((Operand.mem (am.addrAt s L) : Operand 64).read s))) := by
  intro L
  have hlen' : (pre ++ 0xFF :: am.modrm 2 :: am.tail).length = L := by
    simp only [List.length_append, List.length_cons, L]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 2 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_call_memory s h _ pre.length (am.modrm 2)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0xFF 2 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = L + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (L + 1)
  obtain ⟨hd, hss⟩ := call_start h (L + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 L))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [callMem_form _ t _ _ _ _ hctx.mode64 haddr hlock _ _ _ _ _ hea hrip hd hss
    (hread.of_external_eq rfl) htarget (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

abbrev CallMemSitePre (p : BitVec 64) (am : AddrMode) (s : RamState) : Prop :=
  (Sha1.Proofs.Common.Instructions.StorePre.PushPre p (callMemLen am) s ∧
    (callMemPtr p am s).toNat < 2^32) ∧
    MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8

theorem callMem_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (CallMemSitePre p am) (codeRange p (encodeCallM64 am))
      (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) := by
  refine Sha1.Proofs.Common.Instructions.MovStore.callEffect_step true _ (fun _ h => h.1.1)
    fun s h hcode ⟨⟨hpre, htarget⟩, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have h5 := am.tail_length_le
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := hcode.low (by simp [encodeCallM64])
      (by simp only [encodeCallM64, List.length_cons]; omega)
    simp only [encodeCallM64, List.length_cons] at this
    omega
  exact callMem_step s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow hread htarget hpre.write

theorem hasBytes_of_copy {source destination : Ram} {src dst : BitVec 64} {bytes : ByteArray}
    (h : ∀ i < bytes.size, destination[dst + BitVec.ofNat 64 i]? =
      source[src + BitVec.ofNat 64 i]?)
    (hb : (⟨src.toNat, bytes.size⟩ : MemoryRegion).HasBytes source bytes) :
    (⟨dst.toNat, bytes.size⟩ : MemoryRegion).HasBytes destination bytes := by
  refine ⟨rfl, ?_⟩
  intro i
  have hb' := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb' ⊢
  exact (h i.val i.isLt).trans hb'

theorem memcpy_hasBytes [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {s t : RamState} {bytes : ByteArray} (h : MemcpySiteResult boundary ret s t)
    (hlen : (MemoryRoutines.rdx.read s).toNat = bytes.size)
    (hb : (⟨(rsi.read s).toNat, bytes.size⟩ : MemoryRegion).HasBytes s.external bytes) :
    (⟨(rdi.read s).toNat, bytes.size⟩ : MemoryRegion).HasBytes t.external bytes :=
  hasBytes_of_copy (fun i hi ↦ h.copy i (by simpa only [hlen] using hi)) hb

set_option maxRecDepth 2048 in
theorem digest_memcpy_call [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} (hStride : UnitStringStride bindings)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = p)
    (hSite : p = 0x100083 ∨ p = 0x1000d4)
    (hp : MemcpySitePre (p + 6) s) (hw : SlotWritable s) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  let am : AddrMode := .rip (if p = 0x100083 then 0xfff77 else 0xfff26)
  have ht : callMemPtr p am s = 0x103730 := by
    rcases hSite with rfl | rfl
    all_goals simp only [am, ↓reduceIte, BitVec.reduceEq]
    all_goals change (Operand.mem 0x200000 : Operand 64).read s = _
    all_goals exact memcpy_pointer hCode
  have hm : MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8 := by
    rcases hSite with rfl | rfl
    all_goals simp only [am, ↓reduceIte, BitVec.reduceEq]
    all_goals change MemReadable s 0x200000 8
    all_goals exact memcpy_pointer_readable hCode
  have hb : CodeIn (codeRange p (encodeCallM64 am)) s := by
    rcases hSite with rfl | rfl
    · simp only [am, ↓reduceIte]
      change CodeIn (codeRange 0x100083 [0xff, 0x15, 0x77, 0xff, 0x0f, 0]) s
      exact Sha1.Proofs.Compress.Machine.program_text_slice hCode 0x83 6 (by decide +kernel)
    · simp only [am, BitVec.reduceEq, ↓reduceIte]
      change CodeIn (codeRange 0x1000d4 [0xff, 0x15, 0x26, 0xff, 0x0f, 0]) s
      exact Sha1.Proofs.Compress.Machine.program_text_slice hCode 0xd4 6 (by decide +kernel)
  have hcodeApart : RangeApart (pushAddr s) 8 p (callMemLen am) := by
    rcases hSite with rfl | rfl
    · exact rangeApart_text (offset := 0x83) hp.slotCode (by decide +kernel)
    · exact rangeApart_text (offset := 0xd4) hp.slotCode (by decide +kernel)
  have hret : p + 6 ≠ boundary.rip := by
    rcases hSite with rfl | rfl
    · exact text_address_ne_return hOutside 0x89 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xda (by decide +kernel)
  have hout : boundary.rip.toNat < 0x103730 ∨ 0x10375f ≤ boundary.rip.toNat :=
    Sha1.Proofs.Buffered.outside_text_range_of_not_inProgram hOutside 0x103730 0x10375f
      (by decide) (by decide +kernel)
  exact Sha1.Proofs.Buffered.memcpy_call hStride hout
    (callMem_effect_step p am (by simp [am, AddrMode.Valid]) rfl rfl) hReady hCode hb
    ⟨⟨⟨hRip, hw, hcodeApart⟩, by rw [ht]; decide⟩, hm⟩ hp ht hret

section Digest

variable [bindings : Bindings] {initial s : RamState} {input : ByteArray}

theorem input_stack_disjoint (hCall : Digest.ValidCall bindings initial input) :
    (Digest.inputRegion initial input).Disjoint (Stack.region initial Digest.minStackBytes) :=
  (hCall.separation.2 _ (by simp)).1 _ (by simp)

theorem input_size_bounded (hCall : Digest.ValidCall bindings initial input) :
    input.size < 2^64 := by
  have hb : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  omega

theorem Frame.inputBytes (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s) :
    (Digest.inputRegion initial input).HasBytes s.external input := by
  refine ⟨rfl, fun i ↦ ?_⟩
  apply Eq.trans _ (hCall.inputInMemory.2.2.2 i)
  apply h.agrees.byte
  intro c hc hcov
  simp only [digestPreparationChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  have hx := contains_of_mem_covers hCall.stackAvailable.1 hcov
  have hd := input_stack_disjoint hCall
  apply hd _ _ hx
  have hb : (Digest.inputRegion initial input).start + input.size < 2^32 :=
    hCall.inputInMemory.2.1
  change (Digest.inputRegion initial input).start ≤ _ ∧
    _ < (Digest.inputRegion initial input).start + input.size
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 2048 in
theorem memcpy_site_pre (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s) {offset length : Nat} {ret : BitVec 64}
    (hEnd : offset + length ≤ input.size) (hLength : length ≤ 63)
    (hBytes : (Digest.inputRegion initial input).HasBytes s.external input)
    (hdi : rdi.read s = stackPtr s + 184)
    (hsi : rsi.read s = initial.regValue .rdi + BitVec.ofNat 64 offset)
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 length)
    (hRetLow : ret.toNat < 2^32) (hRetOutside : ret.toNat < 0x103730) :
    MemcpySitePre ret s := by
  have hs := hCall.stackAvailable
  have hst := h.storage hCall
  have hlen : (MemoryRoutines.rdx.read s).toNat = length := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrcBound : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  have hsn : (rsi.read s).toNat = (initial.regValue .rdi).toNat + offset := by
    rw [hsi, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read s).toNat = (stackPtr s).toNat + 184 := by
    rw [hdi]
    exact h.address hs (by decide)
  have hlow := hst.stackLow
  have hhigh : (stackPtr s).toNat + 0x118 < 2^32 := hst.stackHigh
  have hfb : Finalize.Kind.frameBytes = 344 := rfl
  have hslot : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
    change (stackPtr s - 8).toNat = _
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · change 8 ≤ (stackPtr s).toNat
      omega
  have hw := h.scratchWritable hCall (AgreesExcept.refl [] s) 8 8 (by decide) (by decide)
  have hd := h.writable hCall (AgreesExcept.refl [] s) 184 length (by omega)
  have hsrc : MemReadable s (rsi.read s) length := by
    apply memReadable_of_allocated (Sha1.Proofs.Compress.allocated_of_hasBytes hBytes)
    · rw [hsn]
      omega
    · change (initial.regValue .rdi).toNat ≤ _
      rw [hsn]
      omega
    · change _ ≤ (initial.regValue .rdi).toNat + input.size
      rw [hsn]
      omega
  have hsep := input_stack_disjoint hCall
  have hstack := h.stackNat hs
  have hstackLow := (stack_bounds hs).1
  refine ⟨⟨h.df.df, ?_, hw.readable, hw.code, ?_, hRetLow, Or.inl hRetOutside⟩, ?_, ?_, ?_⟩
  · rw [hdi, hlen]
    exact hd
  · apply RangeApart.of_toNat
    · rw [hlen, hdn]
      omega
    · rw [hslot]
      omega
    · rw [hlen, hdn, hslot]
      omega
  · rw [hlen]
    exact hsrc
  · intro i hi j hj he
    rw [hlen] at hi
    apply hsep (rsi.read s + BitVec.ofNat 64 i).toNat
    · rw [toNat_add_ofNat _ _ (by rw [hsn]; omega), hsn]
      change (initial.regValue .rdi).toNat ≤ _ ∧
        _ < (initial.regValue .rdi).toNat + input.size
      omega
    · rw [he, toNat_add_ofNat _ _ (by rw [hslot]; omega), hslot, hstack]
      exact stack_region_contains hs (by omega) (by omega)
  · rw [hlen, hsn, hdn]
    apply Classical.byContradiction
    intro hnot
    have hcontain : (Digest.inputRegion initial input).Contains
        (max ((initial.regValue .rdi).toNat + offset) ((stackPtr s).toNat + 184)) := by
      change (initial.regValue .rdi).toNat ≤ _ ∧
        _ < (initial.regValue .rdi).toNat + input.size
      omega
    apply hsep _ hcontain
    exact stack_region_contains hs (by omega) (by omega)

theorem Frame.after_memcpy (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s) {t : RamState} {ret : BitVec 64}
    (hr : MemcpySiteResult (returnBoundary initial) ret s t)
    (hdi : rdi.read s = stackPtr s + 184)
    (hlen : (MemoryRoutines.rdx.read s).toNat ≤ 63) :
    Frame initial (returnBoundary initial) t := by
  have hs := hCall.stackAvailable
  have hst := h.storage hCall
  have hlow := hst.stackLow
  have hhigh : (stackPtr s).toNat + 0x118 < 2^32 := hst.stackHigh
  have hfb : Finalize.Kind.frameBytes = 344 := rfl
  apply h.preserve hs hr.agrees hr.ready hr.code
  · intro c hc hm
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, digestPreparationChanges]
  · intro c hc a hcov
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · obtain ⟨i, hi, rfl⟩ := hcov
      rw [hdi]
      change (Finalize.Kind.digestCopy.stackRegion s).Contains
        (stackPtr s + BitVec.ofNat 64 184 + BitVec.ofNat 64 i).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address hs (by omega)]
      change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _ ∧ _ < (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118)
      omega
    · obtain ⟨i, hi, rfl⟩ := hcov
      have hn : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
        rw [pushAddr, BitVec.toNat_sub_of_le]
        · rfl
        · change 8 ≤ (stackPtr s).toNat
          omega
      rw [toNat_add_ofNat _ _ (by rw [hn]; omega), hn]
      change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _ ∧ _ < (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118)
      omega
  · exact hr.rsp
  · exact hr.agrees.read (r := 3) (n := 64) (by simp [callSiteChanges])
  · exact hr.agrees.read (r := 14) (n := 64) (by simp [callSiteChanges])

end Digest

end Sha1.Proofs.Buffered.DigestPrepare
