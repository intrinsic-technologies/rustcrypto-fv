import Sha3.Proofs.Memory
import X86Proofs.Instructions.Call.Triple

namespace Sha3.Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Prelude Sha3.Spec.Program

theorem call_operation_rel_of_readable [Bindings] (t : RamState) (ctx : Instruction_Context)
    (off : BitVec 64)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hmode : In64BitMode t)
    (htarget : (BitVec.add t.Next_IP off).toNat < 2^32) (hw : MemReadable t (pushAddr t) 8)
    (hpage : (pushAddr t).toNat % 4096 + 8 ≤ 4096) :
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
  spec_bind_with (pushStack_run_of_readable t h hss (stackPtr t) t.Next_IP hw hpage)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (rspWrite_run _ _)
  spec_bind_with (branchNear_run _ _)
  spec_bind_with (get_run _)
  spec_bind_with hend
  rfl

theorem call_operation_abs_of_readable [Bindings] (t : RamState) (ctx : Instruction_Context)
    (target : BitVec 64) (noTrack : Bool)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (htarget : target.toNat < 2^32) (hw : MemReadable t (pushAddr t) 8)
    (hpage : (pushAddr t).toNat % 4096 + 8 ≤ 4096) :
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
  spec_bind_with (pushStack_run_of_readable t h hss (stackPtr t) t.Next_IP hw hpage)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (rspWrite_run _ _)
  spec_bind_with (branchNear_run _ _)
  spec_bind_with (get_run _)
  spec_bind_with hend
  simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem call_rel32_form_of_readable [Bindings] (u v : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (disp : BitVec 32) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 32).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (h : DataReady v) (hss : v.SS = userStackSegment)
    (htarget : (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64)).toNat < 2^32)
    (hw : MemReadable v (pushAddr v) 8)
    (hpage : (pushAddr v).toNat % 4096 + 8 ≤ 4096) :
    (X86.Instructions.CALL_NEAR_RELBRd ip ctx).run u =
      (.ok (), callState (withNextIP v (BitVec.add ip 4#64)) (BitVec.add ip 4#64)
        (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.CALL_NEAR_RELBRd
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 4)) _ (s := v)
    (value := BitVec.add ip 4#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 4#64))
    (value := ()) rfl).trans ?_
  exact call_operation_rel_of_readable _ ctx _ (h.withNextIP _) hss
    (hmode.of_cs_lma_eq rfl rfl) htarget
    (hw.of_external_eq rfl) hpage

theorem call_r_form_of_readable [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment)
    (htarget : ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read t).toNat <
      2^32)
    (hw : MemReadable t (pushAddr t) 8)
    (hpage : (pushAddr t).toNat % 4096 + 8 ≤ 4096) :
    (X86.Instructions.CALL_NEAR_GPRv ip ctx rm).run t =
      (.ok (), callState (withNextIP t ip) ip
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read t)) := by
  have hcontext : ({ ctx with is_mode64 := true, lock_prefix_present := false } :
      Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  simp only [Operand.read_reg64] at htarget ⊢
  unfold X86.Instructions.CALL_NEAR_GPRv
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CALL_NEAR => call_operation_abs_of_readable (withNextIP t ip) _ _ _
      (h.withNextIP ip) hss htarget (hw.of_external_eq rfl) hpage]

theorem call_m_form_of_readable [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hmode64 : ctx.is_mode64 = true) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hread : MemReadable t addr 8)
    (htarget : ((Operand.mem addr : Operand 64).read t).toNat < 2^32)
    (hw : MemReadable t (pushAddr t) 8)
    (hpage : (pushAddr t).toNat % 4096 + 8 ≤ 4096) :
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
    h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl h.tables
  unfold X86.Instructions.CALL_NEAR_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread',
    X86.Instructions.Operations.CALL_NEAR => call_operation_abs_of_readable _ _ _ _ hd hss htarget
      (hw.of_external_eq rfl) hpage]

theorem call_rel32_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (disp : BitVec 32)
    (hcode : BytesAt s s.RIP (0xE8 :: immBytes 32 disp)) (hlow : s.RIP.toNat + 5 ≤ 2^32)
    (htarget : (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)).toNat < 2^32)
    (hw : MemReadable s (pushAddr s) 8)
    (hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096) :
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      callState (callFrom false t (BitVec.add s.RIP 5#64)) (BitVec.add s.RIP 5#64)
        (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xE8 :: immBytes 32 disp) := hcode
  have hlow' : s.RIP.toNat + (0xE8 :: immBytes 32 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xE8, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by simp)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 32).run (afterFetches (beforeFetch s) 2) =
      (.ok disp, afterFetches (beforeFetch s) 6) :=
    memFetch_run_of_bytesAt_imm (beforeFetch s) 2 hf hc hlow' 32 (by decide) disp 1
      (immBytes_getElem?_append [0xE8] disp) (by simp) (by decide)
  obtain ⟨hd, hss⟩ := call_start h 6
  have hdecode := decodeLegacy0_run_of_opcodeE8 _ _ _ (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeE8_run_of_call _ _ _ (hmode 2) (hfeatures 2)] at hdecode
  rw [call_rel32_form_of_readable _ _ _ _ disp rfl rfl f2 (hmode 6) hd hss
    (by rw [add_ofNat_add]; exact htarget) (hw.of_external_eq rfl) hpage, add_ofNat_add] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h _ (immBytes 32 disp)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    ((hmode 6).of_cs_lma_eq rfl rfl)

theorem call_r64_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hcode : BytesAt s s.RIP (pre ++ [0xFF, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (htarget : ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3 (modrmRm modrm)) : Operand 64).read s).toNat < 2^32)
    (hw : MemReadable s (pushAddr s) 8)
    (hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      callState (callFrom false t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (src.read s))) := by
  intro ctx src
  have hlen' : (pre ++ [0xFF, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xFF, modrm]).length ≤ 2^32 := by rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_FF_call_register s h _ pre.length modrm hmod hreg hcode hlow'
    (by simp) (by simp) (by omega) ctx hrex2
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 3)
  rw [call_r_form_of_readable _ _ _ _ hmode64 hlock hmode hd hss htarget
    (hw.of_external_eq rfl) hpage] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem call_m64_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 2 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 8)
    (htarget : ((Operand.mem (am.addrAt s (pre.length + 2 + am.tail.length)) :
      Operand 64).read s).toNat < 2^32)
    (hw : MemReadable s (pushAddr s) 8)
    (hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096) :
    let L := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s L fun t =>
      callState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 L)))
        (BitVec.add s.RIP (BitVec.ofNat 64 L))
        ((Operand.mem (am.addrAt s L) : Operand 64).read s))) := by
  intro L
  have hlen' : (pre ++ 0xFF :: am.modrm 2 :: am.tail).length = L := by simp [L]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 2 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_call_memory s h _ pre.length (am.modrm 2)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0xFF 2 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = L + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (L + 1)
  obtain ⟨hd, hss⟩ := call_start h (L + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 L))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [call_m_form_of_readable _ t _ _ _ _ hctx.mode64 haddr hlock _ _ _ _ _ hea hrip hd hss
    (hread.of_external_eq rfl) htarget (hw.of_external_eq rfl) hpage] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)


theorem afterStep_call_memoryWriteFrame {k : Nat} (s : RamState) (load : Bool)
    (length : Nat) (nextIP target : BitVec 64) (regions : Vector MemoryRegion k)
    (hwrite : ∀ i, i < 8 → ∃ region ∈ regions,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat) :
    MemoryWriteFrame s
      (afterStep s length fun t ↦ callState (callFrom load t nextIP) nextIP target) regions := by
  intro address hout
  rw [afterStep_call_external]
  exact memoryWriteFrame_memStore s (pushAddr s) nextIP regions hwrite address hout

theorem afterStep_call_readyToStep_of_avoids [Bindings] {k : Nat} {s : RamState}
    (h : ReadyToStep s) (load : Bool) (length : Nat) (nextIP target : BitVec 64)
    (regions : Vector MemoryRegion k)
    (hwrite : ∀ i, i < 8 → ∃ region ∈ regions,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat)
    (havoid : ∀ region ∈ regions, region.Avoids InPageTables) :
    ReadyToStep
      (afterStep s length fun t ↦ callState (callFrom load t nextIP) nextIP target) := by
  have hstored := readyToStep_memStore_of_avoids s (pushAddr s) nextIP regions h hwrite havoid
  apply h.of_agreesExcept (AgreesExcept.afterStep_call s load length nextIP target)
  rw [afterStep_call_external]
  exact hstored.memory.tables

theorem call_effect_step_of_avoids [Bindings] {pre : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len k : Nat} (load : Bool) (target : RamState → BitVec 64)
    (regions : RamState → Vector MemoryRegion k)
    (hwrite : ∀ s, pre s → ∀ i, i < 8 → ∃ region ∈ regions s,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat)
    (havoid : ∀ s, pre s → ∀ region ∈ regions s, region.Avoids InPageTables)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → pre s →
      Machine.step s = some (.next (afterStep s len fun t ↦
        callState (callFrom load t (p + BitVec.ofNat 64 len))
          (p + BitVec.ofNat 64 len) (target s)))) :
    StepEffect pre (codeRange p bytes) (callEffect target (p + BitVec.ofNat 64 len)) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    afterStep_call_readyToStep_of_avoids h load len _ _ (regions s)
      (hwrite s hpre) (havoid s hpre),
    ⟨afterStep_call_rip _ _ _ _ _, ⟨Operand.read_afterStep_call_rsp _ _ _ _ _,
      Operand.read_afterStep_call_mem _ _ _ _ _⟩, trivial,
      (pushEffect_components _ _ s).symm ▸ AgreesExcept.afterStep_call _ _ _ _ _⟩⟩

section

variable [Bindings] {pre : RamState → Prop} {p : BitVec 64} {k : Nat}
  (regions : RamState → Vector MemoryRegion k)
  (hwrite : ∀ s, pre s → ∀ i, i < 8 → ∃ region ∈ regions s,
    region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat)
  (havoid : ∀ s, pre s → ∀ region ∈ regions s, region.Avoids InPageTables)

include regions hwrite havoid

theorem call_rel32_effect_step_of_readable (disp : BitVec 32)
    (hpre : ∀ s, pre s → LoadPre p pushAddr 8 s)
    (hpage : ∀ s, pre s → (pushAddr s).toNat % 4096 + 8 ≤ 4096)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect pre (codeRange p (encodeCallRel32 disp))
      (callEffect (fun _ ↦ branchTarget p 5 (disp.signExtend 64)) (p + 5)) := by
  refine call_effect_step_of_avoids false _ regions hwrite havoid ?_
  intro s h hcode hs
  have hp := (hpre s hs).rip
  have hr := (hpre s hs).read
  subst hp
  exact call_rel32_step_of_readable s h disp hcode.bytesAt
    (hcode.low (by simp [encodeCallRel32]) (by simp [encodeCallRel32]))
    htarget hr (hpage s hs)

theorem call_m64_effect_step_of_readable (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hpre : ∀ s, pre s → LoadPre p pushAddr 8 s)
    (hpage : ∀ s, pre s → (pushAddr s).toNat % 4096 + 8 ≤ 4096)
    (hread : ∀ s, pre s →
      MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8)
    (htarget : ∀ s, pre s → (callMemPtr p am s).toNat < 2^32) :
    StepEffect pre (codeRange p (encodeCallM64 am))
      (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) := by
  refine call_effect_step_of_avoids true _ regions hwrite havoid ?_
  intro s h hcode hs
  have hp := (hpre s hs).rip
  have hr := (hpre s hs).read
  subst hp
  have h5 := am.tail_length_le
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have hc := hcode.low (by simp [encodeCallM64]) (by simp [encodeCallM64]; omega)
    simp only [encodeCallM64, List.length_cons] at hc
    omega
  exact call_m64_step_of_readable s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow (hread s hs) (htarget s hs)
    hr (hpage s hs)

theorem call_m64_rip_effect_step_of_readable (disp : BitVec 32)
    (hpre : ∀ s, pre s → LoadPre p pushAddr 8 s)
    (hpage : ∀ s, pre s → (pushAddr s).toNat % 4096 + 8 ≤ 4096)
    (hread : ∀ s, pre s →
      MemReadable s ((AddrMode.rip disp).addr s (p + 6)) 8)
    (htarget : ∀ s, pre s → (callMemPtr p (.rip disp) s).toNat < 2^32) :
    StepEffect pre (codeRange p (encodeCallM64 (.rip disp)))
      (callEffect (callMemPtr p (.rip disp)) (p + 6)) :=
  call_m64_effect_step_of_readable regions hwrite havoid (.rip disp) trivial rfl rfl
    hpre hpage hread htarget

end

end Sha3.Proofs
