import Sha1.Proofs.Buffered.DigestPrepare.Copy
import Sha1.Proofs.Common.Instructions.Store
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

abbrev ByteWritable (s : RamState) (address : BitVec 64) : Prop :=
  Sha1.Proofs.Common.Instructions.StorePre.MemWritable s address 1

theorem byteStore_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : ByteWritable t lin) :
    (X86.Instructions.MOV_MEMb_GPR8_1 ip ctx mod reg rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 8) (movSpec (src.read t))
        next) := by
  have hcontext :
      {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 8 (by decide)
    ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMb_GPR8_1
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

theorem byteStore_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4
        (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3 reg).toNat < 4)
    (hcode : BytesAt s s.RIP (pre ++ 0x88 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hw : ByteWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 2 + am.tail.length)))) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 2 + am.tail.length))
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 8) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x88 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x88 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_88_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ pre.length (by omega)
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      (pre ++ 0x88 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      (pre ++ 0x88 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h pre 0x88 reg am hv [] _ hctx hcode2 hlow2 (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  rw [byteStore_form _ _ _ _ _ _ _ hreg haddr hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _)
    (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x88 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem byteStore_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := byteStore_step s h [rex] (by simpa using hr.scanPrefix)
        (by simp)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
        (.inl (by rw [scanContext_rex _ _ hr]; rfl))
        hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
      simp only [scanContext_rex _ _ hr] at hstep
      have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
          (rexContext s.DS rex.toBitVec).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem store_avoids_program {e : Effect} {addr : BitVec 64} {len : Nat}
    (hc : e.components = [.mem addr len, .rip])
    (ha : ∀ i < len, ¬ InProgram (addr + BitVec.ofNat 64 i)) :
    e.Avoids Extracted.programImage := by
  intro x hx c hm hcov
  rw [hc] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · obtain ⟨i, hi, he⟩ := hcov
    exact ha i hi ⟨x.2, he ▸ hx⟩
  · exact hcov

def positionStore (p : BitVec 64) (s : RamState) : Effect :=
  storeEffect p 8 (fun u ↦ stackPtr u + 0xf7) (fun u ↦ (Operand.reg 15 : Operand 8).read u) s

theorem position_store [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    {boundary : ReturnBoundary} (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial boundary s) {p : BitVec 64}
    (hsite : p = 0x100089 ∨ p = 0x1000be) (hrip : s.RIP = p) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (positionStore p s).Holds s t := by
  have hw := h.writable hCall (AgreesExcept.refl [] s) 0xf7 1 (by decide)
  have hp : Sha1.Proofs.Common.Instructions.StorePre.StorePre p 8
      (fun u ↦ stackPtr u + 0xf7) 1 s := by
    refine ⟨hrip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, ?_⟩
    rcases hsite with rfl | rfl
    · exact rangeApart_text hw.code (by decide +kernel : 0x89 + 8 ≤ Extracted.textBytes.size)
    · exact rangeApart_text hw.code (by decide +kernel : 0xbe + 8 ≤ Extracted.textBytes.size)
  have hb : CodeIn (codeRange p [0x44, 0x88, 0xbc, 0x24, 0xf7, 0, 0, 0]) s := by
    rcases hsite with rfl | rfl
    · exact Sha1.Proofs.Compress.Machine.program_text_slice h.code 0x89 8 (by decide +kernel)
    · exact Sha1.Proofs.Compress.Machine.program_text_slice h.code 0xbe 8 (by decide +kernel)
  have hstep := byteStore_rex_effect_step p 0x44
    (by unfold RexPrefix; decide) 7 (.sib 4 none 0 (.d32 0xf7))
    (by decide) (by decide) (by decide)
  change StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p 8
      (fun u ↦ stackPtr u + 0xf7) 1)
    (codeRange p [0x44, 0x88, 0xbc, 0x24, 0xf7, 0, 0, 0]) (positionStore p) at hstep
  have hne : p + 8 ≠ boundary.rip := by
    rcases hsite with rfl | rfl
    · exact text_address_ne_return h.boundaryOutside 0x91 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0xc6 (by decide +kernel)
  obtain ⟨t, ha, ht, he⟩ := hstep.advances h.ready hb hp hne
  refine ⟨t, ha, ht, he.codeIn ?_ h.code, he⟩
  exact store_avoids_program rfl (by simpa using hw.code)

theorem Frame.after_position_store [bindings : Bindings] {initial s t : RamState}
    {input : ByteArray} {p : BitVec 64}
    (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s)
    (ht : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (he : (positionStore p s).Holds s t) :
    Frame initial (returnBoundary initial) t := by
  have hs := hCall.stackAvailable
  have hst := h.storage hCall
  apply h.preserve hs he.agrees ht hc
  · intro c hc hm
    simp only [positionStore, storeEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · cases hm
    · simp [digestPreparationChanges]
  · intro c hc address hcov
    simp only [positionStore, storeEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcov
      change (Finalize.Kind.digestCopy.stackRegion s).Contains
        (stackPtr s + BitVec.ofNat 64 0xf7 + BitVec.ofNat 64 i).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address hs (by omega)]
      have := hst.stackLow
      change (stackPtr s).toNat - Finalize.Kind.frameBytes ≤ _ ∧ _ < (stackPtr s).toNat - Finalize.Kind.frameBytes + (Finalize.Kind.frameBytes + 0x118)
      omega
    · exact hcov.elim
  · exact he.agrees.read (n := 64) (r := 4) (by simp [positionStore])
  · exact he.agrees.read (n := 64) (r := 3) (by simp [positionStore])
  · exact he.agrees.read (n := 64) (r := 14) (by simp [positionStore])

end Sha1.Proofs.Buffered.DigestPrepare
