import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Buffered.Update.SiteCalls
import Sha1.Proofs.Buffered.DigestPrepare.Long.Compression.Interface
import Sha1.Proofs.Compress.Routine.Public
import Sha1.Proofs.Common.Instructions.MovStore.Stack

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Common.Instructions
open Sha1.Proofs.Buffered.DigestPrepare.Long (CompressionCall compressionChanges)

structure SitePre [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (H : Vector (BitVec 32) 5) (block : ByteArray) (s : RamState) : Prop
    extends Storage .digestCopy s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = p
  boundaryOutside : ¬ InProgram boundary.rip
  df : DirectionFlagClear s.RFLAGS
  rdi : s.regValue .rdi = stackPtr s
  rsi : s.regValue .rsi = stackPtr s + 120
  rdx : s.regValue .rdx = 1
  size : block.size = 64
  block : (⟨(stackPtr s + 120).toNat, 64⟩ : MemoryRegion).HasBytes s.external block
  state : (⟨(stackPtr s).toNat, 20⟩ : MemoryRegion).HasBytes s.external
    (Wrapper.Hash.Serialize.stateBytes H)

structure SitePost [Bindings] (boundary : ReturnBoundary) (ret : BitVec 64)
    (H : Vector (BitVec 32) 5) (block : ByteArray) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = ret
  rsp : stackPtr t = stackPtr s
  state : (⟨(stackPtr s).toNat, 20⟩ : MemoryRegion).HasBytes t.external
    (Wrapper.Hash.Serialize.stateBytes (Wrapper.Absorb.compressBlocks H block))
  agrees : AgreesExcept (Kind.digestCopy.changes s) s t
  r12 : (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s
  r15 : (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s

theorem hasBytes_resize {m : Ram} {st n : Nat} {b : ByteArray}
    (h : (⟨st, n⟩ : MemoryRegion).HasBytes m b) (hn : n = b.size) :
    (⟨st, b.size⟩ : MemoryRegion).HasBytes m b := by
  subst hn
  exact h

theorem hasBytes_resize' {m : Ram} {st n : Nat} {b : ByteArray}
    (h : (⟨st, b.size⟩ : MemoryRegion).HasBytes m b) (hn : b.size = n) :
    (⟨st, n⟩ : MemoryRegion).HasBytes m b :=
  ⟨by change b.size = n; exact hn, h.2⟩

theorem covers_local_of_toNat {s : RamState} (h : Storage .digestCopy s) {x : BitVec 64}
    (hx : (stackPtr s).toNat - 344 ≤ x.toNat ∧ x.toNat < (stackPtr s).toNat + 280) :
    Component.Covers (.mem (stackPtr s - Kind.frameBytes)
      (Kind.frameBytes + Kind.digestCopy.stackBytes)) x := by
  have hl := h.stackLow
  have hfb := Kind.frameBytes_eq
  refine ⟨x.toNat - ((stackPtr s).toNat - 344), ?_, ?_⟩
  · simp only [Kind.stackBytes]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, h.belowAddress, BitVec.toNat_ofNat]
    have hx64 : x.toNat < 2^64 := x.isLt
    rw [Nat.mod_eq_of_lt (show x.toNat - ((stackPtr s).toNat - 344) < 2^64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

set_option maxRecDepth 4096 in
theorem compress_site [bindings : Bindings] (hBridge : CompressionCall)
    (hStride : UnitStringStride bindings) {boundary : ReturnBoundary} {p : BitVec 64}
    {disp : BitVec 32} {off : Nat} {H : Vector (BitVec 32) 5} {block : ByteArray}
    {s : RamState} (h : SitePre boundary p H block s)
    (hpo : p = Extracted.textAddress + BitVec.ofNat 64 off)
    (hoff : off + 5 ≤ Extracted.textBytes.size)
    (htarget : branchTarget p 5 (disp.signExtend 64) = 0x1024e0)
    (hbytes : CodeIn (codeRange p (encodeCallRel32 disp)) s)
    (hret : (p + BitVec.ofNat 64 5).toNat < 0x1024e0)
    (hretNe : p + BitVec.ofNat 64 5 ≠ boundary.rip) :
    ∃ t, SitePost boundary (p + BitVec.ofNat 64 5) H block s t := by
  have hl := h.stackLow
  have hfb := Kind.frameBytes_eq
  have hhigh : (stackPtr s).toNat + 0x118 < 2^32 := h.stackHigh
  have hal := h.stackAligned
  have hpr := h.toStorage.pushRange
  have hpush : (pushAddr s).toNat = (stackPtr s).toNat - 8 := h.toStorage.pushAddress
  have hpre : StorePre.PushPre p 5 s :=
    ⟨h.rip, ⟨hpr.readable.low, hpr.readable.mem, hpr.tables⟩,
      hpo ▸ rangeApart_text hpr.code hoff⟩
  have hstep := MovStore.call_rel32_effect_step p disp (by rw [htarget]; decide)
  obtain ⟨u, hcall, hu, he⟩ := hstep.advances h.ready hbytes hpre (by
    show branchTarget p 5 (disp.signExtend 64) ≠ boundary.rip
    rw [htarget]
    exact text_address_ne_return h.boundaryOutside 0x24e0 (by decide +kernel))
  have hcu := callEffect_code he h.code hpr.code
  have hret' := callEffect_returnBoundary he
  have husp : stackPtr u = pushAddr s := callEffect_rsp he
  have husn : (stackPtr u).toNat = (stackPtr s).toNat - 8 := by rw [husp, hpush]
  have hunchanged (x : BitVec 64)
      (hx : x.toNat < (stackPtr s).toNat - 8 ∨ (stackPtr s).toNat ≤ x.toNat) :
      u.external[x]? = s.external[x]? := by
    apply he.agrees.byte
    intro c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨j, hj, rfl⟩ := hcov
      rw [toNat_add_ofNat _ _ (by rw [hpush]; omega), hpush] at hx
      omega
    · exact hcov
  have hdi : u.regValue .rdi = stackPtr s := (callEffect_read he (r := 7) (by decide)).trans h.rdi
  have hsi : u.regValue .rsi = stackPtr s + 120 :=
    (callEffect_read he (r := 6) (by decide)).trans h.rsi
  have hdx : u.regValue .rdx = 1 := (callEffect_read he (r := 2) (by decide)).trans h.rdx
  have h120 : (stackPtr s + 120).toNat = (stackPtr s).toNat + 120 :=
    h.toStorage.stackAddress (offset := 120) (by decide)
  have hentry : u.RIP = 0x1024e0 := he.rip.trans htarget
  have hData : Sha1.Proofs.Compress.Routine.CallData ⟨u, H, block⟩ := by
    refine ⟨he.agrees.directionFlagClear (by simp [pushEffect_components]) ⟨h.df⟩,
      fun a b hm ↦ (hcu (a, b) hm).2, ?_, ?_, ?_, ?_, ?_⟩
    · change 64 * (u.regValue .rdx).toNat = block.size
      rw [hdx, h.size]
      rfl
    · change (⟨(u.regValue .rsi).toNat, block.size⟩ : MemoryRegion).start ≠ 0 ∧
        (⟨(u.regValue .rsi).toNat, block.size⟩ : MemoryRegion).Bounded ∧
        (⟨(u.regValue .rsi).toNat, block.size⟩ : MemoryRegion).HasBytes u.external block
      rw [hsi]
      have hb := hasBytes_resize h.block h.size.symm
      refine ⟨by change (stackPtr s + 120).toNat ≠ 0; rw [h120]; omega,
        by change (stackPtr s + 120).toNat + block.size < 2^32; rw [h120, h.size]; omega,
        hasBytes_of_copy (src := stackPtr s + 120) (dst := stackPtr s + 120) (fun i hi ↦ ?_) hb⟩
      apply hunchanged
      rw [h.size] at hi
      rw [toNat_add_ofNat _ _ (by rw [h120]; omega), h120]
      omega
    · change (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion).start ≠ 0 ∧
        (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion).Bounded ∧
        (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion).HasBytes u.external
          (Wrapper.Hash.Serialize.stateBytes H)
      rw [hdi]
      have hb := hasBytes_resize h.state (Wrapper.Hash.Serialize.stateBytes_size H).symm
      refine ⟨by change (stackPtr s).toNat ≠ 0; omega,
        by change (stackPtr s).toNat + 20 < 2^32; omega,
        hasBytes_resize' (hasBytes_of_copy (src := stackPtr s) (dst := stackPtr s)
          (fun i hi ↦ ?_) hb) (Wrapper.Hash.Serialize.stateBytes_size H)⟩
      apply hunchanged
      rw [Wrapper.Hash.Serialize.stateBytes_size] at hi
      rw [toNat_add_ofNat _ _ (by omega)]
      omega
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change (u.regValue .rsp).toNat - 336 +
          ((u.regValue .rsp).toNat + 8 - ((u.regValue .rsp).toNat - 336)) < 2^32
        change (stackPtr u).toNat - 336 + ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336)) < 2^32
        omega
      · intro address ha
        change (stackPtr u).toNat - 336 ≤ address.toNat ∧
          address.toNat < (stackPtr u).toNat - 336 +
            ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336)) at ha
        apply Option.isSome_iff_exists.mp
        apply he.agrees.grow
        apply Option.isSome_iff_exists.mpr
        apply h.stackAllocated
        change (stackPtr s).toNat - Kind.frameBytes ≤ address.toNat ∧
          address.toNat < (stackPtr s).toNat - Kind.frameBytes +
            (Kind.frameBytes + Kind.digestCopy.stackBytes)
        simp only [Kind.stackBytes]
        omega
      · change 336 ≤ (stackPtr u).toNat
        omega
      · change (stackPtr u).toNat % 16 = 8
        omega
    · have hinStack (address : Nat)
          (ha : (stackPtr s).toNat - 344 ≤ address ∧ address < (stackPtr s).toNat + 280) :
          (Kind.digestCopy.stackRegion s).Contains address := by
        change (stackPtr s).toNat - Kind.frameBytes ≤ address ∧
          address < (stackPtr s).toNat - Kind.frameBytes +
            (Kind.frameBytes + Kind.digestCopy.stackBytes)
        simp only [Kind.stackBytes]
        omega
      refine ⟨?_, ?_⟩
      · intro address ho hk
        change (u.regValue .rdi).toNat ≤ address ∧ address < (u.regValue .rdi).toNat + 20 at ho
        change (stackPtr u).toNat - 336 ≤ address ∧ address < (stackPtr u).toNat - 336 +
          ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336)) at hk
        rw [hdi] at ho
        omega
      · intro region hr
        simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        have hsub : ∀ address, region.Contains address →
            (stackPtr s).toNat - 344 ≤ address ∧ address < (stackPtr s).toNat + 20 := by
          rcases hr with rfl | rfl
          · intro address ha
            change (u.regValue .rdi).toNat ≤ address ∧
              address < (u.regValue .rdi).toNat + 20 at ha
            rw [hdi] at ha
            omega
          · intro address ha
            change (stackPtr u).toNat - 336 ≤ address ∧
              address < (stackPtr u).toNat - 336 +
                ((stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336)) at ha
            omega
        refine ⟨?_, fun address ha ↦ h.stackAvoids address (hinStack _ (by
          have := hsub _ ha; omega))⟩
        intro read hread address hra hrb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
        subst hread
        change (u.regValue .rsi).toNat ≤ address ∧
          address < (u.regValue .rsi).toNat + block.size at hra
        rw [hsi, h120, h.size] at hra
        have := hsub _ hrb
        omega
  obtain ⟨m, t, hadv, ht, hct, htrip, htsp, hag, hsaved, hout⟩ :=
    hBridge boundary hStride hu hcu
    hentry hData
    (by rw [hret']; show (p + BitVec.ofNat 64 5).toNat < userAddressLimit
        exact Nat.lt_trans hret (by decide))
    (by rw [hret']; exact Or.inl hret)
    (Sha1.Proofs.Compress.Routine.outsideCompression_of_notInProgram h.boundaryOutside)
    (by rw [hret']; exact hretNe.symm)
  rw [hret'] at htrip htsp
  have hsubset (c : Component)
      (hc : c ∈ Sha1.Proofs.Compress.Routine.compressionChanges ⟨u, H, block⟩) :
      c ∈ compressionChanges u := by
    simpa [Sha1.Proofs.Compress.Routine.compressionChanges, compressionChanges,
      Sha1.Proofs.Compress.Routine.Context.stack,
      Sha1.Proofs.Compress.Routine.Context.sp,
      Sha1.Proofs.Compress.Routine.frameComponents,
      Sha1.Proofs.Compress.Machine.scratchComponents] using hc
  have hag' : AgreesExcept (compressionChanges u) u t := by
    apply hag.widen
    · intro c hc hm
      exact hsubset c hc
    · intro x c hc hcov
      exact ⟨c, hsubset c hc, hcov⟩
  have hall : AgreesExcept ([.reg 4, .mem (pushAddr s) 8, .rip] ++ compressionChanges u) s t :=
    (he.agrees.mono (by intro c hc; simpa [pushEffect_components] using hc)).trans hag'
  have hwide : AgreesExcept ([.reg 4, .reg 3, .reg 5, .reg 13] ++
      Kind.digestCopy.changes s) s t := by
    apply hall.widen
    · intro c hc hm
      simp only [compressionChanges, Sha1.Proofs.Compress.Routine.frameComponents,
        Sha1.Proofs.Compress.Machine.scratchComponents, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      repeat' rcases hc with rfl | hc
      all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters]
    · intro x c hc hcov
      refine ⟨.mem (stackPtr s - Kind.frameBytes) (Kind.frameBytes + Kind.digestCopy.stackBytes),
        by simp [Kind.changes, Kind.localChanges], covers_local_of_toNat h.toStorage ?_⟩
      simp only [compressionChanges, Sha1.Proofs.Compress.Routine.frameComponents,
        Sha1.Proofs.Compress.Machine.scratchComponents, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      repeat' rcases hc with rfl | hc
      all_goals try exact hcov.elim
      all_goals obtain ⟨j, hj, rfl⟩ := hcov
      all_goals first
        | (rw [toNat_add_ofNat _ _ (by rw [hpush]; omega), hpush]; omega)
        | (have hreg : (Stack.region u Compress.minStackBytes).start =
              (stackPtr u).toNat - 336 := by
             change (stackPtr u).toNat - 336 = (stackPtr u).toNat - 336
           have hregSize : (Stack.region u Compress.minStackBytes).size = 344 := by
             change 336 + 8 = 344
             decide
           have hj' : j < 344 := by rw [hregSize] at hj; exact hj
           rw [hreg, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
             Nat.mod_eq_of_lt (by omega)]
           rw [husp, pushAddr]
           omega)
        | (change j < (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 336) at hj
           have hk : (BitVec.ofNat 64 (Stack.region u Compress.minStackBytes).start +
               BitVec.ofNat 64 j).toNat = (stackPtr u).toNat - 336 + j := by
             change (BitVec.ofNat 64 ((stackPtr u).toNat - 336) + BitVec.ofNat 64 j).toNat = _
             rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
           rw [hk]
           omega)
        | (simp at hj ⊢
           rw [husp, pushAddr] at *
           omega)
        | (rw [hdi]; bv_omega)
        | (rw [husp]; simp only [pushAddr] at *; bv_omega)
  have hsv3 : (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s :=
    (hsaved .rbx (by decide)).trans (callEffect_read he (r := 3) (by decide))
  have hsv5 : (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s :=
    (hsaved .rbp (by decide)).trans (callEffect_read he (r := 5) (by decide))
  have hsv12 : (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
    (hsaved .r12 (by decide)).trans (callEffect_read he (r := 12) (by decide))
  have hsv13 : (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s :=
    (hsaved .r13 (by decide)).trans (callEffect_read he (r := 13) (by decide))
  have hsv15 : (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s :=
    (hsaved .r15 (by decide)).trans (callEffect_read he (r := 15) (by decide))
  have hagree : AgreesExcept (Kind.digestCopy.changes s) s t := by
    apply hwide.narrow
    intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hn] at hc
    rcases hc with (rfl | rfl | rfl | rfl)
    · exact htsp
    · exact hsv3
    · exact hsv5
    · exact hsv13
  have ho : Compress.outputRegion u = ⟨(stackPtr s).toNat, 20⟩ := by
    change (⟨(u.regValue .rdi).toNat, 20⟩ : MemoryRegion) = _
    rw [hdi]
  rw [ho] at hout
  exact ⟨t, ⟨⟨1 + m, hcall.trans hadv⟩, ht, hct, htrip, htsp, hout, hagree,
    hsv12, hsv15⟩⟩

end Sha1.Proofs.Buffered.Finalize.Digest
