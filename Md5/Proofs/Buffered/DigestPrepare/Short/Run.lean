import Md5.Proofs.Buffered.DigestPrepare.Short
import Md5.Proofs.Buffered.DigestPrepare.Short.Invariant
import Md5.Proofs.Buffered.DigestPrepare.Copy
import Md5.Proofs.Buffered.DigestPrepare.Position

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 2048 in
theorem short_ready [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hShort : input.size < 64) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Frame initial (returnBoundary initial) t ∧
      t.RIP = 0x100078 ∧ rdi.read t = stackPtr t + 176 ∧
      rsi.read t = initial.regValue .rdi ∧
      MemoryRoutines.rdx.read t = BitVec.ofNat 64 input.size ∧
      (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 input.size ∧
      AgreesExcept [.reg 2, .reg 7, .flags, .rip] s t := by
  obtain ⟨u, ha, hu, hcu, hurip, hau⟩ := entry_branch h.ready h.code h.boundaryOutside h.rip
    (input_size_bounded hCall) h.inputSize
  have hurip' : u.RIP = 0x10006d := by
    simpa only [ite_eq_right (show ¬64 ≤ input.size by omega)] using hurip
  have hb : CodeIn (codeRange 0x10006d shortCopyBytes) u :=
    program_text_slice hcu 0x6d 11 (by decide +kernel)
  obtain ⟨n, t, hat, ht, _, he⟩ := short_copy_prepare (returnBoundary initial)
    h.boundaryOutside u hu hb hurip'
  have hct := he.agrees.codeIn (by simp [shortCopyEffect, Effect.components, Component.Covers]) hcu
  have hag : AgreesExcept [.reg 2, .reg 7, .flags, .rip] s t := by
    apply (hau.trans he.agrees).mono
    simp [shortCopyEffect, Effect.components]
  have hsp : stackPtr t = stackPtr s := hag.read (n := 64) (r := 4) (by simp)
  have husp : stackPtr u = stackPtr s := hau.read (n := 64) (r := 4) (by simp)
  have hframe : Frame initial (returnBoundary initial) t := by
    apply h.toFrame.preserve hCall.stackAvailable hag ht hct
    · simp [digestPreparationChanges]
    · simp [Component.Covers]
    · exact hsp
    · exact hag.read (n := 64) (r := 3) (by simp)
    · exact hag.read (n := 64) (r := 14) (by simp)
  refine ⟨2 + n, t, ha.trans hat, hframe, he.rip, ?_, ?_, ?_, ?_, hag⟩
  · rw [he.writes.1, husp, hsp]
  · exact (hag.read (n := 64) (r := 6) (by simp)).trans h.inputPointer
  · exact he.writes.2.trans ((hau.read (n := 64) (r := 15) (by simp)).trans h.inputSize)
  · exact (hag.read (n := 64) (r := 15) (by simp)).trans h.inputSize

set_option maxRecDepth 2048 in
theorem short_copied [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hShort : input.size < 64) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Frame initial (returnBoundary initial) t ∧ t.RIP = 0x10007e ∧
      (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 input.size ∧
      (⟨(stackPtr s).toNat + 176, input.size⟩ : MemoryRegion).HasBytes t.external input ∧
      AgreesExcept (shortChanges s input.size) s t := by
  obtain ⟨n, u, ha, hu, hip, hdi, hsi, hdx, h15, hau⟩ := short_ready hCall h hShort
  have hspu : stackPtr u = stackPtr s := hau.read (n := 64) (r := 4) (by simp)
  have hb := hu.inputBytes hCall
  have hp : MemcpySitePre 0x10007e u :=
    memcpy_site_pre hCall hu (offset := 0) (by omega) (by omega) hb hdi
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hsi) hdx
      (by decide) (by decide)
  have hw := hu.scratchWritable (AgreesExcept.refl [] u) 8 8 (by decide) (by decide)
  obtain ⟨t, hr⟩ := memcpy_call hStride hu.ready hu.code hu.boundaryOutside hip
    (Or.inl rfl) hp ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
  have hlen : (MemoryRoutines.rdx.read u).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨m, hradv⟩ := hr.advances
  refine ⟨n + m, t, ha.trans hradv,
    hu.after_memcpy hCall hr hdi (by rw [hlen]; omega), hr.rip, ?_, ?_, ?_⟩
  · exact (hr.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges])).trans h15
  · have hbytes : (⟨(rsi.read u).toNat, input.size⟩ : MemoryRegion).HasBytes u.external input := by
      rw [hsi]
      exact hb
    have hout := hr.hasBytes hlen hbytes
    have hn : (stackPtr u + 176).toNat = (stackPtr u).toNat + 176 := by
      simpa only [BitVec.ofNat_eq_ofNat] using hu.address (offset := 176) (by decide)
    rw [hdi, hn, hspu] at hout
    exact hout
  · have hag := hau.trans hr.agrees
    rw [callSiteChanges, hdi, hlen, pushAddr, hspu] at hag
    exact hag.mono (by simp [shortChanges, pushAddr])


set_option maxRecDepth 2048 in
theorem prepare_short [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hShort : input.size < 64) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  obtain ⟨n, u, ha, hu, hip, h15, htail, hau⟩ := short_copied hStride hCall h hShort
  have husp : stackPtr u = stackPtr s := hau.read (n := 64) (r := 4) (by simp [shortChanges])
  obtain ⟨v, hb, hv, hcv, he⟩ := position_store hu (Or.inl rfl) hip
  have hvframe := hu.after_position_store hCall hv hcv he
  have hvsp : stackPtr v = stackPtr u := he.agrees.read (n := 64) (r := 4) (by simp)
  have hbytes : CodeIn (codeRange 0x100086 [0xeb, 0x47]) v :=
    program_text_slice hcv 0x86 2 (by decide +kernel)
  obtain ⟨t, hj, ht, hej⟩ := (jmp_rel8_effect_step 0x100086 0x47 (by decide +kernel)).advances
    hv hbytes he.rip (text_address_ne_return h.boundaryOutside 0xcf (by decide +kernel))
  have haj : AgreesExcept [.rip] v t := hej.agrees
  have hct := haj.codeIn (by simp [Component.Covers]) hcv
  have htsp : stackPtr t = stackPtr v := haj.read (n := 64) (r := 4) (by simp)
  have htframe : Frame initial (returnBoundary initial) t := by
    apply hvframe.preserve hCall.stackAvailable haj ht hct
    · simp [digestPreparationChanges]
    · simp [Component.Covers]
    · exact htsp
    · exact haj.read (n := 64) (r := 3) (by simp)
    · exact haj.read (n := 64) (r := 14) (by simp)
  have hag : AgreesExcept (shortChanges s input.size) s t := by
    have hag := (hau.trans he.agrees).trans haj
    simp only [storeEffect_components, husp] at hag
    exact hag.mono (by simp [shortChanges])
  have hPosition : (Operand.mem (stackPtr s + 239) : Operand 8).read t =
      BitVec.ofNat 8 input.size := by
    have hp := he.writes
    change (Operand.mem (stackPtr u + 239) : Operand 8).read v =
      (Operand.reg 15 : Operand 8).read u at hp
    rw [husp] at hp
    have hm := haj.external (by simp [Component.Covers])
    change memLoad t.external (stackPtr s + 239) 8 = _
    rw [hm]
    apply hp.trans
    have hh := congrArg (fun x : BitVec 64 ↦ x.setWidth 8) h15
    change (u.GPR[gprIndex 15]).setWidth 8 = _
    simpa only [Operand.read_reg64, BitVec.setWidth_ofNat_of_le (v := 8) (w := 64)
      (by decide)] using hh
  have hTail : (⟨(stackPtr s).toNat + 176, input.size⟩ : MemoryRegion).HasBytes
      t.external input := by
    have hm := haj.external (by simp [Component.Covers])
    rw [hm]
    refine ⟨rfl, fun i ↦ ?_⟩
    apply Eq.trans _ (htail.2 i)
    apply he.agrees.byte
    intro c hc hcov
    simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hcov
      have hn := congrArg BitVec.toNat heq
      have hhigh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
      change (BitVec.ofNat 64 ((stackPtr s).toNat + 176 + i.val)).toNat =
        (stackPtr u + BitVec.ofNat 64 239 + BitVec.ofNat 64 j).toNat at hn
      rw [husp, BitVec.add_assoc, ← BitVec.ofNat_add,
        h.toFrame.address (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
      omega
    · exact hcov.elim
  have habs := short_absorbed h.toFrame hShort h.absorbed hag hTail hPosition
  have hcontext : Finalize.Kind.digest.context t = Finalize.Kind.digest.context s := by
    simp only [Finalize.Kind.context, htsp, hvsp, husp]
  refine ⟨n + 1 + 1, t, (ha.trans hb).trans hj,
    htframe.finish hStride hej.rip ?_ (input_size_bounded hCall)⟩
  rw [hcontext]
  exact habs

end Md5.Proofs.Buffered.DigestPrepare
