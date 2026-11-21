import Sha1.Proofs.Buffered.DigestPrepare.Contracts
import Sha1.Proofs.Buffered.DigestPrepare.Short.Steps

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

set_option maxRecDepth 2048 in
theorem prepare_short [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hStride : UnitStringStride bindings) (hCall : Digest.ValidCall bindings initial input)
    (hp : Initialized initial (returnBoundary initial) input s)
    (hShort : input.size < 64) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      DigestPrepared initial (returnBoundary initial) input t := by
  have hs := hCall.stackAvailable
  obtain ⟨n, u, ha, hu, hip, h15, htail, hau⟩ := short_copied hStride hCall hp hShort
  have husp : stackPtr u = stackPtr s := hau.read (n := 64) (r := 4) (by simp [shortChanges])
  obtain ⟨v, hb, hv, hcv, he⟩ := position_store hCall hu (Or.inl rfl) hip
  have hvframe := hu.after_position_store hCall hv hcv he
  have hvsp : stackPtr v = stackPtr u :=
    he.agrees.read (n := 64) (r := 4) (by simp [positionStore])
  have hbytes : CodeIn (codeRange 0x100091 [0xeb, 0x47]) v :=
    Sha1.Proofs.Compress.Machine.program_text_slice hcv 0x91 2 (by decide +kernel)
  obtain ⟨t, hj, ht, hej⟩ := (jmp_rel8_effect_step 0x100091 0x47 (by decide +kernel)).advances
    hv hbytes he.rip (text_address_ne_return hp.boundaryOutside 0xda (by decide +kernel))
  have haj : AgreesExcept [.rip] v t := hej.agrees
  have hct := haj.codeIn (by simp [Component.Covers]) hcv
  have htsp : stackPtr t = stackPtr v := haj.read (n := 64) (r := 4) (by simp)
  have htframe : Frame initial (returnBoundary initial) t := by
    apply hvframe.preserve hs haj ht hct
    · simp [digestPreparationChanges]
    · simp [Component.Covers]
    · exact htsp
    · exact haj.read (n := 64) (r := 3) (by simp)
    · exact haj.read (n := 64) (r := 14) (by simp)
  have hag : AgreesExcept (shortChanges s input.size) s t := by
    have hag := (hau.trans he.agrees).trans haj
    simp only [positionStore, storeEffect_components, husp] at hag
    exact hag.mono (by simp [shortChanges])
  have hPosition : (Operand.mem (stackPtr s + 0xf7) : Operand 8).read t =
      BitVec.ofNat 8 input.size := by
    have hw := he.writes
    change (Operand.mem (stackPtr u + 0xf7) : Operand 8).read v =
      (Operand.reg 15 : Operand 8).read u at hw
    rw [husp] at hw
    have hm := haj.external (by simp [Component.Covers])
    change memLoad t.external (stackPtr s + 0xf7) 8 = _
    rw [hm]
    apply hw.trans
    have hh := congrArg (fun x : BitVec 64 ↦ x.setWidth 8) h15
    change (u.GPR[gprIndex 15]).setWidth 8 = _
    simpa only [Operand.read_reg64, BitVec.setWidth_ofNat_of_le (v := 8) (w := 64)
      (by decide)] using hh
  have hTail : (⟨(stackPtr s).toNat + 184, input.size⟩ : MemoryRegion).HasBytes
      t.external input := by
    have hm := haj.external (by simp [Component.Covers])
    rw [hm]
    refine ⟨rfl, fun i ↦ ?_⟩
    apply Eq.trans _ (htail.2 i)
    apply he.agrees.byte
    intro c hc hcov
    simp only [positionStore, storeEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hcov
      have hn := congrArg BitVec.toNat heq
      have hb' := stack_bounds hs
      have hsn := hp.toFrame.stackNat hs
      change (BitVec.ofNat 64 ((stackPtr s).toNat + 184 + i.val)).toNat =
        (stackPtr u + BitVec.ofNat 64 0xf7 + BitVec.ofNat 64 j).toNat at hn
      rw [husp, BitVec.add_assoc, ← BitVec.ofNat_add,
        hp.toFrame.address hs (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
      omega
    · exact hcov.elim
  have habs := short_absorbed hp.toFrame hs hShort hp.absorbed hag hTail hPosition
  have hcontext : stackPtr t + 0xb8 = stackPtr s + 0xb8 := by
    rw [htsp, hvsp, husp]
  refine ⟨n + 1 + 1, t, (ha.trans hb).trans hj,
    htframe.finish hCall hStride hej.rip ?_ (input_size_bounded hCall)⟩
  rw [hcontext]
  exact habs

end Sha1.Proofs.Buffered.DigestPrepare
