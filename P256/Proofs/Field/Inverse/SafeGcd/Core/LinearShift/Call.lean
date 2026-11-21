import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Routine
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

set_option maxHeartbeats 2000000 in
theorem linear_stage [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111220)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l116d00 initial).arguments
      initial.external (linearCall fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1115e6 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1170c6 final).arguments final.external
        (linearReturned fr controls p) := by
  simp only [linearCall, frameAtoms, outputAtoms, inputAtoms, bounds, Atom.all_append, Atom.All,
    Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn] at hcore
  obtain ⟨⟨⟨⟨⟨hrsp, hdf, hrbx, hrbp, hr12, hr13, hr14, hr15,
    hsave5, hsave14, hsave3, hreturn, hreturnRead, hreturnLow, hwrite, hroom, halign, _⟩,
    hshiftlo, hshifthi, _⟩, hmx, hfc, houtput, hsepout, _⟩,
    hwords1, hwords2, hsign1, hsign2, hread1, hread2, hsep1, hsep2, hu, hv, _⟩,
    hrdi, hrsi, hrdx, hrcx, hr8, hret, hslot, _⟩ := hcore
  have hsp : stackPtr initial = fr.rsp - 0x50 := Value.eq_bits hrsp
  have hdi : initial.regValue .rdi = fr.rsp - 0x48 := Value.eq_bits hrdi
  have hsi : initial.regValue .rsi = fr.rsi := Value.eq_bits hrsi
  have hcx : initial.regValue .rcx = fr.rcx := Value.eq_bits hrcx
  have hdx : initial.regValue .rdx = fr.rdx := Value.eq_bits hrdx
  have h8 : initial.regValue .r8 = fr.r8 := Value.eq_bits hr8
  have hret' : (returnBoundary initial).rip = 0x1115e6 := by
    change memLoad initial.external (stackPtr initial) 64 = _
    rwa [hsp]
  have hwindow : Writable code initial.external (stackPtr initial - 0x70) 0x70 := by
    rw [hsp]; exact hwrite.sub (by bv_omega) (by bv_omega)
  have hentry := Support.activation_entryAtoms LinearCombination.Machine.LinearCombination.frameInfo
    LinearCombination.Machine.lifted .l116d00 rfl (by rw [hret']; decide)
    (by rwa [hsp]) hwindow (by change 0x70 ≤ (stackPtr initial).toNat; rw [hsp]; bv_omega)
    (by rw [hsp]; bv_omega) (Reg.read_df_iff.1 hdf)
  have hinput : Atom.All code (LinearCombination.Machine.lifted.locationOf .l116d00 initial).arguments
      initial.external (LinearCombination.Machine.LinearCombination.frameAt .l116d00 (Support.activation initial 0x70) ++
        LinearCombination.commonAtoms (Support.activation initial 0x70) controls p.linear) := by
    rw [Atom.all_append]
    refine ⟨hentry, ?_⟩
    simp only [LinearCombination.commonAtoms, Support.activation, Atom.All, Atom.Holds,
      Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
    rw [hdi, hsi, hcx, hsp, hdx, h8]
    refine ⟨hmx, hfc, ?_, ?_, hwords1, hwords2, hsign1, hsign2, hread1, hread2, ?_, ?_, hu, hv, trivial⟩
    · exact hwrite.sub (by bv_omega) (by bv_omega)
    · right; bv_omega
    · bv_omega
    · bv_omega
  have hretCode : ∃ b, (0x1115e6, b) ∈ code :=
    ⟨_, hcode _ (Machine.code_l1170c6 _ (mem_codeRange _ _ 0 (by decide)))⟩
  obtain ⟨fuel, final, he, ready, hp, hw, hs, hr, mx, fc⟩ := LinearCombination.linear_advances hcode hready hrip
    (fr := Support.activation initial 0x70) (RamWriteFrame.refl _ _) hout
    (Or.inl (by change (returnBoundary initial).rip ≠ boundary.rip
                rw [hret']; exact ReturnOutside.ne hout hretCode)) hinput
  have hwithin : RegionsWithin [(Support.activation initial 0x70).region,
      LinearCombination.outputRegion (Support.activation initial 0x70)] [fr.region, outputRegion fr] := by
    intro r hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    all_goals refine ⟨fr.region, by simp, ?_, ?_⟩
    all_goals simp only [Activation.region, LinearCombination.outputRegion, Support.activation, hsp, hdi]
    all_goals bv_omega
  have loads (addr : BitVec 64) (ha : fr.rsp.toNat - 24 ≤ addr.toNat)
      (hb : addr.toNat + 8 ≤ fr.rsp.toNat + 8) :
      memLoad final.external addr 64 = memLoad initial.external addr 64 := by
    apply hp.frame.memLoad_eq
    constructor
    · have hh := hreturnRead.low; omega
    · intro r hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl
      all_goals right
      all_goals simp only [Activation.region, LinearCombination.outputRegion, Support.activation, hsp, hdi]
      all_goals bv_omega
  change WordsAt final.external (initial.regValue .rdi) 64 _ at hw
  change Readable final.external (initial.regValue .rdi) 41 at hr
  change memLoad final.external (initial.regValue .rdi + 40) 8 = _ at hs
  rw [hdi] at hw hs hr
  rw [show fr.rsp - 0x48 + 40 = fr.rsp - 0x20 by bv_omega] at hs
  have hspFinal := hp.rsp
  change (Reg.ofIndex 4).read final = ⟨64, stackPtr initial + 8⟩ at hspFinal
  rw [show stackPtr initial + 8 = fr.rsp - 0x48 by rw [hsp]; bv_omega] at hspFinal
  refine ⟨fuel, final, he, ready, hp.rip.trans hret', hframe.trans hp.frame hwithin, ?_⟩
  simp only [linearReturned, frameAtoms, outputAtoms, bounds, Atom.all_append, Atom.All, Atom.Holds,
    Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
  refine ⟨⟨⟨⟨hspFinal, Reg.read_df_iff.2 hp.df,
    (hp.preserved 3 (by decide)).trans hrbx, (hp.preserved 5 (by decide)).trans hrbp,
    (hp.preserved 12 (by decide)).trans hr12, (hp.preserved 13 (by decide)).trans hr13,
    (hp.preserved 14 (by decide)).trans hr14, (hp.preserved 15 (by decide)).trans hr15,
    ?_, ?_, ?_, ?_, hreturnRead.of_frame hp.frame, hreturnLow,
    hwrite.of_frame hp.frame, hroom, halign, trivial⟩, hshiftlo, hshifthi, trivial⟩,
    by change (⟨32, final.MXCSR⟩ : Value) = ⟨32, controls.MXCSR⟩; rw [mx],
    by change (⟨16, final.FP87_Control⟩ : Value) = ⟨16, controls.FP87_Control⟩; rw [fc],
    houtput.of_frame hp.frame, hsepout, trivial⟩, hw, hs, hr, trivial⟩
  · rw [loads _ (by bv_omega) (by bv_omega)]; exact hsave5
  · rw [loads _ (by bv_omega) (by bv_omega)]; exact hsave14
  · rw [loads _ (by bv_omega) (by bv_omega)]; exact hsave3
  · rw [loads _ (by bv_omega) (by bv_omega)]; exact hreturn

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
