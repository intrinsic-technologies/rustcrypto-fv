import P256.Proofs.Scalar.Inverse.Wrapper.Defs

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

set_option maxHeartbeats 2000000 in
theorem core_stage [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111b70)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l117650 initial).arguments
      initial.external (coreCall fr p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112e5a ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l11893a final).arguments final.external
        (coreReturned fr p) := by
  simp only [coreCall, frameAtoms, outputAtoms, inputAtoms, Atom.all_append, Atom.All,
    Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn] at hcore
  obtain ⟨⟨⟨⟨hrsp, hdf, hrbx, hrbp, hr12, hr13, hr14, hr15,
    hsave, hreturn, hreturnRead, hreturnLow, hwrite, hroom, halign, hmx, hfc, _⟩,
    houtput, hsepout, _⟩, hwords, hread, hsep, hmod, hscale, hmodread, hscaleread, hmodsep, hscalesep, _⟩,
    hrdi, hrsi, hrdx, hrcx, hr8, hret, hslot, _⟩ := hcore
  have hsp : stackPtr initial = fr.rsp - 0x40 := Value.eq_bits hrsp
  have hdi : initial.regValue .rdi = fr.rsp - 0x30 := Value.eq_bits hrdi
  have hsi : initial.regValue .rsi = fr.rsi := Value.eq_bits hrsi
  have hcx : initial.regValue .rcx = 0x332e375511ff43b1 := Value.eq_bits hrcx
  have hdx : initial.regValue .rdx = 0x2025e0 := Value.eq_bits hrdx
  have h8 : initial.regValue .r8 = 0x2025c0 := Value.eq_bits hr8
  have hret' : (returnBoundary initial).rip = 0x112e5a := by
    change memLoad initial.external (stackPtr initial) 64 = _
    rwa [hsp]
  have hwindow : Writable code initial.external (stackPtr initial - 0x2c0) 0x2c0 := by
    rw [hsp]; exact hwrite.sub (by bv_omega) (by bv_omega)
  have hentry := Core.Support.activation_entryAtoms Core.Machine.Core.frameInfo
    Core.Machine.lifted .l117650 rfl (by rw [hret']; decide)
    (by rwa [hsp]) hwindow (by change 0x2c0 ≤ (stackPtr initial).toNat; rw [hsp]; bv_omega)
    (by rw [hsp]; bv_omega) (Reg.read_df_iff.1 hdf)
  have hinput : Atom.All code (Core.Machine.lifted.locationOf .l117650 initial).arguments
      initial.external (Core.Prefix.atoms .entry (Core.Support.activation initial 0x2c0) initial
        (scalarInput p)) := by
    change Atom.All _ _ _ ((Core.Machine.Core.frameAt .l117650 (Core.Support.activation initial 0x2c0) ++
      [.reg 39 ⟨32, initial.MXCSR⟩, .reg 51 ⟨16, initial.FP87_Control⟩]) ++ _)
    rw [Atom.all_append, Atom.all_append]
    refine ⟨⟨hentry, (Vector.getElem_ofFn _).trans rfl,
      (Vector.getElem_ofFn _).trans rfl, trivial⟩, ?_⟩
    simp only [Core.commonAtoms, Core.outputAtoms, Core.inputAtoms, Core.Support.activation, Atom.all_append, Atom.All, Atom.Holds]
    rw [hdi, hsi, hcx, hsp, hdx, h8]
    refine ⟨⟨hwrite.sub (by bv_omega) (by bv_omega), Or.inr (by bv_omega), trivial⟩,
      hwords, hmod, hscale, hread, hmodread, hscaleread, ?_, ?_, ?_, rfl, trivial⟩
    · rcases hsep with h | h
      · left; bv_omega
      · right; bv_omega
    · rcases hmodsep with h | h
      · left; bv_omega
      · right; bv_omega
    · rcases hscalesep with h | h
      · left; bv_omega
      · right; bv_omega
  have hretCode : ∃ b, (0x112e5a, b) ∈ code :=
    ⟨_, hcode _ (Machine.code_l11893a _ (mem_codeRange _ _ 0 (by decide)))⟩
  obtain ⟨fuel, final, he, ready, hp, hw, hc, hr, hmxFinal, hfcFinal⟩ := Core.advances hcode hready hrip
    (fr := Core.Support.activation initial 0x2c0) (controls := initial) (RamWriteFrame.refl _ _) hout
    (Or.inl (by change (returnBoundary initial).rip ≠ boundary.rip
                rw [hret']; exact ReturnOutside.ne hout hretCode)) hinput
  have hwithin : RegionsWithin [(Core.Support.activation initial 0x2c0).region,
      Core.outputRegion (Core.Support.activation initial 0x2c0)] [fr.region, outputRegion fr] := by
    intro r hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    all_goals refine ⟨fr.region, by simp, ?_, ?_⟩
    all_goals simp only [Activation.region, Core.outputRegion, Core.Support.activation, hsp, hdi]
    all_goals bv_omega
  have loads (addr : BitVec 64) (ha : fr.rsp.toNat - 8 ≤ addr.toNat)
      (hb : addr.toNat + 8 ≤ fr.rsp.toNat + 8) :
      memLoad final.external addr 64 = memLoad initial.external addr 64 := by
    apply hp.frame.memLoad_eq
    constructor
    · have hh := hreturnRead.low; omega
    · intro r hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl
      all_goals right
      all_goals simp only [Activation.region, Core.outputRegion, Core.Support.activation, hsp, hdi]
      all_goals bv_omega
  change WordsAt final.external (initial.regValue .rdi) 64 _ at hw
  change Readable final.external (initial.regValue .rdi) 33 at hr
  change memLoad final.external (initial.regValue .rdi + 32) 8 = _ at hc
  rw [hdi] at hw hc hr
  rw [show fr.rsp - 0x30 + 32 = fr.rsp - 0x10 by bv_omega] at hc
  have hspFinal := hp.rsp
  change (Reg.ofIndex 4).read final = ⟨64, stackPtr initial + 8⟩ at hspFinal
  rw [show stackPtr initial + 8 = fr.rsp - 0x38 by rw [hsp]; bv_omega] at hspFinal
  refine ⟨fuel, final, he, ready, hp.rip.trans hret', hframe.trans hp.frame hwithin, ?_⟩
  simp only [coreReturned, frameAtoms, outputAtoms, Atom.all_append, Atom.All, Atom.Holds,
    Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
  refine ⟨⟨⟨hspFinal, Reg.read_df_iff.2 hp.df,
    (hp.preserved 3 (by decide)).trans hrbx, (hp.preserved 5 (by decide)).trans hrbp,
    (hp.preserved 12 (by decide)).trans hr12, (hp.preserved 13 (by decide)).trans hr13,
    (hp.preserved 14 (by decide)).trans hr14, (hp.preserved 15 (by decide)).trans hr15,
    ?_, ?_, hreturnRead.of_frame hp.frame, hreturnLow,
    hwrite.of_frame hp.frame, hroom, halign,
    (congrArg (fun x : BitVec 32 => (⟨32, x⟩ : Value)) hmxFinal).trans hmx,
    (congrArg (fun x : BitVec 16 => (⟨16, x⟩ : Value)) hfcFinal).trans hfc, trivial⟩,
    houtput.of_frame hp.frame, hsepout, trivial⟩, hw, hc, hr, trivial⟩
  · rw [loads _ (by bv_omega) (by bv_omega)]; exact hsave
  · rw [loads _ (by bv_omega) (by bv_omega)]; exact hreturn

end P256.Proofs.Scalar.Inverse.Wrapper
