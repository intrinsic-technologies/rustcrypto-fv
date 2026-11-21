import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Blocks

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem linear_advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111220)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l116d00 initial).arguments
      initial.external (Machine.LinearCombination.frameAt .l116d00 fr ++ commonAtoms fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.LinearCombination.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords p) ∧
      memLoad final.external (fr.rdi + 40) 8 = resultSign p ∧
      Readable final.external fr.rdi 41 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
  have hi : (layout fr controls).Rel code () ⟨.entry, #v[], p⟩
      (Machine.lifted.locationOf .l116d00 initial) :=
    ⟨rfl, ⟨p, rfl, rfl, by simpa only [layout, coreAtoms, start, Lifted.locationOf, List.append_nil] using hcore⟩, hframe⟩
  obtain ⟨l1, h1, hr1⟩ := entry_block code hcode fr controls () #v[] p _ hi
  obtain ⟨l2, h2, hr2⟩ := stage0_block code hcode fr controls () #v[] p _ hr1
  obtain ⟨l3, h3, hr3⟩ := stage1_block code hcode fr controls () #v[] p _ hr2
  obtain ⟨l4, h4, hr4⟩ := stage2_block code hcode fr controls () #v[] p _ hr3
  obtain ⟨l5, h5, hr5⟩ := stage3_block code hcode fr controls () #v[] p _ hr4
  obtain ⟨l6, h6, hr6⟩ := stage4_block code hcode fr controls () #v[] p _ hr5
  obtain ⟨l7, h7, hr7⟩ := stage5_block code hcode fr controls () #v[] p _ hr6
  obtain ⟨l8, h8, hr8⟩ := stage6_block code hcode fr controls () #v[] p _ hr7
  obtain ⟨l9, h9, hr9⟩ := stage7_block code hcode fr controls () #v[] p _ hr8
  obtain ⟨l10, h10, hr10⟩ := stage8_block code hcode fr controls () #v[] p _ hr9
  obtain ⟨l11, h11, hr11⟩ := stage9_block code hcode fr controls () #v[] p _ hr10
  obtain ⟨l12, h12, hr12⟩ := stage10_block code hcode fr controls () #v[] p _ hr11
  obtain ⟨l13, h13, hr13⟩ := stage11_block code hcode fr controls () #v[] p _ hr12
  obtain ⟨l14, h14, hr14⟩ := stage12_block code hcode fr controls () #v[] p _ hr13
  obtain ⟨l15, h15, hr15⟩ := stage13_block code hcode fr controls () #v[] p _ hr14
  obtain ⟨l16, h16, hr16⟩ := stage14_block code hcode fr controls () #v[] p _ hr15
  obtain ⟨l17, h17, hr17⟩ := stage15_block code hcode fr controls () #v[] p _ hr16
  obtain ⟨l18, h18, hr18⟩ := stage16_block code hcode fr controls () #v[] p _ hr17
  have hb := stage17_block code hcode fr controls () #v[] p _ hr18
  change Ahead Machine.lifted code _ _ at hb
  have decode (lo : Output Value Ram Reg.count) (final : RamState)
      (hq : (layout fr controls).RetRel code () ⟨#v[], none, p⟩ lo)
      (hrel : Lift.RetRel code Machine.lifted lo final) :
      Machine.LinearCombination.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords p) ∧
      memLoad final.external (fr.rdi + 40) 8 = resultSign p ∧
      Readable final.external fr.rdi 41 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
    obtain ⟨htag, ⟨r, ho, hatoms⟩, hf⟩ := hq
    have har : p = r := congrArg (fun o => o.store) ho
    subst r
    change Atom.All code lo.values lo.store (Machine.LinearCombination.doneAt fr ++ _) at hatoms
    rw [Atom.all_append] at hatoms
    obtain ⟨hsp, hdf, hpres⟩ := FrameCompat.doneAtoms_retRel (m := Machine.LinearCombination.frameInfo)
      hrel hatoms.1 (by decide)
    have hrip' : final.RIP = fr.ret :=
      (Value.eq_bits (Option.some.inj (htag.symm.trans hrel.rip))).symm
    have hf' : RamWriteFrame fr.original final.external [fr.region, outputRegion fr] := by
      rwa [hrel.store] at hf
    refine ⟨⟨hrip', hsp, hpres, hdf, hf'⟩, ?_⟩
    obtain ⟨hw, hs, hr, hmx, hfc, _⟩ := hatoms.2
    rw [hrel.store] at hw hs hr
    have mx := hmx.symm.trans (hrel.regs 39 (by decide) (by decide))
    have fc := hfc.symm.trans (hrel.regs 51 (by decide) (by decide))
    exact ⟨hw, hs, hr, (Value.eq_bits mx).symm, (Value.eq_bits fc).symm⟩
  have sim := Machine.simulation code hcode hout
  have hprefix := ((((((((((((((((((h1.reaches []).trans (h2.reaches [])).trans (h3.reaches [])).trans (h4.reaches [])).trans (h5.reaches [])).trans (h6.reaches [])).trans (h7.reaches [])).trans (h8.reaches [])).trans (h9.reaches [])).trans (h10.reaches [])).trans (h11.reaches [])).trans (h12.reaches [])).trans (h13.reaches [])).trans (h14.reaches [])).trans (h15.reaches [])).trans (h16.reaches [])).trans (h17.reaches [])).trans (h18.reaches []))
  obtain ⟨mid, hmid, hmrel⟩ := sim.reaches hprefix
    (Rel.locationOf (P := Machine.lifted) (l := .l116d00) hready hrip)
  obtain ⟨n, hn⟩ := machine_reaches_iff.mp hmid
  obtain ⟨fuel, final, lo, hex, hrel, hq⟩ := P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.ahead_return_advances sim hmrel hb
    (fun lo final hq hrel => by
      have hp := (decode lo final hq hrel).1
      intro hboundary
      rcases hoff with hip | hsp
      · exact hip (hp.rip.symm.trans hboundary.1)
      · exact hsp ((Value.eq_bits hp.rsp).symm.trans hboundary.2))
  exact ⟨n + fuel, final, hn.trans hex, ⟨hrel.ready, hrel.sse, hrel.code⟩, decode lo final hq hrel⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
