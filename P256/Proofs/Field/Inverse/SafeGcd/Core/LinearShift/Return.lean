import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Tail

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem finish_stage [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1115e6)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1170c6 initial).arguments
      initial.external (linearReturned fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.Shift.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (shiftedWords p) ∧
      memLoad final.external (fr.rdi + 32) 8 = resultSign p ∧
      Readable final.external fr.rdi 33 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
  have hi : (Tail.layout fr controls).Rel code () ⟨.first, #v[], p⟩
      (Machine.lifted.locationOf .l1170c6 initial) :=
    ⟨rfl, ⟨p, rfl, rfl, by simpa only [Tail.layout, Tail.atoms, Tail.start, Lifted.locationOf, List.append_nil] using hcore⟩, hframe⟩
  obtain ⟨l1, h1, hr1⟩ := Tail.first_block code fr controls () #v[] p _ hi
  obtain ⟨l2, h2, hr2⟩ := Tail.second_block code fr controls () #v[] p _ hr1
  obtain ⟨l3, h3, hr3⟩ := Tail.third_block code fr controls () #v[] p _ hr2
  have hb := Tail.finish_block code hcode fr controls () #v[] p _ hr3
  change Ahead Machine.lifted code _ _ at hb
  have decode (lo : Output Value Ram Reg.count) (final : RamState)
      (hq : (Tail.layout fr controls).RetRel code () ⟨#v[], none, p⟩ lo)
      (hrel : Lift.RetRel code Machine.lifted lo final) :
      Machine.Shift.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (shiftedWords p) ∧
      memLoad final.external (fr.rdi + 32) 8 = resultSign p ∧
      Readable final.external fr.rdi 33 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
    obtain ⟨htag, ⟨r, ho, hatoms⟩, hf⟩ := hq
    have har : p = r := congrArg (fun o => o.store) ho
    subst r
    change Atom.All code lo.values lo.store (Machine.Shift.doneAt fr ++ _) at hatoms
    rw [Atom.all_append] at hatoms
    obtain ⟨hsp, hdf, hpres⟩ := FrameCompat.doneAtoms_retRel (m := Machine.Shift.frameInfo)
      hrel hatoms.1 (by decide)
    have hrip' : final.RIP = fr.ret :=
      (Value.eq_bits (Option.some.inj (htag.symm.trans hrel.rip))).symm
    have hf' : RamWriteFrame fr.original final.external [fr.region, outputRegion fr] := by
      rwa [hrel.store] at hf
    refine ⟨⟨hrip', hsp, hpres, hdf, hf'⟩, ?_⟩
    obtain ⟨hw, hs, hr, hmx, hfc, _⟩ := hatoms.2
    rw [hrel.store] at hw hs hr
    change WordsAt final.external fr.rdi 64 (Tail.outputWords p) at hw
    have mx := hmx.symm.trans (hrel.regs 39 (by decide) (by decide))
    have fc := hfc.symm.trans (hrel.regs 51 (by decide) (by decide))
    exact ⟨by simpa only [Tail.shiftedWords_eq, Tail.outputWords] using hw, hs, hr,
      (Value.eq_bits mx).symm, (Value.eq_bits fc).symm⟩
  have sim := Machine.simulation code hcode hout
  have hprefix := ((h1.reaches []).trans (h2.reaches [])).trans (h3.reaches [])
  obtain ⟨mid, hmid, hmrel⟩ := sim.reaches hprefix
    (Rel.locationOf (P := Machine.lifted) (l := .l1170c6) hready hrip)
  obtain ⟨n, hn⟩ := machine_reaches_iff.mp hmid
  obtain ⟨fuel, final, lo, hex, hrel, hq⟩ := P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.ahead_return_advances sim hmrel hb
    (fun lo final hq hrel => by
      have hp := (decode lo final hq hrel).1
      intro hboundary
      rcases hoff with hip | hsp
      · exact hip (hp.rip.symm.trans hboundary.1)
      · exact hsp ((Value.eq_bits hp.rsp).symm.trans hboundary.2))
  exact ⟨n + fuel, final, hn.trans hex, ⟨hrel.ready, hrel.sse, hrel.code⟩, decode lo final hq hrel⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
