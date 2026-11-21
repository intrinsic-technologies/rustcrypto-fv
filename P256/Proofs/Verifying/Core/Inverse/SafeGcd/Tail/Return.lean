import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail.Finish
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared (zeroWords correctionInput)

open P256.Proofs.Field.Inverse.SafeGcd

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem finish_stage [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {a : LoopState}
    {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112689)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1146d9 initial).arguments
      initial.external (returnedAtoms fr controls p a)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.Core.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (Correction.correctedWords (correctionInput p a)) ∧ memLoad final.external (fr.rdi + 32) 8 = choiceByte p a ∧
      Readable final.external fr.rdi 33 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
  have hi : (Finish.layout fr controls p).Rel code () ⟨.finish, #v[], a⟩
      (Machine.lifted.locationOf .l1146d9 initial) := ⟨rfl, ⟨a, rfl, rfl, hcore⟩, hframe⟩
  have hb := Finish.finish_block code hcode fr controls p () #v[] a _ hi
  change Ahead Machine.lifted code _ _ at hb
  have decode (lo : Output Value Ram Reg.count) (final : RamState)
      (hq : (Finish.layout fr controls p).RetRel code () ⟨#v[], none, a⟩ lo)
      (hrel : Lift.RetRel code Machine.lifted lo final) :
      Machine.Core.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (Correction.correctedWords (correctionInput p a)) ∧ memLoad final.external (fr.rdi + 32) 8 = choiceByte p a ∧
      Readable final.external fr.rdi 33 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
    obtain ⟨htag, ⟨r, ho, hatoms⟩, hf⟩ := hq
    have har : a = r := congrArg (fun o => o.store) ho
    subst r
    change Atom.All code lo.values lo.store (Machine.Core.doneAt fr ++ _) at hatoms
    rw [Atom.all_append] at hatoms
    obtain ⟨hsp, hdf, hpres⟩ := P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.doneAtoms_retRel (m := Machine.Core.frameInfo)
      hrel hatoms.1 (by decide)
    have hrip' : final.RIP = fr.ret :=
      (Value.eq_bits (Option.some.inj (htag.symm.trans hrel.rip))).symm
    have hf' : RamWriteFrame fr.original final.external [fr.region, outputRegion fr] := by
      rwa [hrel.store] at hf
    refine ⟨⟨hrip', hsp, hpres, hdf, hf'⟩, ?_⟩
    obtain ⟨hw, hc, hr, hmx, hfc, _⟩ := hatoms.2
    rw [hrel.store] at hw hc hr
    exact ⟨hw, hc, hr,
      (Value.eq_bits (hmx.symm.trans (hrel.regs 39 (by decide) (by decide)))).symm,
      (Value.eq_bits (hfc.symm.trans (hrel.regs 51 (by decide) (by decide)))).symm⟩
  obtain ⟨fuel, final, lo, he, hrel, hq⟩ := Correction.Execution.ahead_return_advances
    (Machine.simulation code hcode hout)
    (Rel.locationOf (P := Machine.lifted) (l := .l1146d9) hready hrip) hb
    (fun lo final hq hrel => by
      have hp := (decode lo final hq hrel).1
      intro hboundary
      rcases hoff with hip | hsp
      · exact hip (hp.rip.symm.trans hboundary.1)
      · exact hsp ((Value.eq_bits hp.rsp).symm.trans hboundary.2))
  exact ⟨fuel, final, he, ⟨hrel.ready, hrel.sse, hrel.code⟩, decode lo final hq hrel⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail
