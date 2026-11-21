import P256.Proofs.Scalar.Inverse.Wrapper.Tail
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Scalar.Inverse.Wrapper
open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem finish_stage [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {a : Inputs}
    {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112e86)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l118966 initial).arguments
      initial.external (choiceReturned fr a)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.Inverse.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords a) ∧ memLoad final.external (fr.rdi + 32) 8 = resultChoice a ∧ Readable final.external fr.rdi 33 ∧
      final.regValue .rax = fr.rdi ∧ final.MXCSR = a.mxcsr ∧ final.FP87_Control = a.fcw := by
  have hi : (Tail.layout fr).Rel code () ⟨.finish, #v[], a⟩
      (Machine.lifted.locationOf .l118966 initial) := ⟨rfl, ⟨a, rfl, rfl, hcore⟩, hframe⟩
  have hb := Tail.finish_block code hcode fr () #v[] a _ hi
  change Ahead Machine.lifted code _ _ at hb
  have decode (lo : Output Value Ram Reg.count) (final : RamState)
      (hq : (Tail.layout fr).RetRel code () ⟨#v[], none, a⟩ lo)
      (hrel : Lift.RetRel code Machine.lifted lo final) :
      Machine.Inverse.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords a) ∧ memLoad final.external (fr.rdi + 32) 8 = resultChoice a ∧ Readable final.external fr.rdi 33 ∧
      final.regValue .rax = fr.rdi ∧ final.MXCSR = a.mxcsr ∧ final.FP87_Control = a.fcw := by
    obtain ⟨htag, ⟨r, ho, hatoms⟩, hf⟩ := hq
    have har : a = r := congrArg (fun o => o.store) ho
    subst r
    change Atom.All code lo.values lo.store (Machine.Inverse.doneAt fr ++ _) at hatoms
    rw [Atom.all_append] at hatoms
    obtain ⟨hsp, hdf, hpres⟩ := P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.doneAtoms_retRel (m := Machine.Inverse.frameInfo)
      hrel hatoms.1 (by decide)
    have hrip' : final.RIP = fr.ret :=
      (Value.eq_bits (Option.some.inj (htag.symm.trans hrel.rip))).symm
    have hf' : RamWriteFrame fr.original final.external [fr.region, outputRegion fr] := by
      rwa [hrel.store] at hf
    refine ⟨⟨hrip', hsp, hpres, hdf, hf'⟩, ?_⟩
    obtain ⟨hw, hc, hr, hx, hmx, hfc, _⟩ := hatoms.2
    rw [hrel.store] at hw hc hr
    exact ⟨hw, hc, hr, Value.eq_bits ((hrel.regs 0 (by decide) (by decide)).symm.trans hx),
      (Value.eq_bits (hmx.symm.trans (hrel.regs 39 (by decide) (by decide)))).symm,
      (Value.eq_bits (hfc.symm.trans (hrel.regs 51 (by decide) (by decide)))).symm⟩
  obtain ⟨fuel, final, lo, he, hrel, hq⟩ := Correction.Execution.ahead_return_advances
    (Machine.simulation code hcode hout)
    (Rel.locationOf (P := Machine.lifted) (l := .l118966) hready hrip) hb
    (fun lo final hq hrel => by
      have hp := (decode lo final hq hrel).1
      intro hboundary
      rcases hoff with hip | hsp
      · exact hip (hp.rip.symm.trans hboundary.1)
      · exact hsp ((Value.eq_bits hp.rsp).symm.trans hboundary.2))
  exact ⟨fuel, final, he, ⟨hrel.ready, hrel.sse, hrel.code⟩, decode lo final hq hrel⟩

end P256.Proofs.Scalar.Inverse.Wrapper
