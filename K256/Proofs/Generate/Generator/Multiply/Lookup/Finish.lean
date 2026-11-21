import K256.Proofs.Generate.Generator.Multiply.Lookup.Finish.Negate
import K256.Proofs.Generate.Generator.Multiply.Lookup.Finish.Return
import K256.Proofs.Generate.Generator.Multiply.Lookup.SelectCall

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.ECC

theorem finish {fr : Activation} {a : Registers} {entry m : Ram} {digit : Int} {t : Projective}
    (state : Scanning fr entry digit 8 a m t)
    (dst : Writable Extracted.programImage entry fr.rdi 120) (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨stage 8, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn11c510.doneAt fr) ∧ ParseSignature.ArgumentWidths out.values ∧
      (if digit < 0 then t.neg else t).Stored out.store fr.rdi ∧
      RamWriteFrame entry out.store [window fr, ⟨fr.rdi.toNat,120⟩] := by
  obtain ⟨b, n, call, args, right, prepared⟩ := prepareSigned state
  have atoms := state.atoms
  simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, _, bx, _, _, _, _, _, _, _, _, _, _, _, _, win, lower, _, _⟩ := atoms
  have shift (k : Word) (hk : k.toNat ≤ 496) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have n496 : (fr.rsp - 496).toNat = fr.rsp.toNat - 496 := shift 496 (by decide)
  have n408 : (fr.rsp - 408).toNat = fr.rsp.toNat - 408 := shift 408 (by decide)
  have n288 : (fr.rsp - 288).toNat = fr.rsp.toNat - 288 := shift 288 (by decide)
  have n168 : (fr.rsp - 168).toNat = fr.rsp.toNat - 168 := shift 168 (by decide)
  have left : t.Stored n (fr.rsp - 408) := by
    apply state.stored.of_frame prepared
    refine ⟨by rw [n408]; have := fr.rsp.isLt; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    left
    change (fr.rsp - 408).toNat + 120 ≤ (fr.rsp - 288).toNat
    omega
  have childBase : fr.rsp - 408 - 88 = fr.rsp - 496 := by bv_omega
  have win' := win.of_frame prepared
  have stack : Writable Extracted.programImage n (fr.rsp - 408 - 88) 88 := by
    rw [childBase]
    slot_state region
  have lread : Readable n (fr.rsp - 408) 120 := by slot_state region
  have rread : Readable n (fr.rsp - 288) 120 := by slot_state region
  have target : Writable Extracted.programImage n (fr.rsp - 168) 120 := by slot_state region
  have sign : (b[1].get 64).setWidth 8 = if decide (digit < 0) then 1 else 0 := by
    simpa only [decide_eq_true_eq] using args.flag
  obtain ⟨c, o, path, spBack, saved, kept, widths, chosen, selected⟩ :=
    resumeSelect (decide (digit < 0)) call args.rsp args.lhs args.rhs args.target
      args.targetWidth sign stack (by omega) (by decide) lread rread target
      (Nat.le_refl _) (by omega) (by omega) left right
  rw [childBase] at selected
  let scratch : List MemoryRegion := [⟨(fr.rsp - 496).toNat,448⟩]
  have localFrame : RamWriteFrame m o scratch := by
    apply ((RamWriteFrame.refl _ _).trans prepared ?_).trans selected
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
        change (fr.rsp - 496).toNat + 88 ≤ (fr.rsp - 496).toNat + 448
        omega
      · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
        · change (fr.rsp - 496).toNat ≤ (fr.rsp - 168).toNat
          omega
        · change (fr.rsp - 168).toNat + 120 ≤ (fr.rsp - 496).toNat + 448
          omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
      · change (fr.rsp - 496).toNat ≤ (fr.rsp - 288).toNat
        omega
      · change (fr.rsp - 288).toNat + 120 ≤ (fr.rsp - 496).toNat + 448
        omega
  have below (r : MemoryRegion) (hr : r ∈ scratch) : r.start + r.size ≤ fr.rsp.toNat - 48 := by
    obtain rfl := List.mem_singleton.mp hr
    change (fr.rsp - 496).toNat + 448 ≤ _
    omega
  have regs (i : Fin Reg.count) (hi : i.val ∈ [3,4,22,39,50,51]) : c[i] = a[i] := by
    rcases i with ⟨i, h⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · have bb := (args.kept 3 (by decide)).trans bx
      exact (saved 3 (by decide)).trans (by rw [bb, Value.get_mk]; exact bx.symm)
    · exact spBack.trans sp.symm
    · exact (kept 22 (by decide)).trans (args.kept 22 (by decide))
    · exact (kept 39 (by decide)).trans (args.kept 39 (by decide))
    · exact (kept 50 (by decide)).trans (args.kept 50 (by decide))
    · exact (kept 51 (by decide)).trans (args.kept 51 (by decide))
  have resume : Atom.All Extracted.programImage c o (Fn11c510.frameAt .l11c845 fr) :=
    frameAtomsAfter state.atoms localFrame below regs
  have r14 : c[14].get 64 = fr.rsp - 408 := by
    have value := congrArg (Value.get 64) (saved 14 (by decide))
    rw [Value.get_mk] at value
    exact value.trans ((congrArg (Value.get 64) (args.kept 14 (by decide))).trans state.accumulator)
  have r15 : c[15].get 64 = fr.rsp - 168 := by
    have value := congrArg (Value.get 64) (saved 15 (by decide))
    rw [Value.get_mk] at value
    exact value.trans args.temporary
  have dest := (dst.of_frame state.writes).of_frame localFrame
  have point : (if digit < 0 then t.neg else t).Stored o (fr.rsp - 168) := by
    simpa only [decide_eq_true_eq] using chosen
  obtain ⟨out, run, tag, done_, aw, output, finalFrame⟩ := finishReturn resume r14 r15 widths point dest above
  refine ⟨out, Program.Exec.of_sem (path.exec run.sem), tag, done_, aw, output, ?_⟩
  have lifts (r : MemoryRegion) (hr : r ∈ scratch) : ∃ w ∈ [window fr, ⟨fr.rdi.toNat,120⟩],
      w.start ≤ r.start ∧ r.start + r.size ≤ w.start + w.size := by
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, Nat.le_refl _, ?_⟩
    change (fr.rsp - 496).toNat + 448 ≤ (fr.rsp - 496).toNat + 496
    omega
  have initialFrame : RamWriteFrame entry m [window fr, ⟨fr.rdi.toNat,120⟩] :=
    (RamWriteFrame.refl _ _).trans state.writes (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  apply (initialFrame.trans localFrame lifts).trans finalFrame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · change (fr.rsp - 496).toNat ≤ (fr.rsp - 408).toNat
      omega
    · change (fr.rsp - 408).toNat + 120 ≤ (fr.rsp - 496).toNat + 496
      omega
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply.Lookup
