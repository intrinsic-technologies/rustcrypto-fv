import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Addition
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Return
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Choice
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Entry
import K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule.Value

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1 Rounding

theorem round (addCall : AddExecution) : RoundExecution := by
  intro fr a m x y atoms image _ hx hy rx ry dest above apart wx wy
  let w := ProductSchedule.machineProduct (scalarWords x) (scalarWords y)
  obtain ⟨b, n, push, entry, before, s, words, lo, hi, flag⟩ := enterAdd atoms rx ry (fun p hp => (apart p hp).1) wx wy
  have pack : WordsAt n (fr.rsp - 112) 64 (scalarWords (upper w)) := by
    rw [← upper_words w]
    simpa only [lo, hi] using words
  have stack : Writable Extracted.programImage m (fr.rsp - 224) 224 := by
    simp only [Fn11b8f0.frameAt, Fn11b8f0.frameAtG1, Atom.All, Atom.Holds] at atoms
    rcases atoms with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, _⟩
    exact stack
  have bound := upper_bound w
  have nBound : 2^128 < domain.n ∧ domain.n ≤ 2^256 := by decide +kernel
  obtain ⟨c, p, addPath, returnAtoms, widths, bx, r12, r15, incremented, addWrites⟩ :=
    addOne addCall push entry image stack before s (u := upper w) (by omega) pack
  rw [lo] at bx
  rw [hi] at r12
  rw [flag] at r15
  obtain ⟨e, q, choosePath, lastAtoms, ws, bit, keep3, keep12, barrier⟩ :=
    choice returnAtoms widths r15 (shift_bit w)
  have room := s.low
  have high := s.readable.low
  have at168 : (fr.rsp - 168).toNat = fr.rsp.toNat - 168 :=
    BitVec.toNat_sub_of_le (by change 168 ≤ fr.rsp.toNat; omega)
  have at80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 :=
    BitVec.toNat_sub_of_le (by change 80 ≤ fr.rsp.toNat; omega)
  have incremented' := incremented.of_frame barrier (by decide) (by
    simp only [Outside, List.mem_singleton, forall_eq, at80, at168]
    exact ⟨by omega, Or.inr (by omega)⟩)
  have destAfter := (dest.of_frame addWrites).of_frame barrier
  obtain ⟨out, run, tag, done_, width, result, frame⟩ := finish lastAtoms ws destAfter above bit
    (keep3.trans bx) (keep12.trans r12) incremented'
  have val : roundedHigh w = Generate.Curve.mulShift384 x y := by
    rw [show w = _ from ProductSchedule.machineProduct_eq _ _, rounded_product (by omega) (by omega)]
  rw [val] at result
  refine ⟨out, Program.Exec.of_sem ((addPath.trans choosePath).exec run.sem), tag, done_, width, result, ?_⟩
  have scratch := addWrites.trans barrier (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> dsimp only <;> omega)
  apply ((RamWriteFrame.refl m _).trans scratch ?_).trans frame
  · intro r hr
    exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply.Split
