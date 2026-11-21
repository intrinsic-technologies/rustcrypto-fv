import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.LIR.Fn11c510
import K256.Proofs.Common.Point.DoubleWords.Field

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
open K256.Proofs.Common.Point.AddWords K256.Proofs.Sec1.Serialize.Normalize

structure SignedArguments (fr : Activation) (a b : Registers) (digit : Int) : Prop where
  rsp : b[4].get 64 = fr.rsp - 408 - 8
  lhs : b[6].get 64 = fr.rsp - 408
  rhs : b[2].get 64 = fr.rsp - 288
  target : b[7].get 64 = fr.rsp - 168
  targetWidth : b[7].width = 64
  flag : (b[1].get 64).setWidth 8 = (if digit < 0 then 1 else 0)
  temporary : b[15].get 64 = fr.rsp - 168
  kept : ∀ i : Fin Reg.count, i.val ∈ [3,14,22,39,50,51] → b[i] = a[i]

private theorem firstNegationWord (k c a x : Word) :
    k + (c * a - x) = a * c + (k - x) := by
  rw [BitVec.mul_comm c a]
  bv_omega

private theorem nextNegationWord (x y k : Word) :
    x - y + k = x + (k - y) := by bv_omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem prepareSigned {fr : Activation} {a : Registers} {entry m : Ram} {digit : Int} {t : Projective}
    (state : Scanning fr entry digit 8 a m t) :
    ∃ b next, program.runBlock (dialect Extracted.programImage) ⟨.l11c6ed, a, m⟩ =
      .call ⟨.l10fcc0, b, memStore next (fr.rsp - 408 - 8) (0x11c845 : Word)⟩
        (Generator.callFrame .l11c845 0x11c845) ∧
      SignedArguments fr a b digit ∧
      t.neg.Stored next (fr.rsp - 288) ∧
      RamWriteFrame m next [⟨(fr.rsp - 288).toNat,120⟩] := by
  have atoms := state.atoms
  simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, lower, _, _⟩ := atoms
  have low := stack.readable.low
  have hacc := state.accumulator
  change a[14].get 64 = fr.rsp - 408 at hacc
  have rsp : a[4].get 64 = fr.rsp - 408 := congrArg (Value.get 64) sp
  have hsign : (a[0].get 64).setWidth 8 = (if digit < 0 then 1 else 0) := by
    simpa only [choice, Nat.lt_irrefl, ite_false, decide_eq_true_eq] using state.flag
  have addr (k : Word) (hk : k.toNat ≤ 496) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have n496 : (fr.rsp - 496).toNat = fr.rsp.toNat - 496 := addr 496 (by decide)
  have n408 : (fr.rsp - 408).toNat = fr.rsp.toNat - 408 := addr 408 (by decide)
  have n288 : (fr.rsp - 288).toNat = fr.rsp.toNat - 288 := addr 288 (by decide)
  obtain ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩ := state.stored.coordinates
  have bx0 := wx 0 (by decide)
  have bx1 := wx 1 (by decide)
  have bx2 := wx 2 (by decide)
  have bx3 := wx 3 (by decide)
  have bx4 := wx 4 (by decide)
  have by0 := wy 0 (by decide)
  have by1 := wy 1 (by decide)
  have by2 := wy 2 (by decide)
  have by3 := wy 3 (by decide)
  have by4 := wy 4 (by decide)
  have bz0 := wz 0 (by decide)
  have bz1 := wz 1 (by decide)
  have bz2 := wz 2 (by decide)
  have bz3 := wz 3 (by decide)
  have bz4 := wz 4 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, reduceAddOffset] at bx0 bx1 bx2 bx3 bx4 by0 by1 by2 by3 by4 bz0 bz1 bz2 bz3 bz4
  refine ⟨?b, ?next, ?run, ?args, ?right, ?frame⟩
  case run =>
    arithmetic_segment using code_l11c6ed [rsp, hacc, hsign, bx0, bx1, bx2, bx3, bx4,
      by0, by1, by2, by3, by4, bz0, bz1, bz2, bz3, bz4]
  case args =>
    refine ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
    · exact (show fr.rsp - 416 = fr.rsp - 408 - 8 by bv_omega)
    · change ((if digit < 0 then (1 : BitVec 8) else 0).setWidth 64).setWidth 8 = _
      exact BitVec.setWidth_setWidth_of_le _ (by decide)
    · rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame =>
    repeat' apply RamWriteFrame.memStore
    · exact RamWriteFrame.refl _ _
    all_goals
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change (fr.rsp - 288).toNat ≤ _ ∧ _ ≤ (fr.rsp - 288).toNat + 120 ∧ _
      bv_omega
  case right =>
    refine ⟨xl, weak (negate 1 yl), zl, ?_, ?_, ?_, rx, weak_repr (negate_repr ry (by decide)) (by decide), rz⟩
    all_goals
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl <;>
        refine_norm [wordAddr, Nat.reduceMul, weak, negate, first, carry, top, modulusWords, mask48, mask52,
          Vector.getElem_mk, List.getElem_toArray, Vector.getElem_ofFn,
          bx0, bx1, bx2, bx3, bx4, by0, by1, by2, by3, by4, bz0, bz1, bz2, bz3, bz4]
    all_goals
      simp only [List.getElem_cons_zero, Fin.getElem_fin, Nat.reduceAdd, Nat.reduceMul,
        BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMul,
        firstNegationWord, nextNegationWord, BitVec.and_comm]
      try rfl

end K256.Proofs.Generate.Generator.Multiply.Lookup
