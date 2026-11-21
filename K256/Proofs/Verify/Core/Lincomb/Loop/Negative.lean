import K256.Proofs.Verify.Core.Lincomb.Loop.Packed
import K256.Proofs.Common.Point.DoubleWords.Field
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)
open K256.Proofs.Common.Field K256.Proofs.Common.Point.AddWords
  K256.Proofs.Common.Tactic K256.Proofs.Sec1.Serialize.Normalize

private theorem negationCarry (x y k : Word) :
    x - y + k = x + (k - y) := by bv_omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in

theorem negativePack {a : Registers} {m : Ram} {sp table : BitVec 64} {k : Fin 8} {q : Projective}
    (rsp : a[4].get 64 = sp) (src : a[6].get 64 = table) (index : a[7].get 64 = BitVec.ofNat 64 k.val)
    (write : Writable Extracted.programImage m sp 0x1a8)
    (read : Readable m (table + BitVec.ofNat 64 (120*k.val)) 120)
    (apart : Outside (digitWrites sp) (table + BitVec.ofNat 64 (120*k.val)) 120)
    (point : q.Stored m (table + BitVec.ofNat 64 (120*k.val))) :
    ∃ b n, Reaches .l110418 a m .l110300 b n ∧ Packed sp q.neg a b m n := by
  generalize address : table + BitVec.ofNat 64 (120 * k.val) = ptr at read apart point
  have scale : BitVec.ofNat 64 k.val * 120 = BitVec.ofNat 64 (120 * k.val) := by
    rw [Nat.mul_comm, BitVec.ofNat_mul]
    rfl
  have scratchWrite : Writable Extracted.programImage m (sp + 0xe0) 80 :=
    write.of_offsets rfl (BitVec.add_zero _).symm (by decide)
  have destinationWrite : Writable Extracted.programImage m (sp + 0x58) 120 :=
    write.of_offsets rfl (BitVec.add_zero _).symm (by decide)
  have high := write.readable.low
  clear write
  have scratchApart :
      ptr.toNat + 120 ≤ (sp + 0xe0).toNat ∨ (sp + 0xe0).toNat + 80 ≤ ptr.toNat :=
    apart.2 ⟨(sp + 0xe0).toNat, 80⟩ (.tail _ (.head _))
  have destinationApart :
      ptr.toNat + 120 ≤ (sp + 0x58).toNat ∨ (sp + 0x58).toNat + 120 ≤ ptr.toNat :=
    apart.2 ⟨(sp + 0x58).toNat, 120⟩ (.head _)
  obtain ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩ := point.coordinates
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
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, reduceAddOffset, BitVec.add_zero] at bx0 bx1 bx2 bx3 bx4 by0 by1 by2 by3 by4 bz0 bz1 bz2 bz3 bz4
  have reachJump {b : Registers} {n : Ram}
      (step : program.runBlock (dialect Extracted.programImage) ⟨.l110418, a, m⟩ =
        .jump ⟨.l110300, b, n⟩) : Reaches .l110418 a m .l110300 b n := by
    apply Semantics.Reaches.single
    change (program.runBlock _ _).next _ [] = _
    rw [step]
    rfl
  refine ⟨?_, ?_, reachJump ?run, ?post⟩
  case run =>
    cfg_eval [rsp, src, index, scale]
    simp only [address]
    segment_words [bx0, bx1, bx2, bx3, bx4, by0, by1, by2, by3, by4, bz0, bz1, bz2, bz3, bz4]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l110418)
    rfl
  case post =>
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i, hi⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · refine ⟨xl, weak (negate 1 yl), zl, ?_, ?_, ?_,
        rx, weak_repr (negate_repr ry (by decide)) (by decide), rz⟩
      all_goals
        intro i hi
        have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl <;>
          segment_words [wordAddr, Nat.reduceMul, weak, negate, first, carry, top, modulusWords,
            mask48, mask52, Vector.getElem_mk, List.getElem_toArray, Vector.getElem_ofFn,
            bx0, bx1, bx2, bx3, bx4, by0, by1, by2, by3, by4, bz0, bz1, bz2, bz3, bz4]
      all_goals
        simp only [List.getElem_cons_zero, Fin.getElem_fin, Nat.reduceAdd, Nat.reduceMul,
          BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMul,
          negationCarry, BitVec.and_comm, bx1, bx2, bx3, bx4]
        try rfl
    · change RamWriteFrame m _ [⟨(sp + 0x58).toNat, 120⟩, ⟨(sp + 0xe0).toNat, 80⟩]
      slot_state region

end K256.Proofs.Verify.Core.Lincomb.Loop
