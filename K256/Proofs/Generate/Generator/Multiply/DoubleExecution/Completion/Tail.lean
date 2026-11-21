import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Frame

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  K256.Proofs.Common.Tactic
open K256.Proofs.Sec1.Affine.Uncompressed

def tailMap : Vector (Fin 3597) Reg.count :=
  RegMap.args [(0, 3576), (1, 3593), (2, 3573), (3, 3344), (4, 4), (5, 3420),
    (6, 3556), (7, 3578), (8, 3587), (9, 3526), (10, 3504), (11, 3483),
    (12, 3449), (13, 3474), (14, 3476), (15, 3472), (19, 3594), (22, 22),
    (39, 39), (50, 50), (51, 51)] 3597

def tailRegisters : List Nat := [2, 3, 4, 5, 6, 7, 9, 12, 13, 14, 15, 22, 39, 50, 51]

theorem tailIndexBound (i : Fin Reg.count) (keep : i.val ∈ tailRegisters) :
    (tailMap[i]).val < 3583 :=
  (show ∀ j : Fin Reg.count, j.val ∈ tailRegisters → (tailMap[j]).val < 3583 by decide +kernel)
    i keep

private theorem branch_eval (scope : Values Value 3597) (m : Ram) (n : Nat)
    (test : scope[3596].truth = (n != 0)) :
    (Block.terminate (.condBr (Fin.last 3596) ⟨Label.l11d810, tailMap⟩
      ⟨Label.l11f5e5, tailMap⟩) : Block Op Label signature Reg.count 3597).eval
      (dialect Extracted.programImage) scope m =
      .jump ⟨if n = 0 then .l11f5e5 else .l11d810, scope.select tailMap, m⟩ := by
  simp only [Block.eval, Terminator.eval, dialect_truth, Edge.eval]
  change (if scope[3596].truth then _ else _) = _
  rw [test]
  by_cases hn : n = 0
  · subst n
    rfl
  · have ht : (n != 0) = true := bne_iff_ne.mpr hn
    simp only [ht, ite_true]
    apply congrArg (fun l : Label => Transfer.jump
      (⟨l, scope.select tailMap, m⟩ : Location Value Ram Label signature))
    exact (ite_eq_right hn).symm

set_option maxRecDepth 1400 in
set_option maxHeartbeats 1800000 in
theorem doubleTail {a : Values Value 3583} {m : Ram} {sp : BitVec 64} {n : Nat}
    (rsp : a[4].get 64 = sp)
    (stack : Writable Extracted.programImage m sp 0x1c0)
    (count : memLoad m (sp + 0x1bc) 32 = BitVec.ofNat 32 (n + 1))
    (bound : n < 4) :
    ∃ (b : Registers) (t : Ram), b_l11d880_83.eval (dialect Extracted.programImage) a m =
      .jump ⟨if n = 0 then .l11f5e5 else .l11d810, b, t⟩ ∧
      b[1] = ⟨64, BitVec.ofNat 64 n⟩ ∧
      b[8] = ⟨64, a[3568].get 64 &&& a[3474].get 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ tailRegisters →
        b[i] = (a[(tailMap[i]).val]?).getD ⟨1, 0⟩) ∧
      t = memStore (memStore m (sp + 0x168) (a[3568].get 64 &&& a[3474].get 64)) (sp + 0x170)
        ((a[3581].get 64 >>> 52) + a[3576].get 64) ∧
      RamWriteFrame m t (writes sp) := by
  have low := stack.readable.low
  have hn : n < 2^32 := by omega
  have hsub : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 by rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.add_sub_cancel]
  have test : (!(BitVec.ofNat 32 n == 0)) = (n != 0) := by
    have hs : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hs with rfl | rfl | rfl | rfl <;> rfl
  have hwidth : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) hn
  refine ⟨?_, ?_, ?run, ?count, ?r8, ?rPres, ?stores, ?frame⟩
  case run =>
    arithmetic_prefix [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l11d880_83)
    refine branch_eval _ _ n ?_
    simp only [↓arithmeticRead, Value.truth_ofBool]
    segment_words [count, hsub, test]
  case count =>
    simp only [Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead]
    segment_words [count, hsub, hwidth]
  case r8 =>
    simp only [Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead]
  case rPres =>
    intro i hi
    rw [getElem?_pos a (tailMap[i]).val (tailIndexBound i hi), Option.getD_some]
    rcases i with ⟨i, boundI⟩
    simp only [tailRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead] <;> rfl
  case stores => rfl
  case frame =>
    unfold writes
    slot_state region

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
