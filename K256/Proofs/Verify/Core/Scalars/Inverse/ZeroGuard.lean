import K256.Proofs.Verify.Core.State
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core.Scalars.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private abbrev kept (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 6, 12, 13, 15, 22, 39, 50, 51] → b[i] = a[i]

private inductive Limb where
  | low | second | third | high

private def Limb.label : Limb → Label
  | .low => .l1097fe
  | .second => .l109808
  | .third => .l109810
  | .high => .l109818

private def Limb.next : Limb → Label
  | .low => .l109808
  | .second => .l109810
  | .third => .l109818
  | .high => .l109948

private def Limb.offset : Limb → BitVec 64
  | .low => 48
  | .second => 56
  | .third => 64
  | .high => 72

set_option linter.unusedSimpArgs false in
private theorem testLimb (limb : Limb) {a : Registers} {m : Ram} {sp v : BitVec 64}
    (rsp : a[4].get 64 = sp) (rd : Readable m sp 80)
    (load : memLoad m (sp + limb.offset) 64 = v) :
    ∃ b, Reaches limb.label a m (if v = 0 then limb.next else .l109824) b m ∧
      b[2] = (match limb with | .low => ⟨64, v⟩ | _ => a[2]) ∧ kept a b := by
  have zf : (testFlags (v &&& v)).ZF.getD false = (v == 0) := by rw [BitVec.and_self]; rfl
  have read : LoadOk m (sp + limb.offset) 8 := by
    exact LoadOk.of_offsets rd rfl (BitVec.add_zero sp).symm (by cases limb <;> decide)
  cases limb <;> simp only [Limb.offset] at load read <;> dsimp only [Limb.label, Limb.next]
  all_goals
    by_cases zero : v = 0
    all_goals
      first | rw [ite_eq_left zero] | rw [ite_eq_right zero]
      refine ⟨?_, Semantics.Reaches.single (by
        change program.step _ _ = _
        unfold Program.step
        cfg_eval
        simp only [rsp, load, zf, cmpSpec_ZF, read, ite_true]
        first
          | rw [ite_eq_left (by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] using zero)]
          | rw [ite_eq_right (by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq, Decidable.not_not] using zero)]
        rfl), ?_, ?_⟩ <;> try rfl
      rintro ⟨i,hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option linter.unusedSimpArgs false in
theorem zeroGuard {a : Registers} {m : Ram} {sp : BitVec 64} (rsp : a[4].get 64 = sp)
    (rd : Readable m sp 80) :
    let word := fun (off : BitVec 64) => memLoad m (sp + off) 64
    ∃ b, Reaches .l1097fe a m
        (if word 48 = 0 ∧ word 56 = 0 ∧ word 64 = 0 ∧ word 72 = 0 then .l109948 else .l109824) b m ∧
      b[2] = ⟨64, word 48⟩ ∧ kept a b := by
  let word (off : BitVec 64) := memLoad m (sp + off) 64
  change ∃ b, Reaches _ a m (if word 48 = 0 ∧ word 56 = 0 ∧ word 64 = 0 ∧ word 72 = 0
    then .l109948 else .l109824) b m ∧ b[2] = ⟨64, word 48⟩ ∧ kept a b
  have spOf {b : Registers} (h : kept a b) := (congrArg (Value.get 64) (h 4 (by decide))).trans rsp
  have chain {b c : Registers} (h : kept a b) (k : kept b c) : kept a c :=
    fun i hi => (k i hi).trans (h i hi)
  obtain ⟨b, first, low, hb⟩ := testLimb .low (m := m) (v := word 48) rsp rd rfl
  simp only [Limb.label] at first
  by_cases z0 : word 48 = 0
  case neg =>
    rw [ite_eq_right z0] at first
    exact ⟨b, by simpa only [z0, false_and, ite_false] using first, low, hb⟩
  rw [ite_eq_left z0] at first
  obtain ⟨c, second, rdx, hc⟩ := testLimb .second (m := m) (v := word 56) (spOf hb) rd rfl
  have path := first.trans second
  have low := rdx.trans low
  have keptC := chain hb hc
  by_cases z1 : word 56 = 0
  case neg =>
    rw [ite_eq_right z1] at path
    exact ⟨c, by simpa only [z0, z1, true_and, false_and, ite_false] using path,
      low, keptC⟩
  rw [ite_eq_left z1] at path
  obtain ⟨d, third, rdx, hd⟩ := testLimb .third (m := m) (v := word 64) (spOf keptC) rd rfl
  have path := path.trans third
  have low := rdx.trans low
  have keptD := chain keptC hd
  by_cases z2 : word 64 = 0
  case neg =>
    rw [ite_eq_right z2] at path
    exact ⟨d, by simpa only [z0, z1, z2, true_and, false_and, ite_false] using path,
      low, keptD⟩
  rw [ite_eq_left z2] at path
  obtain ⟨e, high, rdx, he⟩ := testLimb .high (m := m) (v := word 72) (spOf keptD) rd rfl
  exact ⟨e, by simpa only [z0, z1, z2, true_and, Limb.next] using path.trans high,
    rdx.trans low, chain keptD he⟩

end K256.Proofs.Verify.Core.Scalars.Inverse
