import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Registers

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)

open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

private theorem signFlag (w : Words) :
    ((w.delta == 0) || (w.delta.msb != false)) = !(SafeGcd.Batch.positive w) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.bne_false, BitVec.msb_eq_toInt, decide_eq_true_eq,
    Bool.not_eq_true', SafeGcd.Batch.positive, decide_eq_false_iff_not]
  have zero : w.delta = 0 ↔ w.delta.toInt = 0 := by rw [← BitVec.toInt_inj]; rfl
  rw [zero]
  omega

private theorem evenFlag (w : Words) : (w.g.setWidth 8 &&& 1 == 0) = SafeGcd.Batch.even w := rfl

private theorem branch {test : Prop} [Decidable test] (c : Registers) (m : Ram) :
    (if test then Transfer.jump ⟨.l1095c1,c,m⟩ else Transfer.jump ⟨.l109925,c,m⟩ :
      Transfer Value Ram Label signature Reg.count) =
      .jump ⟨if test then .l1095c1 else .l109925,c,m⟩ := by by_cases h : test <;> simp [h]

private theorem via (mid : Label) {a b c : Registers} {m : Ram} {start finish : Label}
    (step : program.step (dialect Extracted.programImage) ⟨⟨start,a,m⟩,[]⟩ =
      .next ⟨⟨mid,b,m⟩,[]⟩) (tail : Reaches mid b m finish c m) : Reaches start a m finish c m :=
  (Semantics.Reaches.single step).trans tail

local macro "divstep_block" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    change program.step _ _ = _
    unfold Program.step
    cfg_eval
    try simp only [$ls,*]
    try rw [branch]
    rfl))

local macro "divstep_post" st:ident n:ident "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    all_goals constructor
    all_goals try simp only [SafeGcd.Batch.next, SafeGcd.Batch.numerator, SafeGcd.Batch.swap,
      $ls,*, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, ite_true, ite_false,
      reduceCtorEq]
    all_goals first
      | rfl
      | exact ($st).f
      | change ((BitVec.ofNat 32 $n).setWidth 64).setWidth 32 = _
        rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]))

local macro "divstep_kept" : tactic =>
  `(tactic| (
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> subst i <;> rfl))

set_option linter.unusedSimpArgs false in
private theorem iteration {a : Registers} {m : Ram} {w : Words} {n : Nat}
    (st : Inner a w (n+1)) (small : n < 62) :
    ∃ b, Reaches .l109925 a m (if n = 0 then .l1095c1 else .l109925) b m ∧ Kept a b ∧
      Inner b (SafeGcd.Batch.next w) n ∧ Rows b (SafeGcd.Batch.next w) := by
  have byte := congrArg (BitVec.setWidth 8) st.g
  have counter : (a[2].get 64).setWidth 32 - 1 = BitVec.ofNat 32 n := by
    rw [setWidth_get _ (by decide : 32 ≤ 64), st.counter,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 by rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.add_sub_cancel]
  have z : BitVec.ofNat 32 n = 0 ↔ n = 0 := by
    constructor
    · intro h
      have he := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at he
      exact he
    · rintro rfl; rfl
  cases even : SafeGcd.Batch.even w
  case true =>
    refine ⟨?_, via (b := ?_) .l10992a ?s0
      (via (b := ?_) .l10993d ?s1
      (via (b := ?_) .l10990b ?s2
        (Semantics.Reaches.single ?s3))), ?_, ?_, ?_⟩
    case s0 => divstep_block [byte, testFlags_ZF, evenFlag, even,
      Bool.not_false, Bool.not_true, ite_true, ite_false, reduceCtorEq]
    case s1 => divstep_block []
    case s2 => divstep_block []
    case s3 => divstep_block [counter, beq_iff_eq, z, st.delta, st.f, st.g, st.u, st.v, st.q, st.r]
    · divstep_kept
    divstep_post st n [even]
  case false =>
    cases pos : SafeGcd.Batch.positive w
    case true =>
      refine ⟨?_, via (b := ?_) .l1098e0 ?s0
        (via (b := ?_) .l1098e5 ?s1
        (via (b := ?_) .l10990b ?s2
          (Semantics.Reaches.single ?s3))), ?_, ?_, ?_⟩
      case s0 => divstep_block [byte, testFlags_ZF, evenFlag, even,
        Bool.not_false, Bool.not_true, ite_true, ite_false, reduceCtorEq]
      case s1 => divstep_block [st.delta, BitVec.and_self, testFlags_ZF, testFlags_SF, testFlags_OF, signFlag, pos,
        Bool.not_false, Bool.not_true, ite_true, ite_false, reduceCtorEq]
      case s2 => divstep_block []
      case s3 => divstep_block [counter, beq_iff_eq, z, st.delta, st.f, st.g, st.u, st.v, st.q, st.r]
      · divstep_kept
      divstep_post st n [even, pos]
    case false =>
      refine ⟨?_, via (b := ?_) .l1098e0 ?s0
        (via (b := ?_) .l109930 ?s1
        (via (b := ?_) .l10993d ?s2
        (via (b := ?_) .l10990b ?s3
          (Semantics.Reaches.single ?s4)))), ?_, ?_, ?_⟩
      case s0 => divstep_block [byte, testFlags_ZF, evenFlag, even,
        Bool.not_false, Bool.not_true, ite_true, ite_false, reduceCtorEq]
      case s1 => divstep_block [st.delta, BitVec.and_self, testFlags_ZF, testFlags_SF, testFlags_OF, signFlag, pos,
        Bool.not_false, Bool.not_true, ite_true, ite_false, reduceCtorEq]
      case s2 => divstep_block []
      case s3 => divstep_block []
      case s4 => divstep_block [counter, beq_iff_eq, z, st.delta, st.f, st.g, st.u, st.v, st.q, st.r]
      · divstep_kept
      divstep_post st n [even, pos]

theorem runWords {b : Registers} {p : Ram} {w : Words} {k : Nat}
    (pos : 0 < k) (small : k ≤ 62) (inner : Inner b w k) :
    ∃ c, Reaches .l109925 b p .l1095c1 c p ∧ Kept b c ∧ Rows c (SafeGcd.Batch.run k w) := by
  induction k generalizing b w with
  | zero => omega
  | succ n ih =>
    obtain ⟨c,step,kept,next,rows⟩ := iteration (m := p) inner (by omega)
    cases n with
    | zero => exact ⟨c, step, kept, rows⟩
    | succ n =>
      obtain ⟨last,path,kept',out⟩ := ih (by omega) (by omega) next
      exact ⟨last, step.trans path, fun i hi => (kept' i hi).trans (kept i hi), out⟩

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
