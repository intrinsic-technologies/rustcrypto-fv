import K256.Proofs.Sec1.Sqrt.Finish.FromProduct
import K256.Proofs.Sec1.Sqrt.Finish.InlineSquare
import K256.Proofs.Sec1.SqrtChainExecution.Composition
import K256.Proofs.Sec1.Sqrt.Finish.Status
import K256.Proofs.Sec1.Sqrt.WordEquality
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Call

namespace K256.Proofs.Sec1.Sqrt.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field
open K256.Proofs.Sec1.LIR (lifted)

open K256.Proofs.Sec1.Serialize.Normalize (carry top)

private def foldedStatus (d : Limbs) (t0 : Word) : Word :=
  let t1 := carry t0 d[1]
  let t2 := carry t1 d[2]
  let t3 := carry t2 d[3]
  let t4 := top t3 d[4]
  let m : Word := 4503599627370495
  let isZero := (((t1 ||| t0) ||| t2) ||| t3) &&& m ||| t4
  let isP := (((t0 ^^^ 4294968272) &&& t1) &&& t2) &&& t3 &&& ((0xf000000000000 : Word) ^^^ t4)
  ((if isZero = 0 then (1 : BitVec 8) else 0) |||
    (if isP = m then (1 : BitVec 8) else 0)).setWidth 64

private def directStatus (d : Limbs) : Word := foldedStatus d (d[0] + 4294968273 * (d[4] >>> 48))

private def directDifference (rhs sq : Limbs) : Limbs :=
  #v[0x3ffffbfffff0bc + (rhs[0] - sq[0]), rhs[1] + 0x3ffffffffffffc - sq[1],
    rhs[2] + 0x3ffffffffffffc - sq[2], rhs[3] + 0x3ffffffffffffc - sq[3],
    0x3fffffffffffc + (rhs[4] - sq[4])]

private def directCompare (a rhs : Limbs) : Word := directStatus (directDifference rhs (inlineSquareWords a))

open Lean Meta Elab Tactic

private theorem statusIteCongr {p q : Prop} [Decidable p] [Decidable q] (h : p = q)
    (a b : BitVec 8) : (if p then a else b) = if q then a else b := by
  subst q
  by_cases h : p <;> simp only [h, ite_true, ite_false]

private theorem orCongr {a b c d : BitVec 8} (ab : a = b) (cd : c = d) :
    a ||| c = b ||| d := by cases ab; cases cd; rfl

elab "project_comparison_byte" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).consumeMData.eq? | throwError "expected flag equality"
  let head ← K256.Proofs.Sec1.Sqrt.WordReads.exposeLimb lhs
  let g ← mkFreshExprSyntheticOpaqueMVar (← mkEq head.expr rhs)
  goal.assign (← mkEqTrans (← head.getProof) g)
  replaceMainGoal [g.mvarId!]

elab "compare_test" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, p, q) := (← instantiateMVars (← g.getType)).consumeMData.eq? | throwError "expected test equality"
  let some (_, left, k) := p.eq? | throwError "expected a left equality test"
  let some (_, right, k') := q.eq? | throwError "expected a right equality test"
  unless ← isDefEq k k' do throwError "tests use different constants"
  let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq left right)
  let f ← withLocalDeclD `w (← inferType left) fun w => do mkLambdaFVars #[w] (← mkEq w k)
  g.assign (← mkAppM ``congrArg #[f, h])
  replaceMainGoal [h.mvarId!]

private theorem registerTests (p z₁ z₂ oldP oldZ backup : Word) :
    let pByte := if (cmpSpec p (4503599627370495 : Word)).ZF = true then (1 : BitVec 8) else 0
    let zByte := if ((orFlags (z₁ ||| z₂)).ZF.getD false) = true then (1 : BitVec 8) else 0
    ((mergeGPR 8 ((mergeGPR 8 pByte oldP).setWidth 8 |||
      (mergeGPR 8 zByte oldZ).setWidth 8) backup).setWidth 8).setWidth 64 =
    ((if z₁ ||| z₂ = 0 then (1 : BitVec 8) else 0) |||
      (if p = 4503599627370495 then (1 : BitVec 8) else 0)).setWidth 64 := by
  simp only [setWidth_mergeGPR8, cmpSpec_ZF, orFlags, Option.getD_some, beq_iff_eq, BitVec.or_comm]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem compareStatusCall {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} {sp : Word}
    (a b : Limbs) (hsp : args[4].get 64 = sp) (hr12 : args[12].get 64 = 68719492368) (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2 ^ 32)
    (hcode : sp.toNat + 432 ≤ 0x11a14c ∨ 0x11a51c + 8 ≤ sp.toNat)
    (ha : WordsAt mem (sp + 40) 64 a)
    (hb0 : memLoad mem (sp + 352) 64 = b[0]) (hb1 : memLoad mem (sp + 328) 64 = b[1])
    (hb2 : memLoad mem (sp + 304) 64 = b[2]) (hb3 : memLoad mem (sp + 336) 64 = b[3])
    (hb4 : memLoad mem (sp + 320) 64 = b[4]) :
    CallTo (lifted := lifted) (fun child _ =>
      (child.arguments[7]'(show 7 < Reg.count by decide)).get 64 = directCompare a b)
      (lifted.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩) := by
  have haddr : (sp - (8 : Word)).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase)
  lifted_registers [hsp, hr12]
  subst sp
  run_tac Lean.Elab.Tactic.withMainContext do
    let d ← Lean.Meta.getLocalDeclFromUserName `ha
    let _ ← Refine.Tactic.introAtoms d.fvarId "limb"
  final_product_block
  project_comparison_byte
  refine (registerTests _ _ _ _ _ _).trans ?_
  change _ = (directStatus (directDifference b (inlineSquareWords a)))
  apply congrArg (fun b : BitVec 8 => b.setWidth 64)
  apply orCongr
  all_goals
    apply statusIteCongr
    compare_test
    lifted_word_reads [word0, word1, word2, word3, word4, hb0, hb1, hb2, hb3, hb4]
    simp only [hr12]
    lifted_word_eq [directDifference, inlineSquareWords, inlineSquareStage0, inlineSquareStage1,
      inlineSquareStage2, inlineSquareStage3, inlineSquareStage4, inlineSquareStage5, inlineSquareStage6,
      inlineSquareStage7, Serialize.Normalize.carry, Serialize.Normalize.top]

set_option maxRecDepth 4096 in
private theorem directDifference_eq (b sq : Limbs) :
    directDifference b sq = difference b sq := by
  apply Vector.ext
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  · exact Eq.refl ((0x3ffffbfffff0bc : Word) + (b[0] - sq[0]))
  · exact congrArg (· - sq[1]) (BitVec.add_comm b[1] _)
  · exact congrArg (· - sq[2]) (BitVec.add_comm b[2] _)
  · exact congrArg (· - sq[3]) (BitVec.add_comm b[3] _)
  · exact Eq.refl ((0x3fffffffffffc : Word) + (b[4] - sq[4]))

private theorem directStatus_eq (d : Limbs) : directStatus d = zeroStatus d := by
  have h : d[0] + 4294968273 * (d[4] >>> 48) = Serialize.Normalize.first d :=
    (BitVec.add_comm _ _).trans (congrArg (fun x : Word => x + d[0]) (BitVec.mul_comm _ _))
  exact congrArg (foldedStatus d) h

private theorem transferLowByte (tr : Transfer Value Ram lifted.Label Lift.signature Reg.count)
    (w : Word) :
    CallTo (lifted := lifted) (fun child _ =>
      (child.arguments[7]'(show 7 < Reg.count by decide)).get 64 = w) tr →
    (match tr with
      | .call child _ => some (((child.arguments[7]'(show 7 < Reg.count by decide)).get 64).setWidth 8)
      | _ => none) = some (w.setWidth 8) := by
  cases tr <;> intro h
  case call child frame =>
    exact congrArg (fun x : Word => some (x.setWidth 8)) h
  all_goals exact h.elim

private theorem comparisonByte_eq_of_call {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {w : Word}
    (h : CallTo (lifted := lifted) (fun child _ =>
      (child.arguments[7]'(show 7 < Reg.count by decide)).get 64 = w)
      (lifted.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩)) :
    comparisonByte code args mem = some (w.setWidth 8) :=
  transferLowByte _ w h

set_option maxHeartbeats 1000000 in
private theorem comparisonAtProductRaw {code : CodeMap} {fr : Activation} {a : Limbs}
    {args : Values Value Reg.count} {mem : Ram}
    (geom : SqrtChainExecution.Geometry code fr)
    (pre : SqrtChainExecution.ProductState code fr a 13 args mem) :
    comparisonByte code args mem = some ((directCompare (SqrtChainExecution.words a 27) a).setWidth 8) := by
  let sp := fr.rsp - 440
  have h := pre.frame
  change Atom.All code args mem (LIR.Fn115950.frameAt .l11a14c fr) at h
  simp only [LIR.Fn115950.frameAt, LIR.Fn115950.frameAtG1, Atom.All, Atom.Holds] at h
  obtain ⟨rsp, _, _, _, _, _, _, _, _, _, _, _, rd, _, _, stack, room, _, _⟩ := h
  have hbase : 440 ≤ fr.rsp.toNat := by omega
  have hspNat : sp.toNat = fr.rsp.toNat - 440 := BitVec.toNat_sub_of_le hbase
  have readBound := rd.low
  have stackNat : (fr.rsp - 552).toNat = fr.rsp.toNat - 552 :=
    BitVec.toNat_sub_of_le (by change 552 ≤ fr.rsp.toNat; omega)
  have callNat : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have hsa : Writable code mem (sp - 8) 440 := stack.sub (by omega) (by omega)
  have hcode : sp.toNat + 432 ≤ 0x11a14c ∨ 0x11a51c + 8 ≤ sp.toNat := by
    rcases geom.stackCode with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have wordsAt : WordsAt mem (sp + 40) 64 (SqrtChainExecution.words a 27) := by
    change WordsAt mem (fr.rsp - 440 + 40) 64 _
    rw [show fr.rsp - 440 + 40 = fr.rsp - 400 by bv_omega]
    exact pre.squared
  have saves := pre.saved
  change Atom.All code args mem (SqrtChainExecution.savedAtoms 13 sp a) at saves
  have saves' : Atom.All code args mem
      [.mem (sp + 352) 64 a[0], .mem (sp + 328) 64 a[1], .mem (sp + 304) 64 a[2],
        .mem (sp + 336) 64 a[3], .mem (sp + 320) 64 a[4], .gpr 12 68719492368] := saves
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hc, _⟩ := saves'
  have harg4 : args[4].get 64 = sp := congrArg (Value.get 64) rsp
  have harg12 : args[12].get 64 = 68719492368 := congrArg (Value.get 64) hc
  have run := compareStatusCall (SqrtChainExecution.words a 27) a harg4 harg12 hsa
    (by omega) (by omega) hcode wordsAt hb0 hb1 hb2 hb3 hb4
  exact comparisonByte_eq_of_call run

private theorem directCompare_eq (a rhs : Limbs) :
    directCompare a rhs = comparisonStatus a rhs := by
  calc
    directCompare a rhs = directStatus (directDifference rhs (squareWords a)) :=
      congrArg (fun sq => directStatus (directDifference rhs sq)) (inlineSquareWords_eq a)
    _ = directStatus (difference rhs (squareWords a)) :=
      congrArg directStatus (directDifference_eq rhs (squareWords a))
    _ = comparisonStatus a rhs := directStatus_eq _

theorem comparisonAtProduct {code : CodeMap} {fr : Activation} {a : Limbs}
    {args : Values Value Reg.count} {mem : Ram}
    (geom : SqrtChainExecution.Geometry code fr)
    (pre : SqrtChainExecution.ProductState code fr a 13 args mem) :
    comparisonByte code args mem = some ((comparisonStatus (SqrtChainExecution.words a 27) a).setWidth 8) :=
  (comparisonAtProductRaw geom pre).trans
    (congrArg (fun w : Word => some (w.setWidth 8)) (directCompare_eq _ _))

theorem compareStage {code : CodeMap} {fr : Activation} {a : Limbs}
    (geom : SqrtChainExecution.Geometry code fr) : SqrtChainExecution.CompareStage code fr a := by
  intro args mem pre
  exact finishProductStatus geom pre (comparisonAtProduct geom pre)

end K256.Proofs.Sec1.Sqrt.Finish
