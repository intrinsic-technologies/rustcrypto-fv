import K256.Proofs.Generate.Generator.Affine.Products.Multiply.Normalize
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Commutative
import K256.Proofs.Sec1.SqrtProducts.SecondSchedule

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Common.Tactic
open Lean Meta Elab.Tactic

private def ProductOutput (sp : Word) (x y : Limbs) :
    Transfer Value Ram Label signature Reg.count → Prop
  | .call loc _ => WordsAt loc.store (sp + 152) 64 x ∧ WordsAt loc.store (sp + 192) 64 y
  | .stuck => True
  | _ => False

private theorem productOutput_guard {g : Prop} [Decidable g]
    {t : Transfer Value Ram Label signature Reg.count} {sp : Word} {x y : Limbs}
    (h : ProductOutput sp x y t) : ProductOutput sp x y (if g then t else .stuck) := by
  split
  · exact h
  · trivial

private theorem productLoadAddr {m : Ram} {a b : Word} (h : a = b) :
    memLoad m a 64 = memLoad m b 64 :=
  congrArg (fun p => memLoad m p 64) h

open Sec1.Sqrt.WordReads in
private partial def normalizeProductWord (env : Env) (e : Expr) :
    StateRefT (Std.HashMap Expr Simp.Result) MetaM Simp.Result := do
  unless e.hasFVar do return { expr := e }
  if let some r := (← get)[e]? then return r
  let r ←
    if e.isAppOfArity ``memLoad 5 then do
      let args := e.getAppArgs
      let addr ← normalizeProductWord env args[3]!
      let (offset, _) ← Meta.simp addr.expr env.shared.words.1 env.shared.words.2
      let addr ← addr.mkEqTrans offset
      let source := mkAppN e.getAppFn (args.set! 3 addr.expr)
      let load ← read env source
      let h := addr.proof?.map fun p =>
        mkAppN (mkConst ``productLoadAddr) #[args[2]!, args[3]!, addr.expr, p]
      let r : Simp.Result := { expr := source, proof? := h }
      let r ← r.mkEqTrans load
      r.mkEqTrans (← normalizeProductWord env load.expr)
    else if let .app f a := e then do
      let rf ← normalizeProductWord env f
      let ra ← normalizeProductWord env a
      Simp.mkCongr rf ra
    else pure { expr := e }
  modify (·.insert e r)
  return r

set_option linter.unusedVariables false in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem productOutputWords {sp : Word} {a : Registers} {m : Ram} {x y w : Limbs}
    (rsp : a[4].get 64 = sp + 280) (src : a[6].get 64 = sp + 752)
    (scalar : a[2].get 64 = sp + 288) (dst : a[7].get 64 = sp + 376)
    (stack : Writable Extracted.programImage m (sp - 8) 336)
    (coords : Readable m (sp + 752) 80)
    (room : 8 ≤ sp.toNat) (high : sp.toNat + 832 ≤ 2^32)
    (ha : WordsAt m (sp + 752) 64 x) (hb : WordsAt m (sp + 792) 64 y)
    (hw : WordsAt m (sp + 288) 64 w)
    {b : Registers} {n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨.l10e4c0, a, m⟩ =
        .call ⟨.l114930, b, n⟩ (productNormalizeReturn .l10ecb2 0x10ecb2)) :
    WordsAt n (sp + 152) 64 (mulWords x w) ∧ WordsAt n (sp + 192) 64 (mulWords y w) := by
  have certificate : ProductOutput sp (mulWords w x) (Sec1.SqrtProducts.secondProduct y w)
      (program.runBlock (dialect Extracted.programImage) ⟨.l10e4c0, a, m⟩) := by
    have data := And.intro ha (And.intro hb hw)
    lifted_inputs data
    lifted_registers [rsp, src, scalar, dst]
    generate_block [rsp, src, scalar, dst, Lift.reduceAddOffset, Lift.reduceSubOffset]
    run_tac withMainContext do
      let goal ← getMainGoal
      let target := (← goal.getType).consumeMData
      let args := target.getAppArgs
      let #[base, xs, ys, transfer] := args
        | throwError "expected a product output predicate"
      let mut branch := transfer.consumeMData
      let mut guards := #[]
      while branch.isAppOfArity ``ite 5 do
        guards := guards.push (branch.getArg! 1, branch.getArg! 2, branch.getArg! 3)
        branch := (branch.getArg! 3).consumeMData
      unless branch.isAppOfArity ``Transfer.call 7 do
        throwError "expected a call at the end of the product block"
      let loc := branch.getArg! 5
      unless loc.isAppOfArity ``Location.mk 7 do throwError "expected call state"
      let out := loc.appArg!
      let wordsAt (offset : Nat) (limbs : Expr) : MetaM Expr := do
        let addr ← mkAppM ``HAdd.hAdd #[base, toExpr (BitVec.ofNat 64 offset)]
        return mkAppN (mkConst ``WordsAt) #[out, addr, mkNatLit 64, mkNatLit 5, limbs]
      let post ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``And)
        (← wordsAt 152 xs) (← wordsAt 192 ys))
      let proof := guards.foldr (fun (p, inst, t) h =>
        mkAppN (mkConst ``productOutput_guard) #[p, inst, t, base, xs, ys, h]) post
      goal.assign proof
      replaceMainGoal [post.mvarId!]
    constructor
    run_tac withMainContext do
      let shared ← Refine.Tactic.Shared.new #[]
      let inputs ← (List.range 15).toArray.mapM fun i => do
        Sec1.Sqrt.WordReads.inputOf (← getLocalDeclFromUserName (.mkSimple s!"word{i}"))
      let env : Sec1.Sqrt.WordReads.Env :=
        { shared, inputs, bases := #[(← getLocalDeclFromUserName `sp).toExpr] }
      let mut cache := {}
      let mut left := #[]
      for wordSet in ← getGoals do
        for g in ← Sec1.Sqrt.WordReads.wordGoals wordSet do
          let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected a word equality"
          let (normalized, cache') ← (normalizeProductWord env lhs).run cache
          cache := cache'
          let ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
          let pureGoal ← mkFreshExprSyntheticOpaqueMVar
            (mkApp3 (mkConst ``Eq [.one]) ty normalized.expr rhs)
          g.assign (mkAppN (mkConst ``Eq.trans [.one])
            #[ty, lhs, normalized.expr, rhs, ← normalized.getProof, pureGoal])
          left := left.push pureGoal.mvarId!
      replaceMainGoal left.toList
    all_goals try dsimp -zeta only [Sec1.SqrtProducts.secondProduct, Sec1.SqrtProducts.secondCoefficients,
      Multiply.SqrtSchedule.reduceWords]
    all_goals first
      | lifted_word_eq []
      | (rw [BitVec.and_comm]; lifted_word_eq [])
  rw [run] at certificate
  change WordsAt _ _ _ _ ∧ WordsAt _ _ _ _ at certificate
  rwa [Multiply.SqrtSchedule.mulWords_comm w x, Sec1.SqrtProducts.secondProduct_eq_mulWords] at certificate

end K256.Proofs.Generate.Generator.Affine
