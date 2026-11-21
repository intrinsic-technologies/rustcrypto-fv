import K256.Proofs.Sec1.Sqrt.WordEquality
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Words
import K256.Proofs.Sec1.SqrtChainExecution.Stages

namespace K256.Proofs.Sec1.SqrtLaterProducts

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open Common.Field.Multiply SqrtChainExecution
open LIR (lifted)

def OutputWords (base : Word) (ws : Limbs) :
    Transfer Value Ram LIR.Label signature Reg.count → Prop
  | .call loc _ | .jump loc => WordsAt loc.store base 64 ws
  | .stuck => True
  | .returned _ => False

private theorem outputWords_guard {g : Prop} [Decidable g]
    {t : Transfer Value Ram LIR.Label signature Reg.count} {base : Word} {ws : Limbs}
    (h : OutputWords base ws t) : OutputWords base ws (if g then t else .stuck) := by
  split
  · exact h
  · trivial

def schedule (i : Fin 13) : SqrtSchedule.Schedule :=
  if i.val = 2 then .third else if i.val = 4 then .fifth else .other

def productInputBase (i : Fin 13) (base : Word) : Word :=
  if i.val ∈ [7, 8, 9] then base else base + 40

def WordCertificate (i : Fin 13) : Prop :=
  ∀ {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} {sp : Word} {a : Limbs},
    args[4].get 64 = sp → Writable code mem (sp - 8) 440 →
    8 ≤ sp.toNat → sp.toNat + 432 ≤ 2^32 →
    Atom.All code args mem (savedAtoms i.castSucc sp a) →
    WordsAt mem (productInputBase i sp) 64 (words a (2 * i.val + 1)) →
    OutputWords sp (SqrtSchedule.mulWords (schedule i) (words a (2 * i.val + 1))
        (words a (2 * factorIndex[i]))) (lifted.program.runBlock (dialect code)
          ⟨productPC[i.castSucc], args, mem⟩)

private theorem read_gpr {args : Values Value Reg.count} {r : Fin Reg.count} {v : Word}
    (h : args[r] = ⟨64, v⟩) : args[r].get 64 = v :=
  congrArg (Value.get 64) h

open Lean Meta Elab.Tactic

private partial def scalarFacts (h : Expr) : MetaM (Array Expr × Array Expr) := do
  let t ← whnfD (← inferType h)
  if t.isAppOfArity ``And 2 then
    let (a, b) ← scalarFacts (← mkAppM ``And.left #[h])
    let (c, d) ← scalarFacts (← mkAppM ``And.right #[h])
    return (a ++ c, b ++ d)
  if t.isConstOf ``True then return (#[], #[])
  let some (_, lhs, _) := t.eq? | throwError "expected a saved SEC1 field word"
  if lhs.isAppOf ``memLoad then return (#[← mkExpectedTypeHint h t], #[])
  let p ← mkAppM ``read_gpr #[h]
  let some (_, lhs, rhs) := (← inferType p).eq? | throwError "expected register read"
  let read := lhs.appArg!
  let index := read.getArg! 6
  let index ← if (← inferType index).isAppOf ``Fin then mkAppM ``Fin.val #[index] else pure index
  let some i ← (evalNat (← whnfD index)).run | throwError "expected a saved register index"
  let reg ← CFG.Eval.elementAt (read.getArg! 5) i 53
  let lhs := mkApp2 (mkConst ``Value.get) (mkNatLit 64) reg
  return (#[], #[← mkExpectedTypeHint p (← mkEq lhs rhs)])

elab "certify_product" label:term:max variant:term:max inputOffset:num : tactic => withMainContext do
  let ns := #[`code, `args, `mem, `sp, `a, `hsp, `writable, `room, `bound, `saved, `squared].map mkIdent
  let sp := mkIdent `sp
  let room := mkIdent `room
  let hsp := mkIdent `hsp
  evalTactic (← `(tactic| intro $ns*))
  evalTactic (← `(tactic| have slot : ($sp - (8 : BitVec 64)).toNat = ($sp).toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ ($sp).toNat; exact $room)))
  let squared := mkIdent `squared
  let args := mkIdent `args
  let mem := mkIdent `mem
  let code := mkIdent `code
  if inputOffset.getNat == 0 then
    evalTactic (← `(tactic| change WordsAt $mem $sp 64 _ at $squared:ident))
  else
    evalTactic (← `(tactic| change WordsAt $mem ($sp + $inputOffset) 64 _ at $squared:ident))
  evalTactic (← `(tactic| change OutputWords $sp (SqrtSchedule.mulWords $variant _ _)
    (lifted.program.runBlock (dialect $code) ⟨$label, $args, $mem⟩)))
  let g ← getMainGoal
  let ((memoryFacts, registerFacts), squared) ← g.withContext do
    let saved ← getLocalDeclFromUserName `saved
    let squared ← getLocalDeclFromUserName `squared
    return (← scalarFacts saved.toExpr, squared.toExpr)
  let (names, regNames, hs) ← g.withContext do
    let mut memHyps := #[]
    for i in [:5] do
      let p := mkApp2 squared (mkNatLit i) (← mkDecideProof
        (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit 5]))
      memHyps := memHyps.push p
    memHyps := memHyps ++ memoryFacts
    let mut hs : Array Hypothesis := #[]
    let mut names := #[]
    let mut regNames := #[]
    for p in memHyps do
      let n := Name.mkSimple s!"stackWord{names.size}"
      names := names.push (mkIdent n)
      hs := hs.push {userName := n, type := ← inferType p, value := p}
    for p in registerFacts do
      let n := Name.mkSimple s!"registerWord{regNames.size}"
      regNames := regNames.push (mkIdent n)
      hs := hs.push {userName := n, type := ← inferType p, value := p}
    return (names, regNames, hs)
  let (_, g) ← g.assertHypotheses hs
  replaceMainGoal [g]
  for n in names do
    evalTactic (← `(tactic| try simp (config := {bitVecOfNat := false}) only
      [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.reduceOfNat, add_zero_lit,
        Lift.reduceAddOffset, Lift.reduceSubOffset, Fin.getElem_fin] at $n:ident))
  for n in names ++ regNames do
    evalTactic (← `(tactic| try simp only [savedValue, Nat.reduceEqDiff, ↓reduceIte, Fin.getElem_fin] at $n:ident))
  evalTactic (← `(tactic| lifted_registers [$hsp]))
  evalTactic (← `(tactic| subst $sp))
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let loc := ty.consumeMData.appArg!.consumeMData.appArg!
  let fdefs ← (← Refine.Tactic.constDefs (mkConst ``LIR.lifted)).mapM Refine.Tactic.simpArg
  let defs ← (← Refine.Tactic.blockDefs (mkConst ``LIR.lifted) loc).mapM Refine.Tactic.simpArg
  evalTactic (← `(tactic| cfg_eval [$fdefs,*, $defs,*]))
  evalTactic (← `(tactic| repeat' apply outputWords_guard))
  evalTactic (← `(tactic| change WordsAt _ _ _ _))
  evalTactic (← `(tactic| lifted_word_reads [$names,*]))
  unless regNames.isEmpty do
    let rs ← regNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
    evalTactic (← `(tactic| all_goals try simp only [$rs,*]))
  evalTactic (← `(tactic| all_goals dsimp only [SqrtSchedule.mulWords,
    SqrtSchedule.addPartial, SqrtSchedule.addHigh, SqrtSchedule.addDiagonalThree,
    SqrtSchedule.addFinalCarry, SqrtSchedule.convolution, SqrtSchedule.reduceWords]))
  let gs ← (← getGoals).mapM fun g => g.withContext do
    let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected a product word equality"
    let some v ← CFG.Eval.getElem? rhs | throwError "expected a literal product result"
    g.replaceTargetDefEq (← mkEq lhs v)
  setGoals gs
  evalTactic (← `(tactic| all_goals lifted_word_eq [SqrtSchedule.scaleHigh]))

end K256.Proofs.Sec1.SqrtLaterProducts
