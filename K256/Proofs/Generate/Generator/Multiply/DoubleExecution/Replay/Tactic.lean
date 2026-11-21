import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Layout

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open Lean Elab Tactic Meta
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Point
open K256.Proofs.Sec1.Affine.Uncompressed

scoped elab "expose_replay_value" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, l, r) := (← g.getType).eq? | throwError "expected equality"
  let r ← withTransparency .default <| whnf r
  replaceMainGoal [← g.change (← mkEq l r)]

syntax replayRegister := num " => " term

scoped elab "replay_segment" " using " code:term:max " from " start:num " to " stop:num
    " registers " "[" registers:replayRegister,* "]" " slots " slots:num
    " normalize " "[" norms:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let cur := mkIdent `cur
  let mem := mkIdent `mem
  let vals := mkIdent `vals
  let facts := mkIdent `facts
  let seed := mkIdent `a
  evalTactic (← `(tactic| (
    intro $cur $mem $vals $facts
    change Atom.All _ _ _ (memoryAtoms $(mkIdent `p) $(mkIdent `yy) $(mkIdent `zz)
      $(mkIdent `sp) $(mkIdent `count) $start) at $facts:ident
    simp only [memoryAtoms, Atom.All, Atom.Holds] at $facts:ident)))
  let names ← withMainContext do Refine.Tactic.introAtoms (← getFVarId facts) "input"
  if names.size != slots.getNat + 2 then
    throwError "expected {slots.getNat} memory slots, found {names.size - 2}"
  let mut regFacts := #[]
  for r in registers.getElems do
    let `(replayRegister| $idx:num => $rhs:term) := r | throwUnsupportedSyntax
    let i := idx.getNat
    let id := mkIdent (Name.mkSimple s!"reg{i}")
    let proof ← if i == 4 || i == 5 then
        let source := mkIdent (if i == 4 then `rsp else `rbp)
        `(term| (show $cur[$idx] = $seed[$idx] from $vals ($idx : Fin $start)).trans $source)
      else
        `(term| $vals ($idx : Fin $start))
    evalTactic (← `(tactic| have $id : $cur[$idx] = $rhs := $proof))
    regFacts := regFacts.push id
  let mut known : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for id in regFacts ++ (names.toList.drop 2).toArray.map mkIdent do
    known := known.push (← `(Lean.Parser.Tactic.simpLemma| $id:ident))
  evalTactic (← `(tactic| (
    refine ⟨?_, ?_, ?ev, ?values, ?memory, ?frame⟩
    case ev =>
      arithmetic_prefix [$known,*]
      segment_words [$known,*]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using $code)
      rfl
    case values =>
      repeat' apply ValuesMatch.push
      all_goals
        first
        | exact $vals
        | expose_replay_value
          first
          | with_reducible rfl
          | simp only [$norms,*, ↓Value.truth_ofBool, Value.ofBool, BitVec.shiftLeft_eq_mul_twoPow,
              (show ∀ t : BitVec 64, t + (0 : BitVec 64) = t from BitVec.add_zero),
              (show ∀ t : BitVec 64, (0 : BitVec 64) + t = t from BitVec.zero_add)] <;> rfl
    case memory =>
      change Atom.All _ _ _ (memoryAtoms $(mkIdent `p) $(mkIdent `yy) $(mkIdent `zz)
        $(mkIdent `sp) $(mkIdent `count) $stop)
      simp only [memoryAtoms, Atom.All, Atom.Holds]
      refine ⟨by slot_state region, ?_⟩
      segment_words [$known,*, eq_self_iff_true, true_and]
      repeat' apply And.intro
      all_goals
        first
        | exact True.intro
        | with_reducible rfl
        | simp only [$norms,*, ↓Value.truth_ofBool, Value.ofBool, BitVec.shiftLeft_eq_mul_twoPow,
            (show ∀ t : BitVec 64, t + (0 : BitVec 64) = t from BitVec.add_zero),
            (show ∀ t : BitVec 64, (0 : BitVec 64) + t = t from BitVec.zero_add)] <;> rfl
    case frame =>
      unfold writes
      slot_state region)))

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
