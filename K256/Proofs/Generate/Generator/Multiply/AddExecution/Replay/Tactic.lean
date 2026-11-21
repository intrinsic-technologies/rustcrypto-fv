import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Layout

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Lean Meta Elab Tactic
open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

private def isWord (name : Name) : Bool :=
  name.getPrefix == `K256.Proofs.Generate.Generator.Multiply.AddGraph

elab "replay_value" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
    | throwError "expected a replay value equality"
  let rhs ← if rhs.isAppOf ``values || rhs.isAppOf ``decode then
      withTransparency .default <| withCanUnfoldPred (fun cfg info => do
        if isWord info.name || info.name == ``Value.ofBool then return false
        canUnfoldDefault cfg info) <| whnf rhs
    else pure rhs
  let mut seen := lhs.getUsedConstantsAsSet
  let mut todo := rhs.getUsedConstants
  let mut rules ← #[``add_zero_lit, ``zero_add_lit, ``BitVec.add_zero, ``BitVec.zero_add,
    ``BitVec.mul_one, ``Value.truth_ofBool].mapM Refine.Tactic.simpArg
  while let some name := todo.back? do
    todo := todo.pop
    if !isWord name || seen.contains name then continue
    seen := seen.insert name
    let .defnInfo d ← getConstInfo name | throwError "expected a graph word"
    rules := rules.push (← Refine.Tactic.simpArg name)
    todo := todo ++ d.value.getUsedConstants
  replaceMainGoal [← g.replaceTargetDefEq (← mkEq lhs rhs)]
  evalTactic (← `(tactic| (simp -failIfUnchanged only [$rules,*]; all_goals rfl)))

scoped syntax "replay_segment " num " regs " "[" ("(" num ", " term ")"),* "]"
    " loads " "[" ("(" term ", " term ", " term ")"),* "]"
    " stores " "[" ("(" term ", " num ", " term ", " term ")"),* "]" : tactic

set_option hygiene false in
elab_rules : tactic
  | `(tactic| replay_segment $k:num
      regs [$[($indices:num, $values:term)],*]
      loads [$[($inputs:term, $sources:term, $readWords:term)],*]
      stores [$[($outputs:term, $codes:num, $dests:term, $writeWords:term)],*]) => do
    let idx := k.getNat
    let heap := mkIdent (`K256.Proofs.Generate.Generator.Multiply.AddReplay ++ Name.mkSimple s!"heap{idx}")
    let suffix := if idx == 0 then "" else s!"_{idx}"
    let coverage := mkIdent (`K256.Proofs.Generate.LIR ++ Name.mkSimple s!"code_l10a410{suffix}")
    evalTactic (← `(tactic| (
      intro a m vals mem
      obtain ⟨stack, dest, src, ret, cellsIn⟩ := mem
      change Models s.fr (decode s) m $heap at cellsIn
      have room := r.room
      have srcAbove := r.srcAbove
      have dstAbove := r.dstAbove
      have apart := r.apart
      have low := stack.readable.low
      have lowDst := dest.readable.low
      have lowSrc := src.low
      have lowRet := ret.low
      have baseEq : (s.fr.rsp - 536).toNat = s.fr.rsp.toNat - 536 :=
        BitVec.toNat_sub_of_le room
      have bounds : Bounds s.fr := ⟨room, srcAbove, dstAbove, lowSrc, lowDst, apart⟩
      have incl := fun x hx => inc x ($coverage x hx))))
    let mut facts : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    for i in [:indices.size] do
      let index : NumLit := ⟨indices[i]!.raw⟩
      let v := values[i]!
      let h := mkIdent <| Name.mkSimple s!"h{index.getNat}"
      let initial : Option Name := match index.getNat with
        | 3 => some `rbx | 4 => some `rsp | 5 => some `rbp | 6 => some `rsi | 7 => some `rdi
        | 12 => some `r12 | 13 => some `r13 | 14 => some `r14 | 15 => some `r15
        | _ => none
      if let some field := initial then
        let projection := mkIdent (`K256.Proofs.Generate.Generator.Multiply.AddReplay.Ready ++ field)
        evalTactic (← `(tactic| have $h : a[$index] = $v :=
          (show a[$index] = s.seed[$index] from vals $index).trans ($projection r)))
      else
        evalTactic (← `(tactic| have $h : a[$index] = $v := vals $index))
      facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
    for i in [:inputs.size] do
      let h := mkIdent <| Name.mkSimple s!"load{i}"
      let (slot, addr, word) := (inputs[i]!, sources[i]!, readWords[i]!)
      evalTactic (← `(tactic| have $h : memLoad m $addr 64 = $word :=
        cellsIn.readAt $slot (by unfold Slot.address; bv_omega)))
      facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
    evalTactic (← `(tactic| (
      refine ⟨?_, ?_, ?ev, ?values, ?memory, ?frame⟩
      case ev =>
        arithmetic_prefix [$facts,*, Value.truth_ofBool, BitVec.shiftLeft_eq_mul_twoPow _ 0,
          BitVec.shiftLeft_eq_mul_twoPow _ 1, BitVec.shiftLeft_eq_mul_twoPow _ 2,
          BitVec.shiftLeft_eq_mul_twoPow _ 3, BitVec.add_zero, Lift.reduceSubOffset, Lift.reduceAddOffset]
        segment_words [$facts,*]
        repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using incl)
        rfl
      case values =>
        repeat' apply ValuesMatch.push
        all_goals first | with_reducible exact vals | replay_value
      case frame =>
        unfold regions
        slot_state region
      refine ⟨by slot_state region, by slot_state region, by slot_state region, by slot_state region, ?_⟩)))
    let target ← instantiateMVars (← getMainTarget)
    unless target.isAppOfArity ``Models 4 do throwError "expected the outgoing slot model"
    let mut mem := target.getArg! 2
    let mut writes := #[]
    for _ in [:outputs.size] do
      unless mem.isAppOfArity ``memStore 6 do throwError "expected a store in the outgoing memory"
      writes := writes.push mem.appArg!
      mem := mem.getArg! 2
    writes := writes.reverse
    let mut prev := mkIdent `cellsIn
    for i in [:outputs.size] do
      let h := mkIdent <| Name.mkSimple s!"model{i}"
      let actual ← withMainContext <| Term.exprToSyntax writes[i]!
      let (slot, addr, word, code) := (outputs[i]!, dests[i]!, writeWords[i]!, codes[i]!)
      evalTactic (← `(tactic| have $h := Models.writeAt bounds $prev $slot $code
        (a := $addr) (by unfold Slot.address; bv_omega)
        (v := $actual) (by change _ = $word; replay_value)))
      prev := h
    evalTactic (← `(tactic| apply Models.changeCodes $prev <;> decide +kernel))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
