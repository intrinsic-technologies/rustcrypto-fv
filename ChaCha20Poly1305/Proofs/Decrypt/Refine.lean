import ChaCha20Poly1305.Proofs.Common.Refine.Tactic

open Lean Meta Elab Tactic
open ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Refine.Tactic

namespace ChaCha20Poly1305.Proofs.Decrypt

syntax "refine_one" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| refine_one [$ls,*]) => do
    evalTactic (← `(tactic| refine_intro))
    evalTactic (← `(tactic| refine_uir [$ls,*]))
    let shared ← Shared.new ls.getElems
    let mut left := []
    for g in ← getGoals do
      let leaves ← g.withContext do
        let ty ← instantiateMVars (← g.getType)
        unless (runGoal? ty).isSome do return { left := [g] }
        let defs ← (← constDefs (ty.consumeMData.getArg! 0)).mapM simpArg
        runLifted shared defs 1 true g
      for t in leaves.targets do
        left := left ++ ((← closeTarget? shared t).getD [t])
      left := left ++ leaves.left
    setGoals left

end ChaCha20Poly1305.Proofs.Decrypt
