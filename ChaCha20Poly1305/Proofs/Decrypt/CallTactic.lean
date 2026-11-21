import ChaCha20Poly1305.Proofs.Decrypt.Invoke

open Lean Meta Elab Tactic
open ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Refine.Tactic

namespace ChaCha20Poly1305.Proofs.Decrypt

syntax "prepare_call " term : tactic
elab_rules : tactic
  | `(tactic| prepare_call $mk) => withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let_expr Exists ctx body := t | throwError "expected a call obligation"
    let .lam _ _ b _ := body | throwError "expected call context"
    let_expr And rel _ := b | throwError "expected callee and resume obligations"
    let l ← whnfR (rel.getArg! 14)
    let m := l.getArg! 6
    let ctor ← Term.elabTermEnsuringType mk (← mkArrow (← inferType m) ctx)
    let term ← Term.exprToSyntax (← whnfR (mkApp ctor m))
    evalTactic (← `(tactic| refine ⟨$term,?_,?_⟩))

syntax "close_resume" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
elab_rules : tactic
  | `(tactic| close_resume [$ls,*]) => withMainContext do
    let s ← Shared.new ls.getElems
    evalTactic (← `(tactic| unfold Layout.Resumes))
    introReturn s
    evalTactic (← `(tactic| refine ⟨?_,?_⟩))
    let [ga,gr] ← getGoals | throwError "expected guard and frame relation"
    let mut left := []
    for g in (← simpShallow s.resume ga).toList do
      if let some g' ← normGoal s g then left := left ++ [g']
    for g in (← simpShallow s.resume gr).toList do
      left := left ++ (← closeRel s g)
    setGoals left

end ChaCha20Poly1305.Proofs.Decrypt
