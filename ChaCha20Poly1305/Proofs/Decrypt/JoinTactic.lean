import ChaCha20Poly1305.Proofs.Decrypt.Micro

open Lean Meta Elab Tactic ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Refine.Tactic

namespace ChaCha20Poly1305.Proofs.Decrypt

syntax "unpack_atoms" ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| unpack_atoms $h:ident [$ls,*]) => withMainContext do
    evalTactic (← `(tactic| simp only [refine_layout,$ls,*] at $h:ident))
    withMainContext do
      let d ← getLocalDeclFromUserName h.getId
      let ns ← introAtoms d.fvarId h.getId.toString
      withMainContext (registerNames .rewrite ns)

syntax "join_atoms" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
elab_rules : tactic
  | `(tactic| join_atoms [$ls,*]) => withMainContext do
    for d in ← hypsWithHead ``RamWriteFrame do registerNames .frame #[d.userName]
    let shared ← Shared.new ls.getElems
    evalTactic (← `(tactic| simp only [refine_layout,$ls,*]))
    let mut left := []
    for g in ← getGoals do
      let some g' ← simpShallow shared.layout g | continue
      for t in ← runOn g' (evalTactic (← `(tactic| repeat' refine And.intro ?_ ?_))) do
        if (← instantiateMVars (← t.getType)).isAppOf ``RamWriteFrame then
          left := left ++ (← closeFrame shared t)
        else
          left := left ++ (← closeAtom shared t)
    setGoals left

end ChaCha20Poly1305.Proofs.Decrypt
