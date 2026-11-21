import Lean.Elab.Match
import Lean.Elab.Command

open Lean Elab

run_cmd Command.liftTermElabM do
  Term.withDeclName
      `ChaCha20Poly1305.Statements.chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag do
    discard <| Term.elabTerm (← `(fun (result : Option ByteArray) (accept : ByteArray → Prop)
      (reject : Prop) => match result with
      | some plaintext => accept plaintext
      | none => reject)) none
    Term.synthesizeSyntheticMVarsNoPostponing
