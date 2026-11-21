import Lean.Elab.Match
import Lean.Elab.Command

open Lean Elab

run_cmd Command.liftTermElabM do
  Term.withDeclName `AesGcm.Statements.aes128gcm_decrypt_in_place_writes_plaintext_or_rejects do
    discard <| Term.elabTerm (← `(fun (result : Option ByteArray) (accept : ByteArray → Prop)
      (reject : Prop) => match result with
      | some plaintext => accept plaintext
      | none => reject)) none
    Term.synthesizeSyntheticMVarsNoPostponing
