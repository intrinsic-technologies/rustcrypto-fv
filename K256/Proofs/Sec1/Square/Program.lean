import K256.Proofs.Common.CFG.IR
import K256.Proofs.Common.Field.Square

namespace K256.Proofs.Sec1.Square

open CFG Common.Field

abbrev Store := Limbs × Limbs

inductive Op : Nat → Type where
  | square : Op 0

def eval : {n : Nat} → Op n → Values Word n → Store → Option (Word × Store)
  | _, .square, _, s => some (0, (s.1, squareWords s.1))

def dialect : Dialect Op Word Store where
  eval := eval
  truth := (· != 0)

inductive Label where
  | entry

def program : Program Op Label (fun _ => 0) 0 where
  blocks | .entry => .letOp .square #v[] (.terminate (.ret #v[]))

theorem exec (s : Store) : program.Exec dialect ⟨⟨.entry, #v[], s⟩, []⟩
    ⟨#v[], none, (s.1, squareWords s.1)⟩ :=
  .done rfl

end K256.Proofs.Sec1.Square
