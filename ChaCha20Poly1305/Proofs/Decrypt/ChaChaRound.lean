import ChaCha20Poly1305.Proofs.Decrypt.ChaChaWords
import ChaCha20Poly1305.Proofs.Common.Refine.Tactic

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
open X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Refine Standards.RFC.ChaCha20Poly1305

structure Data where
  words : Vector UInt32 16
  count : BitVec 64

inductive Label | q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | count | finish
  deriving DecidableEq
inductive Op : Nat → Type | step (index : Label) : Op 1

def program : Program Op Label (fun _ => 1) 0 := ⟨fun
  | .q0 => .letOp (.step .q0) #v[0] (.terminate (.br ⟨.q1, #v[1]⟩))
  | .q1 => .letOp (.step .q1) #v[0] (.terminate (.br ⟨.q2, #v[1]⟩))
  | .q2 => .letOp (.step .q2) #v[0] (.terminate (.br ⟨.q3, #v[1]⟩))
  | .q3 => .letOp (.step .q3) #v[0] (.terminate (.br ⟨.q4, #v[1]⟩))
  | .q4 => .letOp (.step .q4) #v[0] (.terminate (.br ⟨.q5, #v[1]⟩))
  | .q5 => .letOp (.step .q5) #v[0] (.terminate (.br ⟨.q6, #v[1]⟩))
  | .q6 => .letOp (.step .q6) #v[0] (.terminate (.br ⟨.q7, #v[1]⟩))
  | .q7 => .letOp (.step .q7) #v[0] (.terminate (.br ⟨.count, #v[1]⟩))
  | .count => .letOp (.step .count) #v[0] (.terminate (.condBr 1 ⟨.q0, #v[1]⟩ ⟨.finish, #v[1]⟩))
  | .finish => .terminate (.ret #v[])⟩

def advance (i : Label) (p : Data) : Data :=
  match i with
  | .q0 => ⟨qround p.words 0 4 8 12, p.count⟩
  | .q1 => ⟨qround p.words 1 5 9 13, p.count⟩
  | .q2 => ⟨qround p.words 2 6 10 14, p.count⟩
  | .q3 => ⟨qround p.words 3 7 11 15, p.count⟩
  | .q4 => ⟨qround p.words 0 5 10 15, p.count⟩
  | .q5 => ⟨qround p.words 1 6 11 12, p.count⟩
  | .q6 => ⟨qround p.words 2 7 8 13, p.count⟩
  | .q7 => ⟨qround p.words 3 4 9 14, p.count⟩
  | .count => ⟨p.words, p.count - 1⟩
  | .finish => p

def dialect : Dialect Op Data Unit :=
  Dialect.ofPure (fun (.step i) args => advance i args[0]) (fun a => a.count != 0)

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
