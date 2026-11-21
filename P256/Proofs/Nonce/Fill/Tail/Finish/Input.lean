import P256.Proofs.Nonce.Fill.Tail.Finish.Call

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Signing.Search
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem call_input [Bindings] {initial s t : RamState} {orderAddress : BitVec 64}
    {state : Nonce.State} (input : Prepared initial s orderAddress state)
    (effect : (callEffect (fun _ => 0x106f40) 0x1076fa s).Holds s t) :
    Nat256At t (t.regValue .rdi) (nextCandidate state).1 := by
  have di : t.regValue .rdi = frameBase initial + 72 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans input.rdi
  rw [di]
  refine ⟨input.integer.1, ?_⟩
  intro i hi
  apply Eq.trans _ (input.integer.2 i hi)
  have address : frameBase initial + 72 = stackPtr initial - 160 :=
    frameBase_add initial (offset := 72) (by decide)
  rw [address]
  exact ScalarFrame.call_byte (frameOffset := 232) (by decide) input.rsp effect (offset := 160) (len := 32)
    (by decide) (by decide) hi

end P256.Proofs.Nonce.Fill.Tail.Finish
