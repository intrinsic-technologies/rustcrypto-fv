import P256.Proofs.Nonce.Fill.Tail.Decode
import P256.Proofs.Nonce.Fill.Tail.Compare
import P256.Proofs.Nonce.Fill.Tail.Finish
import P256.Proofs.Nonce.Fill.Tail.Retry

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Signing.Search

theorem tail_accept [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state)
    (valid : ValidNonce (nextCandidate state).1) :
    ∃ fuel t, Advances boundary fuel s t ∧
      ReturnState initial t orderAddress (nextCandidate state).1 (nextState state) := by
  obtain ⟨decodeFuel, u, decodeRun, decoded⟩ := Tail.decode pre input
  obtain ⟨compareFuel, v, compareRun, compared, branch⟩ := Tail.compare pre decoded
  have rip : v.RIP = 0x1076e5 := by simpa only [ite_eq_left valid] using branch
  obtain ⟨finishFuel, t, finishRun, result⟩ := Tail.finish pre compared rip
  exact ⟨decodeFuel + compareFuel + finishFuel, t,
    (decodeRun.trans compareRun).trans finishRun, result⟩

theorem tail_reject [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state)
    (invalid : ¬ ValidNonce (nextCandidate state).1) :
    ∃ fuel t, Advances boundary fuel s t ∧ Loop initial t orderAddress (nextState state) := by
  obtain ⟨decodeFuel, u, decodeRun, decoded⟩ := Tail.decode pre input
  obtain ⟨compareFuel, v, compareRun, compared, branch⟩ := Tail.compare pre decoded
  have rip : v.RIP = 0x1076c3 := by simpa only [ite_eq_right invalid] using branch
  obtain ⟨t, retryRun, result⟩ := Tail.retry pre compared.toContext rip
  exact ⟨decodeFuel + compareFuel + 5, t, (decodeRun.trans compareRun).trans retryRun, result⟩

end P256.Proofs.Nonce.Fill
