import P256.Proofs.Projective.Add.Copy.Point
set_option autoImplicit false


namespace P256.Proofs.Projective.Add.Copy

open P256.Proofs.Program.ScalarFrame.Copy32
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem preserves {t u : RamState} {destination source : BitVec 64} {x : Nat}
    (agrees : AgreesExcept (components destination) t u)
    (apart : RangeApart destination 32 source 32) (input : MontgomeryAt t source x) :
    MontgomeryAt u source x := by
  apply input.of_bytes_eq
  intro i hi
  apply agrees.byte
  intro c hc ha
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  exact apart j hj i hi he.symm

theorem stack_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {destination : BitVec 64} {offset : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (agrees : AgreesExcept (components destination) t u)
    (dst : destination = stackPtr s - BitVec.ofNat 64 offset)
    (bound : offset ≤ 920) (len : 32 ≤ offset) :
    MemoryWriteFrame t u #v[Stack.region s 920] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  rw [dst] at ha
  exact ⟨Stack.region s 920, by simp,
    stack_contains pre bound (by omega) ha⟩

theorem stack_preserves {s t u : RamState} {destination : BitVec 64}
    {outputOffset inputOffset x : Nat}
    (agrees : AgreesExcept (components destination) t u)
    (dst : destination = stackPtr s - BitVec.ofNat 64 outputOffset)
    (apart : OffsetsApart (-BitVec.ofNat 64 outputOffset) 32 (-BitVec.ofNat 64 inputOffset) 32)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 inputOffset) x) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 inputOffset) x := by
  apply preserves agrees _ input
  rw [dst]
  intro i hi j hj he
  exact apart.ne (stackPtr s) hi hj (by decide) (by simpa only [BitVec.sub_eq_add_neg] using he)

end P256.Proofs.Projective.Add.Copy
