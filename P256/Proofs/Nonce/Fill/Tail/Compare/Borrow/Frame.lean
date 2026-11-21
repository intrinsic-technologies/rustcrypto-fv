import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.Interface
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Borrow

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar

def blockFrame (s : RamState) : List Component :=
  [.reg 1, .reg 2, .reg 6, .reg 7, .mem (stackPtr s + 8) 8, .flags, .rip]

theorem after_block [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original) (input : Compared initial s orderAddress state)
    (ready : ReadyToStep t) (agrees : AgreesExcept (blockFrame s) s t) :
    Compared initial t orderAddress state := by
  apply after_stack pre input ready agrees (offsets := [8])
  · intro c member a cover
    simp only [blockFrame, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i, hi, rfl⟩ := cover
    exact ⟨8, by simp, i, hi, by rw [input.rsp]; rfl⟩
  · intro off member
    have he : off = 8 := by simpa using member
    subst off
    decide
  all_goals simp [blockFrame]

theorem left_eq [Bindings] {initial s t : RamState} {orderAddress : BitVec 64} {state : Nonce.State}
    (a : Compared initial s orderAddress state) (b : Compared initial t orderAddress state)
    (j : Nat) (hj : j < 4) :
    memLoad t.external (stackPtr t + BitVec.ofNat 64 (72+8*j)) 64 =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 (72+8*j)) 64 := by
  rw [a.rsp, b.rsp, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact (b.integer.memLoad_limb j hj).trans (a.integer.memLoad_limb j hj).symm

theorem order_eq [Bindings] {initial s : RamState} {orderAddress : BitVec 64} {state : Nonce.State}
    (input : Compared initial s orderAddress state) (j : Nat) (hj : j < 4) :
    memLoad s.external (s.regValue .r15 + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (Operations.domain.n / 2^(64*j)) := by
  rw [input.r15]
  exact input.generator.2.1.memLoad_limb j hj

end P256.Proofs.Nonce.Fill.Tail.Compare.Borrow
