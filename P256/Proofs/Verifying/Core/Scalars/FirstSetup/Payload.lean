import P256.Proofs.Verifying.Core.Scalars.FirstSetup.Run

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars.FirstSetup

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem copy128 [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {value : Nat}
    (hp : Core.Pre s boundary) (frame : Frame s t) (out : Frame s u)
    (effect : (Block.effect t).Holds t u)
    (input : Nat256At t (frameBase s + 128) value) :
    Nat256At u (frameBase s + 128) value := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, _, _, _, h5, h6, h7, h8, _, _, _, _⟩
  change memLoad u.external (rspOf t+128#64) 64 =
    memLoad t.external (rspOf t+128#64) 64 at h5
  change memLoad u.external (rspOf t+136#64) 64 =
    memLoad t.external (rspOf t+136#64) 64 at h6
  change memLoad u.external (rspOf t+144#64) 64 =
    memLoad t.external (rspOf t+144#64) 64 at h7
  change memLoad u.external (rspOf t+152#64) 64 =
    memLoad t.external (rspOf t+152#64) 64 at h8
  have sp : rspOf t = frameBase s := frame.rsp
  apply nat256_word_copy input
  · have h := stack_readable (frameOffset := 1176) hp.toCalleePre out
      (offset := 128) (len := 32) (by decide) (by decide)
    rw [out.rsp] at h
    exact h
  · intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h5
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h6
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h7
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h8

theorem copy608 [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {value : Nat}
    (hp : Core.Pre s boundary) (frame : Frame s t) (out : Frame s u)
    (effect : (Block.effect t).Holds t u)
    (input : Nat256At t (frameBase s + 128) value) :
    Nat256At u (frameBase s + 768) value := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, _, _, _, _, _, _, _, h9, h10, h11, h12⟩
  change memLoad u.external (rspOf t+768#64) 64 =
    memLoad t.external (rspOf t+128#64) 64 at h9
  change memLoad u.external (rspOf t+776#64) 64 =
    memLoad t.external (rspOf t+136#64) 64 at h10
  change memLoad u.external (rspOf t+784#64) 64 =
    memLoad t.external (rspOf t+144#64) 64 at h11
  change memLoad u.external (rspOf t+792#64) 64 =
    memLoad t.external (rspOf t+152#64) 64 at h12
  have sp : rspOf t = frameBase s := frame.rsp
  apply nat256_word_copy input
  · have h := stack_readable (frameOffset := 1176) hp.toCalleePre out
      (offset := 768) (len := 32) (by decide) (by decide)
    rw [out.rsp] at h
    exact h
  · intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h9
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h10
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h11
    · simpa only [sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h12

end P256.Proofs.Verifying.Core.Scalars.FirstSetup
