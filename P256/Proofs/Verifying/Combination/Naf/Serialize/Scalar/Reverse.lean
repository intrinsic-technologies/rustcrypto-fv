import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Encode
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Common

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field

theorem Memory.after_reverse [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (ready : ReadyToStep u)
    (post : P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Post t u) : Memory s u cursor point := by
  have work : WritesWithin (P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint t) #v[workRegion s] := by
    intro c hc a ha
    simp only [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨workRegion s, by simp, ?_⟩
    have address : stackPtr t + 8 = stackPtr s - 352#64 :=
      stack_address state.rsp (offset := 8) (by decide)
    rw [address] at ha
    exact work_contains pre (offset := 352) (len := 32) (by decide) (by decide) ha
  have writes : WritesWithin (P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint t) #v[registerRegion s .rdi 272, workRegion s] := by
    intro c hc a ha
    obtain ⟨region, hr, hin⟩ := work c hc a ha
    refine ⟨region, ?_, hin⟩
    have h : region = workRegion s := by simpa using hr
    simp [h]
  exact ⟨after pre state.toFrameState ready post.agrees writes
    (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint]) (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint])
    (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint]) (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint]) (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint]),
    (work_cursor_read pre (post.agrees.memoryWriteFrame work)).trans state.cursorValue⟩

theorem reversed_scalar {t u : RamState} {n : Nat}
    (bound : n < 2^256) (post : P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Post t u)
    (input : Bytes t.external (stackPtr t + 8) 32
      (fun i => UInt8.ofNat (n / 256^(31-i) % 256))) :
    Nat256At u (stackPtr u + 8) n := by
  have rsp : stackPtr u = stackPtr t := post.agrees.read (n := 64) (r := 4)
    (by simp [P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.footprint])
  rw [rsp]
  refine ⟨bound, ?_⟩
  intro i hi
  have byte := post.bytes i hi
  change u.external[stackPtr t + 8 + BitVec.ofNat 64 i]? =
    some ((t.external[stackPtr t + 8 + BitVec.ofNat 64 (31-i)]?).getD 0) at byte
  rw [input (31-i) (by omega), Option.getD_some] at byte
  simpa only [show 31-(31-i)=i by omega] using byte

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
