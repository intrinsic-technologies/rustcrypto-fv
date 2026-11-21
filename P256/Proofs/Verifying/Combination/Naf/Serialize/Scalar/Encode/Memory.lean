import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Entry
import P256.Proofs.Verifying.Combination.Naf.Iterator.InitializeStore
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field

 theorem Memory.after_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (ready : ReadyToStep u) {offset : Nat}
    (bound : offset + 24 ≤ 360)
    (agrees : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 offset) 8, .rip] t u) :
    Memory s u cursor point := by
  have work : WritesWithin [.mem (stackPtr t + BitVec.ofNat 64 offset) 8, .rip]
      #v[registerRegion s .rdi 272, workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨workRegion s, by simp, ?_⟩
      rw [stack_address state.rsp (by omega)] at ha
      exact work_contains pre (by omega) (by omega) ha
    · exact ha.elim
  refine ⟨after pre state.toFrameState ready agrees work (by simp) (by simp)
    (by simp) (by simp) (by simp), ?_⟩
  have memory : MemoryWriteFrame t u #v[registerRegion s .rdi 272, Stack.region s 536] := by
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨Stack.region s 536, by simp, ?_⟩
      rw [stack_address state.rsp (by omega)] at ha
      exact P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ha
    · exact ha.elim
  exact (cursor_read_of_frame pre memory).trans state.cursorValue

theorem scalar_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (state : FrameState s t cursor) {offset len : Nat} (bound : offset + len ≤ 128) :
    MemReadable t (point + BitVec.ofNat 64 offset) len := by
  have low : point.toNat + 128 < 2^32 := pre.pointBounded
  apply readable_of_grow (s := s) _ state.allocated
  apply memoryRegion_memReadable pre.pointBounded pre.pointAllocated
  · change point.toNat ≤ _
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · change _ + len ≤ point.toNat + 128
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
