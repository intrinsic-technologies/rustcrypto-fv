import P256.Proofs.Field.Inverse.Tail.CopyState

set_option autoImplicit false


open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def zeroComponents (t : RamState) (tag : Nat) : List Component :=
  [.mem (stackPtr t + BitVec.ofNat 64 tag) 1,
    .mem (stackPtr t + 0) 8, .mem (stackPtr t + 8) 8,
    .mem (stackPtr t + 16) 8, .mem (stackPtr t + 24) 8, .rip]

theorem zero_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {tag : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (htag : tag < 152)
    (agrees : AgreesExcept (zeroComponents t tag) t u) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready agrees ?_ ?_,
    (agrees.read (r := 4) (n := 64) (by simp [zeroComponents])).trans state.rsp⟩
  · apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [zeroComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
    · exact ⟨workRegion s, by simp, work_contains_frame_offset pre state (k := tag) (by omega)⟩
    · exact ⟨workRegion s, by simp, work_contains_frame_offset pre state (k := 0) (by omega)⟩
    · exact ⟨workRegion s, by simp, work_contains_frame_offset pre state (k := 8) (by omega)⟩
    · exact ⟨workRegion s, by simp, work_contains_frame_offset pre state (k := 16) (by omega)⟩
    · exact ⟨workRegion s, by simp, work_contains_frame_offset pre state (k := 24) (by omega)⟩
  · intro r hr
    simp [zeroComponents]

theorem zero_candidate {t u : RamState} {source beta : Nat}
    (hsource : 32 ≤ source ∧ source + 33 ≤ 152)
    (agrees : AgreesExcept (zeroComponents t (source + 32)) t u)
    (input : Nat256At t (stackPtr t + BitVec.ofNat 64 source) beta) :
    Nat256At u (stackPtr t + BitVec.ofNat 64 source) beta := by
  apply nat256At_copy input
  intro i hi
  apply agrees.byte
  intro c hc hcov
  simp only [zeroComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  have apart (offset len : Nat) (hbound : offset + len ≤ 152)
      (sep : offset + len ≤ source ∨ source + 32 ≤ offset) :
      ¬ Component.Covers (.mem (stackPtr t + BitVec.ofNat 64 offset) len)
        (stackPtr t + BitVec.ofNat 64 source + BitVec.ofNat 64 i) := by
    rintro ⟨j,hj,he⟩
    exact RangeApart.offsets (stackPtr t) (a := offset) (b := source)
      (by omega) (by omega) sep j hj i hi he.symm
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
  · exact apart (source + 32) 1 (by omega) (.inr (by omega)) hcov
  · exact apart 0 8 (by decide) (.inl (by omega)) hcov
  · exact apart 8 8 (by decide) (.inl (by omega)) hcov
  · exact apart 16 8 (by decide) (.inl (by omega)) hcov
  · exact apart 24 8 (by decide) (.inl (by omega)) hcov

end P256.Proofs.Field.Inverse
