import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem work_contains_frame_offset [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    {k i : Nat} (hk : k + i < 152) :
    (workRegion s).Contains (stackPtr t + BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat := by
  rw [state.rsp]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hs := P256.Proofs.Program.stack_bounds pre.stack
  have sp : (stackPtr s - 168).toNat = (stackPtr s).toNat - 168 :=
    P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  rw [toNat_add_ofNat _ _ (by rw [sp]; omega), sp]
  change (stackPtr s).toNat - 880 ≤ _ ∧ _ < (stackPtr s).toNat - 880 + 864
  constructor <;> omega

def copyComponents (t : RamState) (destination : Nat) : List Component :=
  [.reg 0, .reg 1,
    .mem (stackPtr t + BitVec.ofNat 64 destination) 8,
    .mem (stackPtr t + BitVec.ofNat 64 (destination + 8)) 8,
    .mem (stackPtr t + BitVec.ofNat 64 (destination + 16)) 8,
    .mem (stackPtr t + BitVec.ofNat 64 (destination + 24)) 8, .rip]

theorem copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {destination : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (hdest : destination + 32 ≤ 152)
    (agrees : AgreesExcept (copyComponents t destination) t u) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready agrees ?_ ?_,
    (agrees.read (r := 4) (n := 64) (by simp [copyComponents])).trans state.rsp⟩
  · apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨workRegion s, by simp, work_contains_frame_offset pre state (by omega)⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [copyComponents]

theorem copy_byte {t u : RamState} {destination offset : Nat}
    (hdest : destination + 32 ≤ 152) (hoff : offset < 152)
    (sep : offset + 1 ≤ destination ∨ destination + 32 ≤ offset)
    (agrees : AgreesExcept (copyComponents t destination) t u) :
    u.external[stackPtr t + BitVec.ofNat 64 offset]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset]? := by
  apply agrees.byte
  intro c hc hcov
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  have apart (d : Nat) (hd : destination ≤ d ∧ d + 8 ≤ destination + 32) :
      ¬ Component.Covers (.mem (stackPtr t + BitVec.ofNat 64 d) 8)
        (stackPtr t + BitVec.ofNat 64 offset) := by
    rintro ⟨i,hi,he⟩
    have h := RangeApart.offsets (stackPtr t) (a := d) (b := offset)
      (len := 8) (count := 1) (by omega) (by omega) (by omega)
    apply h i hi 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
  all_goals exact apart _ (by omega) hcov

end P256.Proofs.Field.Inverse
