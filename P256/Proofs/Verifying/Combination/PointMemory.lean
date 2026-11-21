import P256.Proofs.Verifying.Combination.Loop.MultiMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem Memory.of_frame [Bindings] {s t w : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (state : Memory s t tables digits p q u v) (pre : MultiPre s boundary tables digits)
    (frame : FrameState s w 96 1432 408) : Memory s w tables digits p q u v := by
  have tableBytes : ∀ i < 1536,
      w.external[tables + BitVec.ofNat 64 i]? = t.external[tables + BitVec.ofNat 64 i]? := by
    intro i hi
    have apart : ∀ region ∈ #v[registerRegion s .rdi 96, Stack.region s 1432],
        (tablesRegion tables).Disjoint region := by
      intro region hr
      have h : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1432 := by simpa using hr
      rcases h with rfl | rfl
      · exact pre.tablesOutput
      · exact pre.tablesStack
    have contained := memoryRegion_contains_add pre.tablesBounded
      (Nat.le_refl _) (Nat.le_refl _) hi
    exact (frame_read frame.frame apart contained).trans
      (frame_read state.frame apart contained).symm
  have digitBytes : ∀ i < 544,
      w.external[digits + BitVec.ofNat 64 i]? = t.external[digits + BitVec.ofNat 64 i]? := by
    intro i hi
    have apart : ∀ region ∈ #v[registerRegion s .rdi 96, Stack.region s 1432],
        (digitsRegion digits).Disjoint region := by
      intro region hr
      have h : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1432 := by simpa using hr
      rcases h with rfl | rfl
      · exact pre.digitsOutput
      · exact pre.digitsStack
    have contained := memoryRegion_contains_add pre.digitsBounded
      (Nat.le_refl _) (Nat.le_refl _) hi
    exact (frame_read frame.frame apart contained).trans
      (frame_read state.frame apart contained).symm
  refine ⟨frame, state.leftTable.of_copy (fun i hi => tableBytes i (by omega)), ?_,
    state.leftDigits.of_copy (fun i hi => digitBytes i (by omega)), ?_⟩
  · apply state.rightTable.of_copy
    intro i hi
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using tableBytes (768+i) (by omega)
  · apply state.rightDigits.of_copy
    intro i hi
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using digitBytes (272+i) (by omega)

end P256.Proofs.Verifying.Combination.Loop.Multi
