import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Program.Arena

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def arenaComponents : List Component :=
  [.reg 0, .mem 0x300000 8, .mem 0x300008 8, .mem 0x300010 8,
    .mem 0x300018 8, .mem 0x300020 8, .rip]

theorem savedMemory_words (s : RamState) :
    memLoad (SavePair.savedMemory s) (stackPtr s - 16) 64 = s.regValue .rbx ∧
    memLoad (SavePair.savedMemory s) (stackPtr s - 8) 64 = s.regValue .r14 ∧
    memLoad (SavePair.savedMemory s) (stackPtr s) 64 = (returnBoundary s).rip := by
  constructor
  · exact memLoad_memStore _ _ (by decide) (by decide) _
  constructor
  · simp only [SavePair.savedMemory, BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad (SavePair.savedMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    simp only [SavePair.savedMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

theorem arena_preserves_stack_word [Bindings] {initial s t : RamState} {routine : Routine} {inputs : List ByteArray}
    {slices : Array Input} (hcall : ValidCallWithSlices routine initial inputs slices)
    (agrees : AgreesExcept arenaComponents s t) {offset : Nat} (ho : offset ≤ routine.minStackBytes) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  have hc : (callStack routine initial).Contains
      (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat :=
    stack_component_within hcall.stackAvailable.1 ho (by omega) ⟨i, hi, rfl⟩
  have hnot {off : Nat} (hoff : off ∈ ([0,8,16,24,32] : List Nat)) :
      ¬ (Component.mem (0x300000 + BitVec.ofNat 64 off) 8).Covers
        (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
    intro hv
    obtain ⟨region, hr, hin⟩ := static_component_within hoff hv
    have hr' : region = allocatorStateRegion ∨ region = randomSourceRegion := by simpa using hr
    rcases hr' with rfl | rfl
    · exact hcall.separation.1 1 3 (by decide) _ hin hc
    · exact hcall.separation.1 2 3 (by decide) _ hin hc
  change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 = _
  have he := agrees.byte (x := stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) (by
    intro c hc
    simp only [arenaComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim
    · exact hnot (off := 0) (by simp)
    · exact hnot (off := 8) (by simp)
    · exact hnot (off := 16) (by simp)
    · exact hnot (off := 24) (by simp)
    · exact hnot (off := 32) (by simp)
    · exact False.elim)
  rw [he]
  rfl

end P256.Proofs.Program
