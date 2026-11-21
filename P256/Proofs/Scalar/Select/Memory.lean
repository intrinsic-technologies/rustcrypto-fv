import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.Copy.Return
import P256.Proofs.Common.Instructions.CrossPageStore.Range
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Scalar.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem output_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113260 32 32 16) {i : Nat} (hi : i < 32) :
    (registerRegion s .rdi 32).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary 0x113260 32 32 16)
    (g : AgreesExcept cs s t) (i : Nat) (hi : i+8 ≤ 32) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi + BitVec.ofNat 64 i) 8 :=
  (ScalarFrame.output_writable pre (by decide) g.grow).add i hi

theorem output_code_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113260 32 32 16) (i : Nat) (hi : i+8 ≤ 32)
    (offset len : Nat) (hc : offset+len ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len :=
  P256.Proofs.Common.Instructions.RangeApart.add_left (ScalarFrame.output_code pre hc) i hi

def clobbers (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackPtr s - 1) 1, .mem (s.regValue .rdi) 32]

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem writes_within (pre : CalleePre s boundary 0x113260 32 32 16) :
    WritesWithin (clobbers s) #v[registerRegion s .rdi 32, Stack.region s 16] := by
  intro c hc address cover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · exact ⟨Stack.region s 16, by simp,
      ScalarFrame.stack_contains pre (offset := 1) (by decide) (by decide) cover⟩
  · obtain ⟨i, hi, rfl⟩ := cover
    exact ⟨registerRegion s .rdi 32, by simp, output_contains pre hi⟩

theorem loaded_of_agrees (pre : CalleePre s boundary 0x113260 32 32 16)
    (agrees : AgreesExcept (clobbers s) s t) : ProgramLoaded t := by
  have memory := agrees.memoryWriteFrame (writes_within pre)
  intro a b fetch
  rw [memory a]
  · exact pre.loaded a b fetch
  · intro region hr ha
    exact pre.avoids region (by simpa using hr) a ha (.inl ⟨b, fetch⟩)

theorem return_address (pre : CalleePre s boundary 0x113260 32 32 16)
    (agrees : AgreesExcept (clobbers s) s t) :
    memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  apply agrees.byte
  intro c hc cover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · obtain ⟨j, hj, eq⟩ := cover
    apply OffsetsApart.ne (c₁ := -1) (c₂ := 0#64) (len₁ := 1) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_zero] using eq.symm
  · obtain ⟨j, hj, eq⟩ := cover
    have disjoint := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
    apply disjoint _ (output_contains pre hj)
    rw [← eq]
    apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
    · exact Nat.sub_le _ _
    · rw [stack_region_end]
      exact Nat.le_refl _

theorem stack_code_apart (pre : CalleePre s boundary 0x113260 32 32 16)
    (offset len : Nat) (hc : offset + len ≤ 118431) :
    RangeApart (stackPtr s - 1) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj eq
  apply pre.avoids (Stack.region s 16) (by simp) _
    (ScalarFrame.stack_contains pre (offset := 1) (by decide) (by decide)
      ⟨i, hi, rfl⟩)
  left
  change InProgram (stackPtr s - 1 + BitVec.ofNat 64 i)
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

end P256.Proofs.Scalar.Select
