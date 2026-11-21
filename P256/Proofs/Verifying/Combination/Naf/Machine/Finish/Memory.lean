import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Verifying.Combination.Naf.Machine.LoopState
import P256.Proofs.Verifying.Combination.Naf.Machine.Frame
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Instructions.StoreByte

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem digits_of_external_eq {s t : RamState} {address : BitVec 64} {ds : List Int}
    (output : DigitsAt s address ds) (memory : t.external = s.external) : DigitsAt t address ds := by
  intro i hi
  rw [memory]
  exact output i hi

theorem digits_append_one {s t : RamState} {address : BitVec 64} {ds : List Int}
    (output : DigitsAt s address ds) (bound : ds.length ≤ 256)
    (agrees : AgreesExcept [.mem (address + BitVec.ofNat 64 ds.length) 1, .rip] s t)
    (last : memLoad t.external (address + BitVec.ofNat 64 ds.length) 8 = 1) :
    DigitsAt t address (ds ++ [1]) := by
  intro i hi
  by_cases eq : i = ds.length
  · subst i
    rw [last, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · have read : memLoad t.external (address + BitVec.ofNat 64 i) 8 =
        memLoad s.external (address + BitVec.ofNat 64 i) 8 := by
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
      intro j hj c hc cover
      have j0 : j = 0 := by omega
      subst j
      simp only [BitVec.add_zero] at cover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨k, hk, he⟩ := cover
        have k0 : k = 0 := by omega
        subst k
        simp only [BitVec.add_zero] at he
        have h := congrArg BitVec.toNat ((BitVec.add_right_inj address).mp he)
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
          Nat.mod_eq_of_lt (by omega : ds.length < 2^64)] at h
        exact eq h
      · exact cover.elim
    rw [read, output i hi]
    by_cases small : i < ds.length
    · rw [List.getElem?_append_left small]
    · have large : ds.length < i := by omega
      have oldNone : ds[i]? = none := List.getElem?_eq_none (by omega)
      have newNone : (ds ++ [1])[i]? = none := List.getElem?_eq_none (l := ds ++ [1]) (i := i) (by simp only [List.length_append, List.length_singleton]; omega)
      rw [oldNone, newNone]

theorem output_byte_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) (state : FrameState s t)
    {i : Nat} (hi : i < 257) : MemWritable t (s.regValue .rdi + BitVec.ofNat 64 i) 1 := by
  have readable : MemReadable t (s.regValue .rdi + BitVec.ofNat 64 i) 1 :=
    P256.Proofs.Program.readable_of_grow
      (Iterator.readable_subrange (memoryRegion_memReadable pre.outputBounded pre.outputAllocated
        (Nat.le_refl _) (Nat.le_refl _)) i 1 (by change i+1 ≤ 257; omega)) state.allocated
  apply MemWritable.of_not_reserved (by decide) readable.low readable.mem
  intro j hj reserved
  apply pre.avoids (registerRegion s .rdi 257) (by simp) _ ?_ (.inr reserved)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change i+j < 257; omega)

theorem output_byte_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) {i : Nat} (hi : i < 257) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 i) 1 0x10f4ed 5 := by
  intro j hj k hk he
  apply pre.avoids (registerRegion s .rdi 257) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 i + BitVec.ofNat 64 j) ?_ (.inl ?_)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change i+j < 257; omega)
  · rw [he]
    have h := inProgram_of_textOffset (0xf4ed+k) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h

theorem FrameState.after_output_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10f350 0 257 168) (state : FrameState s t)
    {i : Nat} (hi : i < 257) (ready : ReadyToStep u)
    (agrees : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 i) 1, .rip] t u) :
    FrameState s u := by
  apply after pre state ready agrees _ (by simp)
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, rfl⟩ := ha
    refine ⟨registerRegion s .rdi 257, by simp, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change i+j < 257; omega)
  · exact ha.elim

end P256.Proofs.Verifying.Combination.Naf.Machine
