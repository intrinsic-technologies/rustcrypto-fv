import P256.Proofs.PublicPoint.Normalize.Finish.Memory
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

theorem constant_inProgram {i : Nat} (hi : i < 72) :
    InProgram (0x2024f0 + BitVec.ofNat 64 i) := by
  have h : ∀ j : Fin 72,
      (Extracted.programSections.fetchByte (0x2024f0 + BitVec.ofNat 64 j.val)).isSome := by
    decide +kernel
  exact Option.isSome_iff_exists.mp (h ⟨i, hi⟩)

theorem constant_readable {t : RamState} (loaded : ProgramLoaded t) : MemReadable t 0x2024f0 72 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  obtain ⟨b, hb⟩ := constant_inProgram hi
  rw [loaded _ b hb]
  rfl

theorem constant_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) :
    0x2024f0 + 72 ≤ (stackPtr s - 912).toNat ∨
      (stackPtr s - 912).toNat + 72 ≤ 0x2024f0 := by
  have hs := stack_bounds pre.stack
  have hn : (stackPtr s - 912).toNat = (stackPtr s).toNat - 912 :=
    stack_sub_toNat pre.stack (by decide)
  by_cases hbefore : 0x2024f0 + 72 ≤ (stackPtr s - 912).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  let a := max 0x2024f0 (stackPtr s - 912).toNat
  have ha : a < 2^64 := by dsimp only [a]; have := (stackPtr s - 912).isLt; omega
  have he : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
  have him : InProgram (BitVec.ofNat 64 a) := by
    have h := constant_inProgram (i := a - 0x2024f0) (by dsimp only [a]; omega)
    have hadd : 0x2024f0 + BitVec.ofNat 64 (a - 0x2024f0) = BitVec.ofNat 64 a := by
      rw [show (0x2024f0 : BitVec 64) = BitVec.ofNat 64 0x2024f0 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [hadd] at h
  apply pre.avoids (Stack.region s 3352) (by simp) (BitVec.ofNat 64 a) _ (.inl him)
  change (Stack.region s 3352).start ≤ _ ∧ _ <
    (Stack.region s 3352).start + (Stack.region s 3352).size
  rw [he, stack_region_end]
  change 3352 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at hs
  change (stackPtr s).toNat - 3352 ≤ a ∧ a < (stackPtr s).toNat + 8
  dsimp only [a]
  omega

theorem constant_zero {t : RamState} (loaded : ProgramLoaded t) (off : Nat) (ho : off + 32 ≤ 64) :
    MontgomeryAt t (0x2024f0 + BitVec.ofNat 64 off) 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro i hi
  have bytes : ∀ j : Fin 64,
      Extracted.programSections.fetchByte (0x2024f0 + BitVec.ofNat 64 j.val) = some 0 := by
    decide +kernel
  have h := loaded _ 0 (bytes ⟨off+i, by omega⟩)
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div]
  change t.external[(0x2024f0 + BitVec.ofNat 64 off) + BitVec.ofNat 64 i]? = some 0
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h

end P256.Proofs.PublicPoint.Normalize.Finish
