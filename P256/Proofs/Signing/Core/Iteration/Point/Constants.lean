import P256.Proofs.Signing.Core.Iteration.Point.Interface
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Constants
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Projective.Multiply.Machine

theorem generator_byte_inProgram {i : Nat} (hi : i < 96) :
    InProgram (0x202ac8 + BitVec.ofNat 64 i) := by
  have bytes : ∀ j : Fin 96,
      (Extracted.programSections.fetchByte (0x202ac8 + BitVec.ofNat 64 j.val)).isSome := by
    decide +kernel
  exact Option.isSome_iff_exists.mp (bytes ⟨i,hi⟩)

theorem generator_at [Bindings] {t : RamState} (loaded : ProgramLoaded t) :
    ProjectiveAt t 0x202ac8 Basepoint.basePoint := by
  exact Basepoint.generator_at loaded

theorem generator_readable [Bindings] {t : RamState} (loaded : ProgramLoaded t) :
    MemReadable t 0x202ac8 96 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  obtain ⟨b,hb⟩ := generator_byte_inProgram hi
  rw [loaded _ _ hb]
  rfl

theorem generator_region_inProgram {a : BitVec 64}
    (ha : (MemoryRegion.mk 0x202ac8 96).Contains a.toNat) : InProgram a := by
  change 0x202ac8 ≤ a.toNat ∧ a.toNat < 0x202ac8+96 at ha
  have h := generator_byte_inProgram (i := a.toNat-0x202ac8) (by omega)
  have eq : 0x202ac8+BitVec.ofNat 64 (a.toNat-0x202ac8) = a := by
    rw [show (0x202ac8 : BitVec 64) = BitVec.ofNat 64 0x202ac8 from rfl,
      ← BitVec.ofNat_add,Nat.add_sub_of_le ha.1,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rwa [eq] at h

theorem generator_stack_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve offset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (bound : offset ≤ reserve) (length : 96 ≤ offset + 8) :
    0x202ac8 + 96 ≤ (stackPtr s - BitVec.ofNat 64 offset).toNat ∨
      (stackPtr s - BitVec.ofNat 64 offset).toNat + 96 ≤ 0x202ac8 := by
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have dest := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := offset) bound
  by_cases before : 0x202ac8 + 96 ≤ (stackPtr s - BitVec.ofNat 64 offset).toNat
  · exact .inl before
  right
  apply Nat.le_of_not_lt
  intro after
  let address := max 0x202ac8 (stackPtr s - BitVec.ofNat 64 offset).toNat
  have small : address < 2^64 := by dsimp only [address]; omega
  have natAddress : (BitVec.ofNat 64 address).toNat = address := Nat.mod_eq_of_lt small
  have program : InProgram (BitVec.ofNat 64 address) := by
    have index : address - 0x202ac8 < 96 := by dsimp only [address]; omega
    have byte := generator_byte_inProgram index
    have ha : 0x202ac8 + BitVec.ofNat 64 (address - 0x202ac8) = BitVec.ofNat 64 address := by
      rw [show (0x202ac8 : BitVec 64) = BitVec.ofNat 64 0x202ac8 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [ha] at byte
  apply pre.avoids (Stack.region s reserve) (by simp) (BitVec.ofNat 64 address) ?_ (.inl program)
  change (stackPtr s).toNat - reserve ≤ (BitVec.ofNat 64 address).toNat ∧
    (BitVec.ofNat 64 address).toNat < (Stack.region s reserve).start + (Stack.region s reserve).size
  rw [natAddress, stack_region_end]
  dsimp only [address]
  omega


end P256.Proofs.Signing.Core.Iteration.Point
