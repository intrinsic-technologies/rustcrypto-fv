import P256.Proofs.Projective.Multiply.Machine.Basepoint.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Field.Montgomery.Arithmetic
import P256.Proofs.Program.Entry

set_option autoImplicit false

open P256.Proofs.Program (CalleePre stack_region_end)
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem generator_at [Bindings] {s : RamState} (loaded : ProgramLoaded s) :
    ProjectiveAt s 0x202ac8 basePoint := by
  have bytes (offset value : Nat)
      (hbytes : ∀ i : Fin 32,
        Extracted.programSections.fetchByte (BitVec.ofNat 64 (0x202ac8 + offset) +
          BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat ((value * 2^256 % P256.Spec.Operations.domain.p) /
          256^i.val % 256)))
      (hbound : value < P256.Spec.Operations.domain.p) :
      MontgomeryAt s (BitVec.ofNat 64 (0x202ac8 + offset)) value := by
    refine ⟨hbound, Nat.lt_trans (Nat.mod_lt _ Field.Montgomery.p_pos) Field.Montgomery.p_lt_radix, ?_⟩
    intro i hi
    exact loaded _ _ (hbytes ⟨i, hi⟩)
  exact ⟨bytes 0 basePoint.x (by decide +kernel) (by decide +kernel),
    bytes 32 basePoint.y (by decide +kernel) (by decide +kernel),
    bytes 64 basePoint.z (by decide +kernel) (by decide +kernel)⟩

theorem generator_byte_inProgram {i : Nat} (hi : i < 96) :
    InProgram (0x202ac8 + BitVec.ofNat 64 i) := by
  have bytes : ∀ j : Fin 96,
      (Extracted.programSections.fetchByte (0x202ac8 + BitVec.ofNat 64 j.val)).isSome := by
    decide +kernel
  exact Option.isSome_iff_exists.mp (bytes ⟨i, hi⟩)

theorem generator_readable [Bindings] {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x202ac8 96 := by
  refine ⟨by decide +kernel, ?_⟩
  intro i hi
  obtain ⟨b, hb⟩ := generator_byte_inProgram hi
  rw [loaded _ _ hb]
  rfl

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

end P256.Proofs.Projective.Multiply.Machine.Basepoint
