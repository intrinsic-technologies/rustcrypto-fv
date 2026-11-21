import P256.Proofs.Sec1.Interface
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem identity_data : ∀ i : Fin 72,
    Extracted.programSections.fetchByte (0x202df8 + BitVec.ofNat 64 i.val) =
      some (if i.val = 64 then 1 else 0) := by decide +kernel

theorem identity_at {s : RamState} (loaded : ProgramLoaded s) :
    AffineAt s 0x202df8 .infinity := by
  have zero (offset : Nat) (ho : offset = 0 ∨ offset = 32) :
      Field.MontgomeryAt s (0x202df8 + BitVec.ofNat 64 offset) 0 := by
    refine ⟨by decide, by decide, ?_⟩
    intro i hi
    have bound : offset + i < 64 := by rcases ho with rfl | rfl <;> omega
    have bytes := loaded _ _ (identity_data ⟨offset+i, by omega⟩)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show offset+i ≠ 64 by omega,
      ↓reduceIte, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, show UInt8.ofNat 0 = 0 from rfl] using bytes
  exact ⟨by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using zero 0 (.inl rfl),
    zero 32 (.inr rfl), loaded _ _ (identity_data ⟨64, by decide⟩)⟩

theorem identity_byte_inProgram {i : Nat} (hi : i < 72) :
    InProgram (0x202df8 + BitVec.ofNat 64 i) :=
  ⟨_, identity_data ⟨i, hi⟩⟩

theorem identity_readable {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x202df8 72 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  rw [loaded _ _ (identity_data ⟨i, hi⟩)]
  rfl

end P256.Proofs.Sec1.Affine
