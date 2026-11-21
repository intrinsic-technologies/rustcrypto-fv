import P256.Proofs.Field.Montgomery.Arithmetic
import P256.Proofs.Field.Interface
import P256.Proofs.Program.Entry

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Negate

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86Proofs
open Field

theorem zero_byte {i : Nat} (hi : i < 32) :
    Extracted.programSections.fetchByte (0x202620 + BitVec.ofNat 64 i) = some 0 := by
  have bytes : ∀ j : Fin 32,
      Extracted.programSections.fetchByte (0x202620 + BitVec.ofNat 64 j.val) = some 0 := by
    decide +kernel
  exact bytes ⟨i,hi⟩

theorem zero_at [Bindings] {s : RamState} (loaded : ProgramLoaded s) :
    MontgomeryAt s 0x202620 0 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i hi
  simpa using loaded _ _ (zero_byte hi)

theorem zero_allocated [Bindings] {s : RamState} (loaded : ProgramLoaded s) :
    (⟨0x202620,32⟩ : MemoryRegion).Allocated s.external := by
  intro address ha
  have bounds : 0x202620 ≤ address.toNat ∧ address.toNat < 0x202620+32 := ha
  have eq : 0x202620 + BitVec.ofNat 64 (address.toNat - 0x202620) = address := by
    rw [show (0x202620 : BitVec 64) = BitVec.ofNat 64 0x202620 from rfl,
      ←BitVec.ofNat_add, Nat.add_sub_of_le bounds.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact ⟨0, loaded _ _ (eq ▸ zero_byte (by omega))⟩

theorem zero_disjoint {region : MemoryRegion}
    (avoids : region.Avoids (fun a => InProgram a ∨ InPageTables a)) :
    (⟨0x202620,32⟩ : MemoryRegion).Disjoint region := by
  intro address ha hb
  have bounds : 0x202620 ≤ address ∧ address < 0x202620+32 := ha
  have eq : 0x202620 + BitVec.ofNat 64 (address - 0x202620) = BitVec.ofNat 64 address := by
    rw [show (0x202620 : BitVec 64) = BitVec.ofNat 64 0x202620 from rfl,
      ←BitVec.ofNat_add, Nat.add_sub_of_le bounds.1]
  apply avoids (BitVec.ofNat 64 address) (by simpa [Nat.mod_eq_of_lt (show address<2^64 by omega)] using hb)
  exact .inl ⟨0, eq ▸ zero_byte (by omega)⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup.Negate
