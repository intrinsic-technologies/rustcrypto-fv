import P256.Proofs.Ecdh.Initial.Prefix.Memory
import P256.Proofs.Field.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Field

theorem one_at {s : RamState} (loaded : ProgramLoaded s) : MontgomeryAt s 0x202580 1 := by
  refine ⟨by decide +kernel,
    Nat.lt_trans (Nat.mod_lt _ Field.Montgomery.p_pos) Field.Montgomery.p_lt_radix, ?_⟩
  have bytes : ∀ i : Fin 32,
      Extracted.programSections.fetchByte (0x202580+BitVec.ofNat 64 i.val) =
      some (UInt8.ofNat ((1*2^256%P256.Spec.Operations.domain.p)/256^i.val%256)) := by
    decide +kernel
  intro i hi
  exact loaded _ _ (bytes ⟨i,hi⟩)

theorem one_byte {i : Nat} (hi : i < 32) : InProgram (0x202580+BitVec.ofNat 64 i) := by
  have bytes : ∀ j : Fin 32,
      (Extracted.programSections.fetchByte (0x202580+BitVec.ofNat 64 j.val)).isSome := by
    decide +kernel
  exact Option.isSome_iff_exists.mp (bytes ⟨i,hi⟩)

theorem one_readable {s : RamState} (loaded : ProgramLoaded s) {k : Nat} (hk : k < 4) :
    MemReadable s (0x202580+BitVec.ofNat 64 (8*k)) 8 := by
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    change (2106752+(8*k)%2^64)%2^64+8 ≤ 2^32
    omega
  · intro i hi
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    obtain ⟨b,hb⟩ := one_byte (i := 8*k+i) (by omega)
    rw [loaded _ _ hb]
    rfl

end P256.Proofs.Ecdh.Initial.Prefix
