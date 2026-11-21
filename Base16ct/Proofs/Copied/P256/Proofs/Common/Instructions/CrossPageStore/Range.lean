import Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore.Store
import X86Proofs.Program.Compose

set_option autoImplicit false

open X86 X86.Machine X86.UserProcess X86Proofs

open X86Proofs

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore

theorem Writable.add {s : RamState} {a : BitVec 64} {n len : Nat}
    (hw : Writable s a n) (offset : Nat) (hsub : offset + len ≤ n) :
    Writable s (a + BitVec.ofNat 64 offset) len := by
  have ha : (a + BitVec.ofNat 64 offset).toNat = a.toNat + offset := by
    have hl := hw.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [ha]
    have := hw.low
    omega
  · intro i hi
    have hm := hw.mem (offset + i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hm
  · rw [ha]
    rcases hw.tables with h | h <;> omega

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions
