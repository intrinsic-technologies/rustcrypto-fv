import P256.Proofs.Common.Instructions.CrossPageStore.Store
import X86Proofs.Program.Compose

set_option autoImplicit false

open X86 X86.Machine X86.UserProcess X86Proofs

open X86Proofs

namespace P256.Proofs.Common.Instructions.CrossPageStore

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
    exact hw.tables.sub (by omega) (by omega)

theorem Writable.toMemWritable {s : RamState} {a : BitVec 64} {len : Nat}
    (hw : Writable s a len) (_ha : a.toNat % 8 = 0) (_hlen : len ≤ 8) :
    MemWritable s a len := by
  exact ⟨hw.low, hw.mem, hw.tables⟩

end P256.Proofs.Common.Instructions.CrossPageStore

namespace P256.Proofs.Common.Instructions

theorem RangeApart.add_left {a p : BitVec 64} {n len codeLen : Nat}
    (h : RangeApart a n p codeLen) (offset : Nat) (hsub : offset + len ≤ n) :
    RangeApart (a + BitVec.ofNat 64 offset) len p codeLen := by
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h (offset + i) (by omega) j hj

end P256.Proofs.Common.Instructions
