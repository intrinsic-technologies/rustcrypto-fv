import Hkdf.Proofs.Common.Instructions.CrossPageStore.Store
import X86Proofs.Program.Compose

set_option autoImplicit false

open X86 X86.Machine X86.UserProcess X86Proofs

open X86Proofs

namespace Hkdf.Proofs.Common.Instructions.CrossPageStore

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
    (hw : Writable s a len) : MemWritable s a len :=
  ⟨hw.low, hw.mem, hw.tables⟩

theorem stackSlot_address (sp c : BitVec 64) (lo : Nat) :
    sp - BitVec.ofNat 64 lo + BitVec.ofNat 64 (c + BitVec.ofNat 64 lo).toNat = sp + c := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm c, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem Writable.stackSlot {s : RamState} {lo hi len : Nat}
    (hw : Writable s (rspOf s - BitVec.ofNat 64 lo) (lo + hi))
    (c : BitVec 64) (hc : SlotIn c len lo hi) :
    MemWritable s (rspOf s + c) len := by
  have h := hw.add (c + BitVec.ofNat 64 lo).toNat hc
  rw [stackSlot_address] at h
  exact h.toMemWritable

end Hkdf.Proofs.Common.Instructions.CrossPageStore

namespace Hkdf.Proofs.Common.Instructions

theorem RangeApart.add_left {a p : BitVec 64} {n len codeLen : Nat}
    (h : RangeApart a n p codeLen) (offset : Nat) (hsub : offset + len ≤ n) :
    RangeApart (a + BitVec.ofNat 64 offset) len p codeLen := by
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h (offset + i) (by omega) j hj

theorem RangeApart.stackSlot {sp p : BitVec 64} {lo hi len codeLen : Nat}
    (h : RangeApart (sp - BitVec.ofNat 64 lo) (lo + hi) p codeLen)
    (c : BitVec 64) (hc : SlotIn c len lo hi) :
    RangeApart (sp + c) len p codeLen := by
  have hs := Hkdf.Proofs.Common.Instructions.RangeApart.add_left (h := h) (c + BitVec.ofNat 64 lo).toNat hc
  rw [Hkdf.Proofs.Common.Instructions.CrossPageStore.stackSlot_address] at hs
  exact hs

end Hkdf.Proofs.Common.Instructions
