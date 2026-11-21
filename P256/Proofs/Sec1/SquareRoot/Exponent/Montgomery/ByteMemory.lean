import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem writable_slice {s : RamState} {base : BitVec 64} {size offset len : Nat}
    (h : MemWritable s base size) (hb : offset+len ≤ size) :
    MemWritable s (base+BitVec.ofNat 64 offset) len := by
  have ha : (base+BitVec.ofNat 64 offset).toNat = base.toNat+offset := by
    have := h.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    have := h.low
    omega
  · intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h.mem (offset+i) (by omega)
  · rw [ha]
    rcases h.tables with hl | hr <;> omega

theorem scratch_byte_writable {s : RamState} (h : Reduction.MemoryPre s)
    (offset : Nat) (ho : offset < 112) :
    MemWritable s (stackPtr s+BitVec.ofNat 64 offset) 1 := by
  have hb : offset/8*8+8 ≤ 112 := by omega
  have hw := h.scratch (offset/8*8) 8 hb (by omega) (by decide)
  have hs := writable_slice (offset := offset%8) (len := 1) hw (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show offset/8*8+offset%8 = offset by omega] at hs
  exact hs

end P256.Proofs.Sec1.SquareRoot.Montgomery
