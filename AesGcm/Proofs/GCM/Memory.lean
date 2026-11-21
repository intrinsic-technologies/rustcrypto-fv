import AesGcm.Proofs.Machine.GcmContext

namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem memoryBlock_zero {mem : Ram} {base : BitVec 64}
    (h0 : memLoad mem base 64 = 0) (h8 : memLoad mem (base + 8) 64 = 0) :
    Fixslice.memoryBlock mem base = Fixslice16.fromStandard (Vector.replicate 16 0) := by
  funext j
  simp only [Fixslice.memoryBlock, Fixslice16.fromStandard, Vector.getElem_replicate]
  by_cases hj : j.val < 8
  · rw [← storedByte_memLoad (n := 64) mem base j.val (by omega), h0]
    simp [storedByte]
  · have ha : base + BitVec.ofNat 64 j.val =
        (base + 8) + BitVec.ofNat 64 (j.val - 8) := by
      change base + BitVec.ofNat 64 j.val = (base + BitVec.ofNat 64 8) + BitVec.ofNat 64 (j.val - 8)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [show 8 + (j.val - 8) = j.val by omega]
    rw [ha, ← storedByte_memLoad (n := 64) mem (base + 8) (j.val - 8) (by have := j.isLt; omega), h8]
    simp [storedByte]

end AesGcm.Proofs.Machine.GCM
