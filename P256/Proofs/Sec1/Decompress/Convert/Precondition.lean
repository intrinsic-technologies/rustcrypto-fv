import P256.Proofs.Sec1.Decompress.Convert.Interface
import P256.Proofs.Sec1.Decompress.Convert.Constants
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Convert

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem Pre.montgomery [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) : SquareRoot.MontgomeryPre s boundary 0x108f70 := by
  have rightRegion : registerRegion s .rdx 32 = MemoryRegion.mk (0x202dc8#64).toNat 32 := by
    simp only [registerRegion, pre.right, BitVec.ofNat_eq_ofNat]
  have modulusRegion : registerRegion s .rcx 32 = MemoryRegion.mk (0x202d88#64).toNat 32 := by
    simp only [registerRegion, pre.modulus, BitVec.ofNat_eq_ofNat]
  refine {
    toCalleePre := pre.toCalleePre
    rightBounded := rightRegion.symm ▸ constant_region_bounded (.inr rfl)
    rightAllocated := rightRegion.symm ▸ constant_region_allocated pre.loaded (.inr rfl)
    rightOutput := rightRegion.symm ▸ constant_region_disjoint (.inr rfl) (pre.avoids _ (by simp))
    rightStack := rightRegion.symm ▸ constant_region_disjoint (.inr rfl) (pre.avoids _ (by simp))
    modulusBounded := modulusRegion.symm ▸ constant_region_bounded (.inl rfl)
    modulusAllocated := modulusRegion.symm ▸ constant_region_allocated pre.loaded (.inl rfl)
    modulusOutput := modulusRegion.symm ▸ constant_region_disjoint (.inl rfl) (pre.avoids _ (by simp))
    modulusStack := modulusRegion.symm ▸ constant_region_disjoint (.inl rfl) (pre.avoids _ (by simp))
    modulus := ?_
    inverse := pre.inverse }
  rw [pre.modulus]
  exact modulus_at pre.loaded

end P256.Proofs.Sec1.Decompress.Convert
