import ChaCha20Poly1305.Proofs.Decrypt.Stream
import ChaCha20Poly1305.Proofs.Decrypt.Refine
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part1

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option pp.maxSteps 150
theorem boundsBlock (x : Input) (hctr : x.w[12].toBitVec.toNat ≤ 1) :
    (Layout.withFrame Fn100a80.active Fn100a80.doneAt (core x)).BlockSimulation fnCode .bounds := by
  have hn := x.len
  refine_one [program]
  exfalso
  apply hc
  have wide (w : BitVec 32) : (w.setWidth 64).toNat = w.toNat := BitVec.toNat_setWidth_of_le (by decide)
  rw [wide (~~~x.w[12].toBitVec),BitVec.toNat_not]
  generalize decide ((BitVec.setWidth 64 (BitVec.setWidth 32 x.n &&& 63)).toNat < 1) = flag
  cases flag <;> simp only [Bool.toNat_false,Bool.toNat_true,BitVec.toNat_sub,BitVec.toNat_add,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceMod,
    BitVec.ofNat_eq_ofNat] <;> omega

end ChaCha20Poly1305.Proofs.Decrypt.Stream
