import ChaCha20Poly1305.Proofs.Decrypt.TailKernel
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part4

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

set_option maxRecDepth 8000
set_option maxHeartbeats 600000
set_option pp.maxSteps 100
theorem storeStep (x : Input) : (layout x).BlockSimulation fnCode .store := by
  by_cases ht : (rem64 x.n).toNat < 4
  all_goals refine_one [program,ht]
  all_goals exfalso
  all_goals
    have small : (rem64 x.n).toNat < 2^32 := by
      unfold rem64
      rw [BitVec.toNat_setWidth_of_le (by decide)]
      exact BitVec.isLt _
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt small] at hc
    contradiction

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
