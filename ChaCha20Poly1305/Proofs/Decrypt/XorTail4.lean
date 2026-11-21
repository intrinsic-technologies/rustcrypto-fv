import ChaCha20Poly1305.Proofs.Decrypt.XorNorm
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part4

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 8000
set_option maxHeartbeats 1800000
set_option pp.maxSteps 120
theorem tail4Step (x : Input) (exitLoop : Bool) (h : done .tail4 x ↔ exitLoop = true) :
    (layout .tail4 x exitLoop).BlockSimulation fnCode .start := by
  cases exitLoop <;> simp [done,bytes] at h
  all_goals refine_one [program,begins,ends,bytes,setWidth_mergeGPR8,mov3,mov64,add3sub3,add3sub2,add3sub1]
  all_goals try assumption
  all_goals simp (discharger := bv_omega) only [
    BitVec.add_assoc] at *
  all_goals simp_all
  all_goals first
    | (apply Eq.trans _ atom24; congr 1 <;> bv_omega)
    | (apply Eq.trans _ atom25; congr 1 <;> bv_omega)
    | (apply Eq.trans _ atom26; congr 1 <;> bv_omega)
    | (apply Eq.trans _ atom27; congr 1 <;> bv_omega)

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
