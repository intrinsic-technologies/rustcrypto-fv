import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101ce0

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

private theorem carryWord (a b : BitVec 32) :
    BitVec.ofNat 64 (addSpec a b).2.CF.toNat = (if a+b<a then (1 : BitVec 64) else 0) := by
  change BitVec.ofNat 64 (decide ((a+b).toNat ≠ a.toNat+b.toNat)).toNat = _
  have hab : (a+b).toNat ≠ a.toNat+b.toNat ↔ a+b<a := by
    change (a.toNat + b.toNat) % 2^32 ≠ _ ↔ (a.toNat+b.toNat) % 2^32 < _
    have := a.isLt; have := b.isLt; omega
  by_cases hc : a+b<a
  · rw [ite_eq_left hc, decide_eq_true (hab.mpr hc)]; rfl
  · rw [ite_eq_right hc, decide_eq_false ((not_congr hab).mpr hc)]; rfl

theorem step4 (x : Input) :
    (Layout.withFrame Fn101ce0.active Fn101ce0.doneAt (core x)).BlockSimulation fnCode .s4 := by
  x86_refine [program, v101dec, v101df5, v101dfb, v101dfe, v101e02, v101e05, v101e0a, v101e0e]
  all_goals simp only [carryWord]

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
