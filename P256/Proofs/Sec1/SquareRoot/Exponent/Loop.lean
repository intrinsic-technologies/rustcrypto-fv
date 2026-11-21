import P256.Proofs.Sec1.SquareRoot.Exponent.Iteration
import P256.Proofs.Sec1.SquareRoot.Exponent.NextWord

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_loop [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x)
    (hp : ExponentLoopState s t x n) (hn : 0 < n) (hmax : n ≤ 64) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFinishState s u x := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    obtain ⟨v, iterationFuel, hav, hpv, hiv, haccv⟩ := exponent_iteration ctx hp (by omega)
    by_cases hz : n = 0
    · subst n
      have hacc : MontgomeryAt v (exponentFrameBase s + 0x30)
          (x ^ sqrtExponent % P256.Spec.Operations.domain.p) := by
        simpa only [Nat.pow_zero, Nat.div_one] using haccv
      obtain ⟨u, finishFuel, hau, hfinish⟩ := hpv.finish ctx hiv hacc
      exact ⟨u, iterationFuel + finishFuel, hav.trans hau, hfinish⟩
    · have hcontinue : ∃ w fuel, Advances boundary fuel v w ∧ ExponentLoopState s w x n := by
        by_cases hword : n % 16 = 0
        · exact hpv.next_word ctx (by omega) (by omega) hword hiv haccv
        · exact hpv.continue_window ctx hword hiv haccv
      obtain ⟨w, controlFuel, haw, hpw⟩ := hcontinue
      obtain ⟨u, loopFuel, hau, hfinish⟩ := ih hpw (by omega) (by omega)
      exact ⟨u, iterationFuel + controlFuel + loopFuel, (hav.trans haw).trans hau, hfinish⟩

end P256.Proofs.Sec1.SquareRoot
