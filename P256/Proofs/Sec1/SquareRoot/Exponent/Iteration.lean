import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour
import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit
import P256.Proofs.Sec1.SquareRoot.Exponent.Window
import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_iteration [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x)
    (hp : ExponentLoopState s t x (n + 1)) (hn : n < 64) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentPosition s u x n ∧
      u.RIP = 0x1154c0 ∧ MontgomeryAt u (exponentFrameBase s + 0x30)
        (x ^ (sqrtExponent / 16 ^ n) % P256.Spec.Operations.domain.p) := by
  obtain ⟨v, beginFuel, hab, hpv, hiv, hav⟩ := hp.window_begin ctx hn
  have hsquared : ∃ w fuel, Advances boundary fuel v w ∧ ExponentPosition s w x n ∧
      w.RIP = 0x11586c ∧ MontgomeryAt w (exponentFrameBase s + 0x30)
        (x ^ (sqrtExponent / 16 ^ (n + 1) * 16) % P256.Spec.Operations.domain.p) := by
    by_cases htop : n = 63
    · subst n
      refine ⟨v, 0, (advances_zero boundary v v).mpr rfl, hpv, ?_, ?_⟩
      · simpa only [ite_true] using hiv
      · simpa only [show (63 : Nat) + 1 = 64 from rfl, sqrtExponent_initial_prefix, Nat.zero_mul] using hav
    · obtain ⟨w, fuel, haw, hpw, hiw, hacc⟩ := square_four_correct ctx hpv
        (by simpa only [htop, ite_false] using hiv) hav
      rw [exponent_prefix_after_square] at hacc
      exact ⟨w, fuel, haw, hpw, hiw, hacc⟩
  obtain ⟨w, squareFuel, has, hpw, hiw, haw⟩ := hsquared
  obtain ⟨v', had, hpv', hiv', hax, hmem⟩ := exponent_read_digit ctx hpw hn hiw
  have hav' : MontgomeryAt v' (exponentFrameBase s + 0x30)
      (x ^ (sqrtExponent / 16 ^ (n + 1) * 16) % P256.Spec.Operations.domain.p) :=
    montgomeryAt_of_memory (fun a => congrArg (fun m : Ram => m[a]?) hmem) haw
  by_cases hz : sqrtExponent / 16 ^ n % 16 = 0
  · have hexp : sqrtExponent / 16 ^ (n + 1) * 16 = sqrtExponent / 16 ^ n := by
      have hh := exponent_prefix_step sqrtExponent n
      simpa only [hz, Nat.add_zero] using hh
    rw [hexp] at hav'
    exact ⟨v', beginFuel + squareFuel + 11, (hab.trans has).trans had, hpv',
      by simpa only [hz, ite_true] using hiv', hav'⟩
  · obtain ⟨u, multiplyFuel, ham, hpu, hiu, hau⟩ := exponent_multiply ctx hpv'
      (by simpa only [hz, ite_false] using hiv') (Nat.mod_lt _ (by decide))
      hax hav'
    rw [exponent_prefix_after_multiply] at hau
    exact ⟨u, beginFuel + squareFuel + 11 + multiplyFuel,
      ((hab.trans has).trans had).trans ham, hpu, hiu, hau⟩

end P256.Proofs.Sec1.SquareRoot
