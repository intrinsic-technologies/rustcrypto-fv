import P256.Proofs.Field.Schoolbook.UpperExecution
import P256.Proofs.Field.Schoolbook.LowerSums.Facts

set_option autoImplicit false

open P256.Proofs.Program (programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem body [Bindings] {s entry : RamState} {boundary : ReturnBoundary}
    (ctx : ExecutionContext s boundary entry) :
    ∃ p lo up l m u, BodyState ctx p ∧ BodyState ctx lo ∧ BodyState ctx u ∧
      (productsEffect entry).Holds entry p ∧
      (lowerSumsEffect p).Holds p lo ∧ (upperProductsEffect lo).Holds lo up ∧
      (upperSumsLowEffect up).Holds up l ∧ (upperSumsMiddleEffect l).Holds l m ∧
      (upperSumsHighEffect m).Holds m u ∧ u.RIP = 0x11cb43 := by
  have initial := BodyState.initial ctx
  obtain ⟨p, ps, hp⟩ := initial.advance (products_correct boundary ctx.pre.outerBoundary)
    (products_code initial.loaded)
    (products_pre ctx.pre ctx.rip ctx.rsp ctx.agrees) (fun _ h => products_scratch h)
  obtain ⟨lo, los, hlo⟩ := ps.advance (lower_sums_correct boundary ctx.pre.outerBoundary)
    (programText_slice (programLoaded_codeIn ps.loaded) 0x1c9f6 _
      (by decide) lowerSumsBytes_extracted)
    (lower_pre ps hp) (fun _ h => lowerSums_scratch h)
  have source : lo.regValue .rsi = s.regValue .rsi :=
    (lowerSums_source hlo).trans ((products_savedSource hp).trans
      (ctx.agrees.read (by simp [P256.Proofs.Common.Field.SquareRoot.Multiply.prologueComponents])))
  obtain ⟨up, l, m, u, us, hup, hl, hm, hu, rip⟩ :=
    upper_body los (lowerSums_rip hlo) source
  exact ⟨p, lo, up, l, m, u, ps, los, us, hp, hlo, hup, hl, hm, hu, rip⟩

end P256.Proofs.Field.Schoolbook
