import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Generate.LIR

private def Keeps (m : Ram) : Transfer Value Ram Label signature Reg.count → Prop
  | .returned out => out.store = m
  | _ => True

private theorem keepsGuard {m : Ram} {t : Transfer Value Ram Label signature Reg.count}
    {g : Prop} [Decidable g] (h : Keeps m t) : Keeps m (if g then t else .stuck) := by
  split <;> first | exact h | trivial

theorem returnedStore {code : CodeMap} {a : Values Value 7260} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : b_l10a410_171.eval (dialect code) a m = .returned out) : out.store = m := by
  obtain ⟨t, ev, inv⟩ : ∃ t, b_l10a410_171.eval (dialect code) a m = t ∧ Keeps m t := by
    refine ⟨?_, ?ev, ?post⟩
    case ev =>
      arithmetic_prefix
      rfl
    case post =>
      repeat' apply keepsGuard
      rfl
  rw [← ev, run] at inv
  exact inv

end K256.Proofs.Generate.Generator.Multiply.AddReplay
