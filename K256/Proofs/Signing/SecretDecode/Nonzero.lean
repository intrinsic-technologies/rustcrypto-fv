import K256.Proofs.Signing.SecretDecode.Nonzero.Compare
import K256.Proofs.Signing.SecretDecode.Nonzero.Choice
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

theorem nonzeroPath {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 80 < 2^32)
    (h : Frame .l106eed fr a m) (limbs : Limbs fr a)
    (nz : ¬ ∀ i < 4, word fr i = 0) :
    ∃ b n, Verify.Core.Reaches .l106eed a m .l106f49 b n ∧ Frame .l106f49 fr b n ∧ Limbs fr b := by
  obtain ⟨b, n, comp, hb, lb, zero⟩ := compareNonzero low room high h limbs nz
  obtain ⟨c, p, choice, hc, lc, zero'⟩ := choiceNonzero low room high hb lb zero
  have same : (c[0].get 64).setWidth 8 = 0 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans zero'
  refine ⟨?_, p, comp.trans (choice.trans (Semantics.Reaches.single ?step)), ?post⟩
  case step =>
    change program.step _ _ = _
    cfg_eval [same]
    rfl
  case post =>
    rcases hc with ⟨atoms, writes, widths⟩
    refine ⟨⟨?_, writes, ?_⟩, ⟨lc.w0, lc.w1, lc.w2, lc.w3, lc.rbpWidth⟩⟩
    · exact atoms
    · intro ⟨i, bound⟩ hi
      have eq := widths ⟨i, bound⟩ hi
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h | h | h | h | h <;> subst i <;> exact eq

end K256.Proofs.Signing.SecretDecode
