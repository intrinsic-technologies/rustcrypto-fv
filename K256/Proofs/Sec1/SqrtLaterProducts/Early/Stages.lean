import K256.Proofs.Sec1.SqrtLaterProducts.Early.Execution
import K256.Proofs.Sec1.SqrtLaterProducts.Words
import K256.Proofs.Sec1.SqrtChainExecution.ProductResume

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution

theorem earlyStages {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    (i : Fin 13) (lo : 2 ≤ i.val) (hi : i.val ≤ 4) (g : Geometry code fr)
    (ha : FieldRepr a x 8) : MultiplyStage code fr a i := by
  intro args mem st
  obtain ⟨child, direct, state⟩ := call lo hi g st
  have old : StandardFrame code fr args mem := by
    have cases : i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl <;> exact st.frame
  have w := window old
  obtain ⟨hb, hl, _⟩ := w.blockBounds (start := 0x116316) (finish := 0x11703f) g (by decide) (by decide)
  have output := productWords i lo ha st w.rsp w.writable hb hl
  rw [direct] at output
  exact productResume g (by simp only [counted, decide_eq_false (by omega : ¬6 ≤ i.val), Bool.false_and])
    direct (state output)

end K256.Proofs.Sec1.SqrtLaterProducts.Early
