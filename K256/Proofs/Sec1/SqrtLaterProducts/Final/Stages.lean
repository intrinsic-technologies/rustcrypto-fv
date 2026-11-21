import K256.Proofs.Sec1.SqrtLaterProducts.Final.Product
import K256.Proofs.Sec1.SqrtChainExecution.ProductResume
import K256.Proofs.Sec1.SqrtLaterProducts.Words

namespace K256.Proofs.Sec1.SqrtLaterProducts.Final

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution

theorem finalStages {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    (i : Fin 13) (late : 9 ≤ i.val) (_hi : i.val ≤ 12) (geo : Geometry code fr) (ha : FieldRepr a x 8) :
    MultiplyStage code fr a i := by
  intro args mem st
  obtain ⟨child, step, post⟩ := call late geo st
  have old : Early.StandardFrame code fr args mem := by
    unfold Early.StandardFrame
    rw [← (frameLayouts i late fr).1]
    exact st.frame
  have w := Early.window old
  obtain ⟨lo, hi, _⟩ := w.blockBounds (start := 0x118991) (finish := 0x11a110)
    geo (by decide) (by decide)
  have word := productWords i (by omega) ha st w.rsp w.writable lo hi
  have incoming := Eq.mp (congrArg (OutputWords (fr.rsp - 440) (words a (2 * (i.val + 1)))) step) word
  have hn : counted i = false := by
    simp [counted, show ¬ i.val ≤ 8 by omega]
  exact productResume geo hn step (post incoming)

end K256.Proofs.Sec1.SqrtLaterProducts.Final
