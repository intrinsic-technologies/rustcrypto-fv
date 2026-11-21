import K256.Proofs.Sec1.SqrtLaterProducts.Early.Stages
import K256.Proofs.Sec1.SqrtLaterProducts.Middle.Stages
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Stages

namespace K256.Proofs.Sec1.SqrtLaterProducts

open X86.UserProcess Refine Common.Field SqrtChainExecution

theorem laterStages {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    (i : Fin 13) (hi : 2 ≤ i.val) (g : Geometry code fr) (ha : FieldRepr a x 8) :
    MultiplyStage code fr a i := by
  by_cases early : i.val ≤ 4
  · exact Early.earlyStages i hi early g ha
  by_cases middle : i.val ≤ 8
  · exact Middle.middleStages i (by omega) middle g ha
  exact Final.finalStages i (by omega) (by omega) g ha

end K256.Proofs.Sec1.SqrtLaterProducts
