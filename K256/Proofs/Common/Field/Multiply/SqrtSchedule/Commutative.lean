import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Value

namespace K256.Proofs.Common.Field.Multiply.SqrtSchedule

private theorem productCoefficients_transpose (p : Fin 5 → Fin 5 → Wide) :
    productCoefficients (fun i j => p j i) = productCoefficients p := by
  simp only [productCoefficients, wideAddRev_eq, wideAdd_left_comm, wideAdd_comm]

theorem mulWords_comm (a b : Limbs) : Field.mulWords a b = Field.mulWords b a := by
  have h : (fun (i j : Fin 5) => wideMul b[i] a[j]) =
      (fun (i j : Fin 5) => wideMul a[j] b[i]) := by
    funext i j
    exact wideMul_comm _ _
  rw [← reduce_productCoefficients b a, ← reduce_productCoefficients a b,
    h, productCoefficients_transpose, wideMul_comm b[4] a[4]]

end K256.Proofs.Common.Field.Multiply.SqrtSchedule
