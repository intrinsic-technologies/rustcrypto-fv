import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.TagOutput
import P256.Proofs.Signing.Core.Iteration.Point.Encode.Correct
import P256.Proofs.PublicPoint.Order

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Standards.SECG.ECC P256.Spec.Operations
open Projective.Multiply Projective.Multiply.Machine

set_option maxHeartbeats 600000 in
theorem correct : Contract := by
  intro bindings s t boundary nonce pre input rip
  let point := model Basepoint.basePoint nonce
  have affine := PublicPoint.model_toAffine nonce input.scalar.1
  have nonzero : point.z ≠ 0 := by
    intro zero
    apply PublicPoint.publicPoint_ne_infinity nonce input.positive input.canonical
    rw [← affine]
    change point.toAffine = .infinity
    simp [Projective.toAffine,zero]
  obtain ⟨n1,a,run1,ip1,multiplied,keep1⟩ := Multiply.multiply_correct pre input rip
  obtain ⟨n2,b,run2,ip2,inverted,keep2⟩ := Normalize.inverse_correct pre multiplied ip1
  obtain ⟨n3,c,run3,ip3,selected,keep3⟩ := Normalize.select_inverse pre inverted ip2
  obtain ⟨n4,d,run4,ip4,xproduct,keep4⟩ := Normalize.x_product pre selected ip3
  obtain ⟨n5,e,run5,ip5,coordinates,keep5⟩ := Normalize.coordinates pre xproduct ip4
  obtain ⟨n6,f,run6,ip6,packed,keep6⟩ := Normalize.Finish.packed pre coordinates nonzero ip5
  obtain ⟨n7,g,run7,ip7,saved,keep7⟩ := Normalize.Finish.saved pre packed ip6
  obtain ⟨n8,h,run8,ip8,prepared,keep8⟩ := Normalize.Finish.prepare pre saved ip7
  obtain ⟨n9,i,run9,ip9,output,keep9⟩ := Normalize.Finish.select pre prepared ip8
  obtain ⟨j,run10,ip10,tagged,keep10⟩ := Normalize.Finish.tag_output pre output ip9
  obtain ⟨n11,k,run11,ip11,converted,keep11⟩ := Normalize.convert pre tagged ip10
  obtain ⟨n12,u,run12,ip12,encoded,keep12⟩ := Encode.correct pre converted ip11
  refine ⟨_,u,point.x*Curve.inverse domain.p point.z % domain.p,
    point.y*Curve.inverse domain.p point.z % domain.p,
    (((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12),
    ip12,?_,encoded,(((((((((((keep1.trans keep2).trans keep3).trans keep4).trans keep5).trans keep6).trans keep7).trans keep8).trans keep9).trans keep10).trans keep11).trans keep12)⟩
  change Points.mul nonce domain.G = _
  rw [← affine]
  change point.toAffine = _
  simp [Projective.toAffine,nonzero]

end P256.Proofs.Signing.Core.Iteration.Point
