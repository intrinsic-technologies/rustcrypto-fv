import P256.Proofs.Ecdh.Initial
import P256.Proofs.Ecdh.Table
import P256.Proofs.Ecdh.Prepare
import P256.Proofs.Ecdh.Multiply
import P256.Proofs.Ecdh.Normalize
import P256.Proofs.Ecdh.Model

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Standards.SECG.ECC

theorem callee_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {d : Nat} {point : Curve.Point} (pre : Pre s boundary)
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d)
    (peer : Sec1.AffineAt s (s.regValue .rdx) point) :
    ∃ u, CalleeResult s u boundary 32 3464 ∧
      (registerRegion s .rdi 32).HasBytes u.external
        (Points.xBytes (Projective.Multiply.model (ProjectiveWrapper.Decode.projective point) d).toAffine) := by
  obtain ⟨a,t,runT,initial⟩ := initial_correct pre peer
  obtain ⟨b,v,runV,prepared⟩ := table_correct pre initial
  obtain ⟨c,w,runW,ready⟩ := prepare_correct pre prepared scalar
  obtain ⟨e,x,runX,multiplied⟩ := multiply_correct pre ready
  exact normalize_correct pre multiplied ⟨a+b+c+e,((runT.trans runV).trans runW).trans runX⟩

theorem diffie_hellman_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {d : Nat} {point : Curve.Point} (pre : Pre s boundary)
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d)
    (peer : Sec1.AffineAt s (s.regValue .rdx) point)
    (curve : Curve.onCurve Operations.domain point = true) :
    ∃ u, CalleeResult s u boundary 32 3464 ∧
      (registerRegion s .rdi 32).HasBytes u.external (P256.Spec.Ecdh.sharedX d point) := by
  obtain ⟨u,result,output⟩ := callee_correct pre scalar peer
  rw [model_sharedX curve scalar.1] at output
  exact ⟨u,result,output⟩

end P256.Proofs.Ecdh
