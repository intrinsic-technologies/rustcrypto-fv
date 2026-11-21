import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Finish

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Proofs.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem curve_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Parsed s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Validated s u bytes := by
  obtain ⟨n0,a,run0,sa⟩ := arithmetic_execute pre state
  obtain ⟨n1,b,run1,sb⟩ := compare_execute pre sa
  obtain ⟨n2,u,run2,su⟩ := finish_execute pre sb
  exact ⟨n0+n1+n2,u,(run0.trans run1).trans run2,su⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
