import P256.Proofs.Sec1.Affine.Branches
import P256.Proofs.Sec1.Affine.Uncompressed.Parse
import P256.Proofs.Sec1.Affine.Uncompressed.Curve
import P256.Proofs.Sec1.Affine.Uncompressed.Output

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem uncompressed_correct : UncompressedCorrect := by
  intro bindings s t boundary bytes pre size tag state rip
  obtain ⟨n, a, runA, parsed⟩ := Uncompressed.parse_correct pre state size rip
  obtain ⟨m, b, runB, validated⟩ := Uncompressed.Curve.curve_correct pre parsed
  obtain ⟨k, u, runU, frameU, ripU, valueU⟩ :=
    Uncompressed.Output.output_correct pre validated size tag
  exact ⟨n + m + k, u, (runA.trans runB).trans runU, frameU, ripU, valueU⟩

end P256.Proofs.Sec1.Affine
