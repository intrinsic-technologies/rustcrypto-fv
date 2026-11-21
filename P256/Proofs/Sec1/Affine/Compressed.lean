import P256.Proofs.Sec1.Affine.Branches
import P256.Proofs.Sec1.Affine.Compressed.Entry
import P256.Proofs.Sec1.Affine.Compressed.Finish
import P256.Proofs.Sec1.Decompress

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compressed_correct : CompressedCorrect := by
  intro bindings s t boundary bytes tag pre size tagByte valid state rip
  obtain ⟨n, a, runA, frameA, ripA, valueA, outputA, sourceA⟩ :=
    Compressed.enter pre state size tagByte valid
      (fun _ hp ↦ by
        simpa only [Spec.Points.element] using Decompress.decompress_correct hp) rip
  obtain ⟨m, u, runU, frameU, ripU, valueU⟩ :=
    Compressed.finish_correct pre frameA ripA sourceA outputA valueA
  exact ⟨n + m, u, runA.trans runU, frameU, ripU, valueU⟩

end P256.Proofs.Sec1.Affine
