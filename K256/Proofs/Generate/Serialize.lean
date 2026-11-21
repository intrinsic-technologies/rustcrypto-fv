import K256.Proofs.Generate.Wrapper.Scalar
import K256.Proofs.Generate.Wrapper.Point
import K256.Proofs.Generate.Wrapper.Copy
import K256.Proofs.Generate.Wrapper.Return
import K256.Proofs.Generate.Output

namespace K256.Proofs.Generate

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters

theorem serialize {initial : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng initial [random]) :
    ∀ args mem d point, KeyReady initial random args mem d point →
      ∃ out, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l102539, args, mem⟩, []⟩ out ∧
        Common.Returned initial #v[outputRegion signingKeyGenerateFromRng initial,
          Stack.region initial signingKeyGenerateFromRng.minStackBytes] out ∧
        (outputRegion signingKeyGenerateFromRng initial).HasBytes out.store
          (K256.Spec.Secp256k1.generatedSigningKey random) := by
  intro args mem d pt key
  obtain ⟨_, _, scalarRun, scalarFrame, dst, width, affine, secret⟩ := Wrapper.scalar call key
  obtain ⟨_, _, pointRun, pointFrame, dest, tag, prefixBytes, encoded⟩ :=
    Wrapper.point call scalarFrame dst width affine secret
  obtain ⟨_, _, copyRun, copyFrame, scalarBytes, pointBytes⟩ :=
    Wrapper.copy call pointFrame dest tag prefixBytes encoded
  obtain ⟨out, finishRun, returned, bytes⟩ := Wrapper.finish call copyFrame
    (output_hasBytes key.scalar key.publicKey scalarBytes pointBytes)
  exact ⟨out, Program.Exec.of_sem (scalarRun.exec (pointRun.exec (copyRun.exec finishRun.sem))),
    returned, bytes⟩

end K256.Proofs.Generate
