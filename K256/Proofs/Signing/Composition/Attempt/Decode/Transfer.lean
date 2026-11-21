import K256.Proofs.Ecdh.Scalar.Select
import K256.Proofs.Generate.Generator.Sample.Decode.Scalar
import K256.Proofs.Verify.Transfer.Compare

namespace K256.Proofs.Signing.Composition.Attempt

open X86.Machine X86.UserProcess X86Proofs CFG Lift Generate.Serialize

private def decodeTarget : Generate.LIR.Label → Option Verify.LIR.Label
  | .l109e60 => some .l109e60
  | .l109f32 => some .l109f32
  | l => Verify.Transfer.compareTarget l

private theorem decodeBlocks (l : Generate.LIR.Label) (dst : Verify.LIR.Label)
    (entry : decodeTarget l = some dst) :
    Relabel.block decodeTarget (Generate.LIR.program.blocks l) =
      Relabel.block some (Verify.LIR.program.blocks dst) := by
  cases l <;> rename_i label <;> cases label <;> cases entry <;> with_unfolding_all rfl

theorem decodeScalarToVerify {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : Generate.LIR.program.Exec (dialect code) ⟨⟨.l109e60,a,m⟩,[]⟩ out) :
    Verify.LIR.program.Exec (dialect code) ⟨⟨.l109e60,a,m⟩,[]⟩ out :=
  Relabel.exec decodeBlocks run rfl

private def selectTarget : Ecdh.LIR.Label → Option Verify.LIR.Label
  | .l10a220 => some .l10a220
  | _ => none

private theorem selectBlocks (l : Ecdh.LIR.Label) (dst : Verify.LIR.Label)
    (entry : selectTarget l = some dst) :
    Relabel.block selectTarget (Ecdh.LIR.program.blocks l) =
      Relabel.block some (Verify.LIR.program.blocks dst) := by
  cases l <;> rename_i label <;> cases label <;> cases entry <;> with_unfolding_all rfl

theorem selectScalarToVerify {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : Ecdh.LIR.program.Exec (dialect code) ⟨⟨.l10a220,a,m⟩,[]⟩ out) :
    Verify.LIR.program.Exec (dialect code) ⟨⟨.l10a220,a,m⟩,[]⟩ out :=
  Relabel.exec selectBlocks run rfl

end K256.Proofs.Signing.Composition.Attempt
