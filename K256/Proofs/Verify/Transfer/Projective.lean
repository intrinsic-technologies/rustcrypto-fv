import K256.Proofs.Ecdh.Decode.Convert
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Verify.LIR.Fn10fa10.Frame

namespace K256.Proofs.Verify.Transfer

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program CFG Lift Refine
open K256.Proofs.Verify.LIR Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply Generate.Serialize

private def projectiveTarget : Ecdh.LIR.Label → Option LIR.Label
  | .l10fa10 => some .l10fa10
  | .l10fa68 => some .l10fa68
  | .l127d50 => some .l127d50
  | _ => none

private theorem projectiveBlocks (a : Ecdh.LIR.Label) (b : LIR.Label)
    (h : projectiveTarget a = some b) :
    Relabel.block projectiveTarget (Ecdh.LIR.program.blocks a) =
      Relabel.block some (program.blocks b) := by
  unfold projectiveTarget at h
  split at h <;> cases h <;> rfl

theorem projectiveExecution (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn10fa10.frameAt .l10fa10 fr))
    (src : Readable fr.original fr.rsi 84)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 84)
    (dst : Writable Extracted.programImage fr.original fr.rdi 120)
    (dstApart : Outside [ParseSignature.callStack fr] fr.rdi 120)
    {point : Curve.Point} (input : Ecdh.Decode.AffinePointAt fr.original fr.rsi point)
    (onCurve : Curve.onCurve domain point = true) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10fa10,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10fa10.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,120⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧
      ∃ peer : Projective, peer.Stored out.store fr.rdi ∧ peer.valid ∧ peer.value = point := by
  obtain ⟨out, run, post⟩ :=
    Ecdh.Decode.Convert.execution fr a entry src srcApart dst dstApart input onCurve
  exact ⟨out, Relabel.exec projectiveBlocks run rfl, post⟩

end K256.Proofs.Verify.Transfer
