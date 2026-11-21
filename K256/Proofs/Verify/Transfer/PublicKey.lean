import K256.Proofs.Verify.Transfer.PublicKey.Execution
import K256.Proofs.Verify.Transfer.Sec1
import K256.Proofs.Verify.LIR.Fn106390.Frame

namespace K256.Proofs.Verify.Transfer

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program CFG
open Lift Refine Verify.LIR Standards.SECG.ECC

theorem publicKeyExecution (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn106390.frameAt .l106390 fr))
    (len : fr.rdx = 65) (src : Readable fr.original fr.rsi 65)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 65)
    (dst : Writable Extracted.programImage fr.original fr.rdi 96)
    (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (image : ∀ x ∈ Extracted.programImage, fr.original[x.1]? = some x.2)
    (text : fr.rsp.toNat ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat - 1544)
    {bytes : ByteArray} {point : Curve.Point} (size : bytes.size = 65)
    (bytesAt : (⟨fr.rsi.toNat,65⟩ : MemoryRegion).HasBytes fr.original bytes)
    (decoded : K256.Spec.Secp256k1.decodePublicKey bytes = some point) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106390,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn106390.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,96⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧ memLoad out.store fr.rdi 64 = 0 ∧
      Ecdh.Decode.AffinePointAt out.store (fr.rdi+8) point := by
  obtain ⟨out,run,post⟩ :=
    PublicKey.execution fr a entry len src srcApart dst dstAbove image text size bytesAt decoded
  exact ⟨out,sec1Exec (dst := .l106390) rfl run,post⟩

end K256.Proofs.Verify.Transfer
