import K256.Proofs.Signing.Nonce.Initialize.Seed.Stages

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

structure FilledDigest (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (x : Nat) : Prop
    extends Frame .l101072 fr a m, OrderRegisters a where
  shift : a[5] = ⟨64,0⟩
  words : WordsAt m (fr.rsp - 176) 64 (scalarWords x)
  widths : ParseSignature.ArgumentWidths a

end K256.Proofs.Signing.Nonce.Initialize
