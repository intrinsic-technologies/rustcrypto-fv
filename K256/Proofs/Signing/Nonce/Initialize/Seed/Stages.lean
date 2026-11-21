import K256.Proofs.Signing.Nonce.Initialize.State

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

structure OrderRegisters (a : Verify.Core.Registers) : Prop where
  w0 : a[15] = ⟨64,(scalarWords Secp256k1.domain.n)[0]⟩
  w1 : a[14] = ⟨64,(scalarWords Secp256k1.domain.n)[1]⟩
  w2 : a[13] = ⟨64,(scalarWords Secp256k1.domain.n)[2]⟩
  w3 : a[3] = ⟨64,(scalarWords Secp256k1.domain.n)[3]⟩

structure DigestLength (fr : Activation) (a : Verify.Core.Registers) (m : Ram) : Prop
    extends Frame .l101026 fr a m, OrderRegisters a where
  shift : a[5] = ⟨64,0⟩
  len : a[6] = ⟨64,32⟩
  bits : a[9] = ⟨64,256⟩
  widths : ParseSignature.ArgumentWidths a

structure DigestLimbs (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (x : Nat) : Prop
    extends Frame .l1010ae fr a m, OrderRegisters a where
  words : WordsAt m (fr.rsp - 272) 64 (scalarWords x)
  widths : ParseSignature.ArgumentWidths a

structure ReducedLimbs (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (x : Nat) : Prop
    extends Frame .l10126c fr a m where
  source : a[5] = ⟨64,fr.rsp - 272⟩
  r13Width : a[13].width = 64
  words : WordsAt m (fr.rsp - 272) 64 (scalarWords x)
  widths : ParseSignature.ArgumentWidths a

end K256.Proofs.Signing.Nonce.Initialize
