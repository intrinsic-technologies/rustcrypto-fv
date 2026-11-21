import K256.Proofs.Verify.Core.Scalars.State

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Generate.Generator.Multiply (scalarWords)

structure DigestProduct (fr : Activation) (a : Registers) (m : Ram)
    (digest : ByteArray) (r s : Nat) : Prop extends Phase fr a m where
  key : a[14] = ⟨64, fr.rsi⟩
  sig : a[15] = ⟨64, fr.r8⟩
  uPtr : a[12] = ⟨64, localSp fr + 384⟩
  uAt : WordsAt m (localSp fr + 384) 64 (scalarWords (digestScalar digest s))
  inverseAt : WordsAt m (localSp fr + 288) 64 (scalarWords (Curve.inverse domain.n s))
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)
  sizeReg : a[13] = ⟨64, fr.rcx⟩
  widths : ParseSignature.ArgumentWidths a

end K256.Proofs.Verify.Core
