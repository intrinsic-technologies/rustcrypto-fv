import K256.Proofs.Signing.Nonce.Initialize.Seed.Stages
import K256.Proofs.Verify.Choice
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.LastFold

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters Generate.Generator.Multiply
  Common.Invert.LinearCombination Common.Invert.ModularShift

def digestDifference (x : Nat) := subRaw (limbs (scalarWords x)) Split.Reduction.orderLimbs

structure DigestSelect (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (x : Nat) : Prop
    extends Frame .l10126c fr (a.set 4 ⟨64,fr.rsp - 280⟩) m where
  rsp : a[4] = ⟨64,fr.rsp - 288⟩
  ret : memLoad m (fr.rsp - 288) 64 = 0x10126c
  dst : a[7] = ⟨64,fr.rsp - 272⟩
  src : a[2] = ⟨64,fr.rsp - 176⟩
  dstLen : a[6] = ⟨64,4⟩
  srcLen : a[1] = ⟨64,4⟩
  flag : a[8] = ⟨64,if x < Secp256k1.domain.n then 1 else 0⟩
  rbp : a[5] = ⟨64,fr.rsp - 272⟩
  r13Width : a[13].width = 64
  widths : ParseSignature.ArgumentWidths a
  originalWords : WordsAt m (fr.rsp - 176) 64 (scalarWords x)
  subtracted : WordsAt m (fr.rsp - 272) 64 (words (digestDifference x).1)

end K256.Proofs.Signing.Nonce.Initialize
