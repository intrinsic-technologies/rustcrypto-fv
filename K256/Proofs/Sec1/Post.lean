import K256.Proofs.Common.Finish

namespace K256.Proofs.Sec1

open K256.Spec K256.Spec.Program K256.Proofs.Common K256.Proofs.CFG K256.Proofs.Lift
  Prelude X86.Machine Standards.SECG.ECC Standards.SECG.DomainParameters

def Post (initial : RamState) (bytes : ByteArray) (out : Output Value Ram Reg.count) : Prop :=
  match Secp256k1.decodePublicKey bytes with
  | some point =>
    Returned initial #v[outputRegion publicKeyFromSec1Bytes initial,
      Stack.region initial publicKeyFromSec1Bytes.minStackBytes] out ∧
    out.values[0] = ⟨64, 0⟩ ∧
    (outputRegion publicKeyFromSec1Bytes initial).HasBytes out.store
      (Points.encodePoint Secp256k1.domain false point)
  | none =>
    Returned initial #v[Stack.region initial publicKeyFromSec1Bytes.minStackBytes] out ∧
    out.values[0] = ⟨64, 1⟩

end K256.Proofs.Sec1
