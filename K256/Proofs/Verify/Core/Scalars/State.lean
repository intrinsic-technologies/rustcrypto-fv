import K256.Proofs.Verify.Core.State

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Generate.Generator.Multiply (scalarWords)

structure Reduced (fr : Activation) (a : Registers) (m : Ram)
    (digest : ByteArray) (r s : Nat) : Prop extends Phase fr a m where
  atoms : Atom.All Extracted.programImage a m (Fn104f20.frameAt .l10518b fr)
  digestAt : WordsAt m (localSp fr + 352) 64 (scalarWords (Nat.mod (Encoding.octetsToNat digest) domain.n))
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)
  sAt : WordsAt m (localSp fr + 224) 64 (scalarWords s)

structure Inverted (fr : Activation) (a : Registers) (m : Ram)
    (digest : ByteArray) (r s : Nat) : Prop extends Phase fr a m where
  atoms : Atom.All Extracted.programImage a m (Fn104f20.frameAt .l1051b1 fr)
  digestAt : WordsAt m (localSp fr + 352) 64 (scalarWords (Nat.mod (Encoding.octetsToNat digest) domain.n))
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)
  inverseAt : WordsAt m (localSp fr + 8) 64 (scalarWords (Curve.inverse domain.n s))

end K256.Proofs.Verify.Core
