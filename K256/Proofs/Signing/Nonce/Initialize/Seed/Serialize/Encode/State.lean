import K256.Proofs.Signing.Nonce.Initialize.Seed.Stages

import K256.Proofs.Generate.Wrapper.Scalar.Octets
import K256.Proofs.Verify.LIR.Fn100000.Frame

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

namespace Encode

def label (k : Nat) : Label := if k < 4 then .l100110 else .l100153

structure Loop (fr : Activation) (x k : Nat) (a : Verify.Core.Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn100000.frameAt (label k) fr)
  remaining : a[2] = ⟨64,BitVec.ofNat 64 (32 - 8*k)⟩
  cursor : a[3] = ⟨64,BitVec.ofNat 64 (32 - 8*k)⟩
  index : a[5] = ⟨64,BitVec.ofNat 64 k⟩
  zero : a[12] = ⟨64,0⟩
  count : a[15] = ⟨64,4⟩
  widths : ParseSignature.ArgumentWidths a
  writes : RamWriteFrame fr.original m [fr.region, ⟨fr.rdx.toNat,32⟩]
  words : ∀ i (_hi : i < k) (bound : i < 4),
    memLoad m (wordAddr fr.rdx 64 (3-i)) 64 = bswapSpec ((scalarWords x)[i])

end Encode

end K256.Proofs.Signing.Nonce.Initialize
