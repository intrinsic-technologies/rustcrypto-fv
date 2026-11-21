import K256.Proofs.Signing.Composition.State
import K256.Proofs.Ecdh.Affine.State

namespace K256.Proofs.Signing.Composition.Attempt

open Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

structure LoopMemory (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (m : Ram) : Prop
    extends CoreMemory s d m where
  hash : (⟨(sp s+352).toNat,32⟩ : MemoryRegion).HasBytes m (SHA256.hashBytes msg)
  order : WordsAt m (sp s+592) 64 (scalarWords domain.n)
  orderPtr : memLoad m (sp s+688) 64 = sp s+592
  state : Nonce.Initialize.StateAt m (sp s+696) st

structure RegistersAt (s : RamState) (a : Registers) (bx bp p13 p15 : BitVec 64) : Prop where
  rsp : a[4] = ⟨64,sp s⟩
  df : a[22] = ⟨1,0⟩
  rbx : a[3] = ⟨64,bx⟩
  rbp : a[5] = ⟨64,bp⟩
  r12 : a[12] = ⟨64,sp s+8⟩
  r13 : a[13] = ⟨64,p13⟩
  r14 : a[14].width = 64
  r15 : a[15] = ⟨64,p15⟩
  widths : ParseSignature.ArgumentWidths a
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16

abbrev digestScalar (msg : ByteArray) := Nat.mod (Encoding.octetsToNat (SHA256.hashBytes msg)) domain.n

abbrev signatureScalar (d : Nat) (msg : ByteArray) (k r : Nat) :=
  Nat.mod (Curve.inverse domain.n k * Nat.mod (digestScalar msg + Nat.mod (r * d) domain.n) domain.n) domain.n

structure NonceParsed (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+456) (sp s+192) (sp s+256) (sp s+160) where
  nonce : WordsAt m (sp s+128) 64 (scalarWords k)

structure ScalarsReady (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+624) (sp s+192) (sp s+656) (sp s+456) where
  nonce : WordsAt m (sp s+624) 64 (scalarWords k)
  digest : WordsAt m (sp s+656) 64 (scalarWords (digestScalar msg))
  inverse : WordsAt m (sp s+8) 64 (scalarWords (Curve.inverse domain.n k))

structure CoordinatesReady (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k x y : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+256) (sp s+192) (sp s+656) (sp s+456) where
  xDst : a[14] = ⟨64,sp s+160⟩
  point : Generate.Curve.generatorWindow k = .affine x y
  xBound : x < 2^256
  xBytes : (⟨(sp s+160).toNat,32⟩ : MemoryRegion).HasBytes m (Encoding.natToOctets 32 x)
  digest : WordsAt m (sp s+656) 64 (scalarWords (digestScalar msg))
  inverse : WordsAt m (sp s+424) 64 (scalarWords (Curve.inverse domain.n k))

structure SignatureScalars (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (r sigS : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+456) (sp s+192) (sp s+192) (sp s+456) where
  temp : a[14] = ⟨64,sp s+160⟩
  rWords : WordsAt m (sp s+128) 64 (scalarWords r)
  sWords : WordsAt m (sp s+456) 64 (scalarWords sigS)

end K256.Proofs.Signing.Composition.Attempt
