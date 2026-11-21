import K256.Proofs.Verify.Core.State
import K256.Proofs.Verify.LIR.Fn100ea0.Frame
import K256.Proofs.Signing.Nonce.Model

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

abbrev State := Standards.RFC.DeterministicSigning.Nonce.State

structure StateAt (m : Ram) (addr : BitVec 64) (state : State) : Prop where
  key : (⟨addr.toNat, 32⟩ : MemoryRegion).HasBytes m state.key
  value : (⟨addr.toNat + 32, 32⟩ : MemoryRegion).HasBytes m state.value

structure Frame (label : Label) (fr : Activation) (a : Verify.Core.Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn100ea0.frameAt label fr)
  writes : RamWriteFrame fr.original m [fr.region]

structure Prepared (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (digest : ByteArray) : Prop
    extends Frame .l101295 fr a m where
  seedPtr : a[12] = ⟨64, fr.rsp - 80⟩
  orderPtr : a[15] = ⟨64, fr.rsp + 616⟩
  bpWidth : a[5].width = 64
  r13Width : a[13].width = 64
  widths : ParseSignature.ArgumentWidths a
  reduced : (⟨(fr.rsp - 80).toNat, 32⟩ : MemoryRegion).HasBytes m
    (Encoding.natToOctets 32 (Nat.mod (Encoding.octetsToNat digest) Secp256k1.domain.n))

structure Updated (fr : Activation) (a : Verify.Core.Registers) (m : Ram) (state : State) : Prop
    extends Frame .l10132a fr a m where
  orderPtr : a[15] = ⟨64, fr.rsp + 616⟩
  bytes : StateAt m (fr.rsp - 272) state
  widths : ParseSignature.ArgumentWidths a

abbrev initial (d : Nat) (digest : ByteArray) :=
  Standards.RFC.DeterministicSigning.Nonce.initialState SHA256.hashBytes 64 32 Secp256k1.domain.n d digest

end K256.Proofs.Signing.Nonce.Initialize
