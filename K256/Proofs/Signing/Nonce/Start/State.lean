import K256.Proofs.Signing.Nonce.Initialize.State
import K256.Proofs.Signing.Hash
import K256.Proofs.Signing.NonceLoop

namespace K256.Proofs.Signing.Nonce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Verify.Hash

structure CandidateRegisters (a : Registers) (sp : BitVec 64) : Prop where
  rsp : a[4] = ⟨64,sp⟩
  df : a[22] = ⟨1,0⟩
  rbx : a[3] = ⟨64,sp + 456⟩
  rbp : a[5] = ⟨64,sp + 192⟩
  r12 : a[12] = ⟨64,sp + 8⟩
  r13 : a[13] = ⟨64,sp + 256⟩
  r14 : a[14].width = 64
  r15 : a[15] = ⟨64,sp + 160⟩
  widths : ParseSignature.ArgumentWidths a

def initializationRegions (sp : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat - 2232, 2272⟩, ⟨sp.toNat + 352,32⟩,
   ⟨sp.toNat + 592,32⟩, ⟨sp.toNat + 688,72⟩]

namespace Start

structure Prepared (a : Registers) (m : Ram) (sp : BitVec 64) (d : Nat) (message : ByteArray) : Prop where
  rsp : a[4] = ⟨64, sp⟩
  df : a[22] = ⟨1, 0⟩
  r12 : a[12] = ⟨64, sp+8⟩
  r13 : a[13] = ⟨64, sp+256⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,14,15] → a[i].width = 64
  digest : (⟨(sp+352).toNat,32⟩ : MemoryRegion).HasBytes m (SHA256.hashBytes message)
  order : WordsAt m (sp+592) 64 (scalarWords domain.n)
  secret : (⟨(sp+8).toNat,32⟩ : MemoryRegion).HasBytes m (Standards.SECG.ECC.Encoding.natToOctets 32 d)

end Start
end K256.Proofs.Signing.Nonce
