import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.State

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

def keyCopy (m : Ram) (src dst : BitVec 64) : Ram :=
  let n := memStore m (dst + 24) (memLoad m (src + 24) 64)
  let n := memStore n (dst + 16) (memLoad n (src + 16) 64)
  let lo := memLoad n src 64
  let hi := memLoad n (src + 8) 64
  memStore (memStore n (dst + 8) hi) dst lo

def keyWrites (fr : Activation) : List MemoryRegion :=
  [⟨(sp fr - 8).toNat, 8⟩, ⟨fr.rdi.toNat, 32⟩]

def keyCallMemory (m : Ram) (fr : Activation) (second : Bool) (input : Input) : Ram :=
  memStore (keyCopy m (digestPtr fr second) fr.rdi) (sp fr - 8) (valueReturn second input)

end K256.Proofs.Signing.Nonce.Initialize.Update
