import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.State
import K256.Proofs.Signing.UpdateV.Copy
import K256.Proofs.Common.WordCopy
import K256.Proofs.Signing.UpdateV.Prepare.ContextCopy
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def copyReturn (second : Bool) : BitVec 64 := if second then 0x104579 else 0x10416d

def moved (fr : Activation) (m : Ram) := memCopy m (sp fr + 560) (sp fr + 328) 104

def padWords (fr : Activation) (second : Bool) (m : Ram) : Nat → Ram
  | 0 => moved fr m
  | k + 1 => memStore (padWords fr second m k) (sp fr + BitVec.ofNat 64 (496 + 8 * (7-k)))
      (memLoad m (sp fr + BitVec.ofNat 64 ((if second then 48 else 160) + 8 * (7-k))) 64)

def pushed (fr : Activation) (second : Bool) (m : Ram) :=
  memStore (padWords fr second m 8) (sp fr - 8) (copyReturn second)

def copied (fr : Activation) (second : Bool) (m : Ram) :=
  memCopy (pushed fr second m) (context fr second) (sp fr + 496) 168

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
