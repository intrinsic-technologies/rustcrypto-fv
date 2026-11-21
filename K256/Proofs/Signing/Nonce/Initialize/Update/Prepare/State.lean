import K256.Proofs.Signing.Nonce.Initialize.Update.State

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def head (second outer : Bool) : Label :=
  if second then (if outer then .l1044c0 else .l104410)
  else (if outer then .l104090 else .l103fe0)

def exitLabel (second outer : Bool) : Label :=
  if second then (if outer then .l1044de else .l10442e)
  else (if outer then .l1040ba else .l10400a)

def pad (fr : Activation) (second : Bool) : BitVec 64 :=
  sp fr + (if second then 48 else 160)

structure Compressed (fr : Activation) (second : Bool) (m : Ram) (key : ByteArray) : Prop where
  used : memLoad m (sp fr + 391) 8 = 0
  hash : Compression.StateAt m (sp fr + 392) (compressBlocks initialHash (UpdateV.keyPad key 0x36))
  count : memLoad m (sp fr + 424) 64 = 1

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
