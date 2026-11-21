import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Loop
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Buffer

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def compressAt (second : Bool) : Label := if second then .l104830 else .l104263

def tailAt (second : Bool) : Label := if second then .l104848 else .l104280

def padded (second : Bool) (state : State) :=
  UpdateV.keyPad state.key 0x36 ++ taggedValue second state

def blockBytes (second : Bool) (state : State) (secret : ByteArray) :=
  remainderBytes (padded second state) ++ secret.extract 0 31

structure Pending (second : Bool) (fr : Activation) (a : Verify.Core.Registers) : Prop
    extends Cursor second fr a 0 where
  next : (if second then a[3] else a[12]) = ⟨64, fr.rsp + 351⟩
  length : (if second then a[12] else a[5]) = ⟨64, 1⟩

structure Filled (second : Bool) (fr : Activation) (m : Ram) (state : State)
    (secret : ByteArray) : Prop where
  outer : (⟨(context fr second).toNat, 64⟩ : MemoryRegion).HasBytes m (UpdateV.keyPad state.key 0x5c)
  bytes : (⟨(context fr second + 64).toNat, 64⟩ : MemoryRegion).HasBytes m (blockBytes second state secret)
  hash : Compression.StateAt m (context fr second + 128) (compressBlocks initialHash (padded second state))
  count : memLoad m (context fr second + 160) 64 = 1

structure Compressed (second : Bool) (fr : Activation) (m : Ram) (state : State)
    (secret : ByteArray) : Prop where
  outer : (⟨(context fr second).toNat, 64⟩ : MemoryRegion).HasBytes m (UpdateV.keyPad state.key 0x5c)
  hash : Compression.StateAt m (context fr second + 128)
    (Reference.compress (compressBlocks initialHash (padded second state)) (bytesToBits (blockBytes second state secret)))
  count : memLoad m (context fr second + 160) 64 = 2

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
