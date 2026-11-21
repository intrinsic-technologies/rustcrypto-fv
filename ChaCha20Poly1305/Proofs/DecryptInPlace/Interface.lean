import ChaCha20Poly1305.Proofs.Decrypt.PacketOf
import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

def scratch (s : RamState) : MemoryRegion := ⟨(stackPtr s).toNat - 1072, 1072⟩

def prefixChanges (s : RamState) : List Component :=
  [.reg 0, .reg 4, .reg 7, .flags, .rip, .mem (stackPtr s - 32) 32]

def callChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 4, .reg 7, .reg 8, .reg 9, .flags, .rip, .mem (stackPtr s - 80) 80]

def keyCopy (s u : RamState) (key : Vector UInt8 32) : Prop :=
  ∀ i : Fin 4, memLoad u.external (stackPtr s - 32 + BitVec.ofNat 64 (8 * i.val)) 64 =
    (Detached.keyQuads key)[i]

structure AfterLength [Bindings] (s u : RamState) (key : Vector UInt8 32) (n : Nat) : Prop where
  track : ChaCha20Poly1305.Proofs.Wrapper.GTrack (prefixChanges s) s u
  rip : u.RIP = if n < 16 then 0x1016be else 0x101682
  rsp : stackPtr u = stackPtr s - 72
  status : u.regValue .rax = 1
  keyWords : keyCopy s u key

structure AtDetached [Bindings] (s u : RamState) (p : Detached.Packet) : Prop where
  track : ChaCha20Poly1305.Proofs.Wrapper.GTrack (callChanges s) s u
  rip : u.RIP = 0x1001f0
  rsp : stackPtr u = stackPtr s - 80
  keyPtr : u.regValue .rdi = stackPtr s - 32
  aadLen : u.regValue .rcx = s.regValue .r8
  desc : u.regValue .r8 = stackPtr s - 56
  tagLo : u.regValue .r9 = p.tag.extractLsb' 0 64
  tagHi : memLoad u.external (stackPtr s - 72) 64 = p.tag.extractLsb' 64 64
  ret : memLoad u.external (stackPtr s - 80) 64 = 0x1016bb
  src : memLoad u.external (stackPtr s - 56) 64 = p.buf
  dst : memLoad u.external (stackPtr s - 48) 64 = p.buf
  len : memLoad u.external (stackPtr s - 40) 64 = p.n
  keyWords : keyCopy s u p.key

def footprint (s : RamState) (accepted : Bool) : List MemoryRegion :=
  scratch s :: (if accepted then [outputRegion decryptInPlace s] else [])

structure AtEpilogue [Bindings] (s u : RamState) (normalize accepted : Bool) : Prop where
  ready : EntryReady Decrypt.Lifted.fnCode u
  rip : u.RIP = if normalize then 0x1016bb else 0x1016be
  rsp : stackPtr u = stackPtr s - 72
  status : if normalize then (u.regValue .rax).setWidth 8 = (if accepted then 0 else 1)
    else (u.regValue .rax).setWidth 32 = (if accepted then 0 else 1)
  saved : CalleeSavedRegistersUnchanged s u
  df : DirectionFlagUnset u
  frame : RamWriteFrame s.external u.external (footprint s accepted)

abbrev inPlacePacket (s : RamState) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (aad msg : ByteArray) (long : 16 ≤ msg.size) (small : msg.size < 2^32) :=
  Decrypt.Wrapper.packet key nonce aad msg (s.regValue .rdx) (s.regValue .rcx) long small

abbrev calleeFrame (u : RamState) := Activation.ofEntry u 864 0x1016bb

end ChaCha20Poly1305.Proofs.DecryptInPlace
