import ChaCha20Poly1305.Proofs.Core.Invariant
import ChaCha20Poly1305.Proofs.Common.Poly1305State
import ChaCha20Poly1305.Proofs.Poly1305.Mac

namespace ChaCha20Poly1305.Proofs.Core

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.Poly1305State ChaCha20Poly1305.Proofs.Poly1305.Mac

def cipherOffset : Nat := 0xd0

def polyOffset : Nat := 0x150

def lengthLimit : BitVec 64 := 0x3fffffffbf

def polyBase (s : RamState) : BitVec 64 := framePointer s + BitVec.ofNat 64 polyOffset

structure PolyState (t : RamState) (base : BitVec 64) (otk : Vector UInt8 32) (acc : Nat) :
    Prop where
  pad : wordValue (padWords t base) = padOf otk
  rClamped : ClampedLimbs (rLimbs t base)
  rValue : limbValue (rLimbs t base) = clampedR otk
  hBounded : BoundedLimbs (hLimbs t base)
  hValue : limbValue (hLimbs t base) % prime = acc

def otk (key : Vector UInt8 32) (nonce : Vector UInt8 12) : Vector UInt8 32 :=
  poly1305KeyGen key nonce

def ciphertext (key : Vector UInt8 32) (nonce : Vector UInt8 12) (plaintext : ByteArray) :
    ByteArray :=
  chacha20Encrypt key 1 nonce plaintext

def adAcc (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ad : ByteArray) : Nat :=
  absorbBlocks (clampedR (otk key nonce)) 0 (ad ++ pad16 ad)

def ctAcc (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ad plaintext : ByteArray) : Nat :=
  let ct := ciphertext key nonce plaintext
  absorbBlocks (clampedR (otk key nonce)) (adAcc key nonce ad) (ct ++ pad16 ct)

def fullAcc (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ad plaintext : ByteArray) : Nat :=
  absorbBlocks (clampedR (otk key nonce)) (ctAcc key nonce ad plaintext)
    (lengthBlock ad (ciphertext key nonce plaintext))

def cipherWords (key : Vector UInt8 32) (nonce : Vector UInt8 12) : ByteArray :=
  ⟨(serialize (initialState key 1 nonce)).toArray⟩

structure Cut1 [bindings : Machine.Bindings] (s t : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) (inPtr outPtr : BitVec 64) :
    Prop extends Inv s t outPtr plaintext.size where
  rip : t.RIP = 0x10083c
  rbp : t.regValue .rbp = s.regValue .rcx
  r12 : t.regValue .r12 = s.regValue .r9
  r13 : t.regValue .r13 = s.regValue .r8
  r14 : t.regValue .r14 = s.regValue .rdi
  r15 : t.regValue .r15 = polyBase s
  rbx : t.regValue .rbx = lengthLimit
  rcx : t.regValue .rcx = BitVec.ofNat 64 plaintext.size
  message : (messageRegion inPtr plaintext.size).HasBytes t.external plaintext
  cipher : (⟨frameBase s + cipherOffset, 0x40⟩ : MemoryRegion).HasBytes t.external
    (cipherWords key nonce)
  position : (⟨frameBase s + cipherOffset + 0x40, 1⟩ : MemoryRegion).HasBytes t.external
    ⟨#[64]⟩
  poly : PolyState t (polyBase s) (otk key nonce) 0

structure Cut2 [bindings : Machine.Bindings] (s t : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) (inPtr outPtr : BitVec 64) :
    Prop extends Inv s t outPtr plaintext.size where
  rip : t.RIP = 0x1008d9
  r15 : t.regValue .r15 = polyBase s
  rbx : t.regValue .rbx = lengthLimit
  lengthSlot : (slot s 0x10).Word64At t.external (BitVec.ofNat 64 plaintext.size)
  adLengthSlot : (slot s 0x98).Word64At t.external (s.regValue .r8)
  resultSlot : (slot s 0xa0).Word64At t.external (s.regValue .rdi)
  descriptorSlot : (slot s 0xa8).Word64At t.external (s.regValue .r9)
  message : (messageRegion inPtr plaintext.size).HasBytes t.external plaintext
  cipher : (⟨frameBase s + cipherOffset, 0x40⟩ : MemoryRegion).HasBytes t.external
    (cipherWords key nonce)
  position : (⟨frameBase s + cipherOffset + 0x40, 1⟩ : MemoryRegion).HasBytes t.external
    ⟨#[64]⟩
  poly : PolyState t (polyBase s) (otk key nonce) (adAcc key nonce associatedData)

structure Cut3 [bindings : Machine.Bindings] (s t : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) (outPtr : BitVec 64) :
    Prop extends Inv s t outPtr plaintext.size where
  rip : t.RIP = 0x100916
  r12 : t.regValue .r12 = outPtr
  r14 : t.regValue .r14 = BitVec.ofNat 64 plaintext.size
  r15 : t.regValue .r15 = polyBase s
  rbx : t.regValue .rbx = lengthLimit
  lengthSlot : (slot s 0x10).Word64At t.external (BitVec.ofNat 64 plaintext.size)
  adLengthSlot : (slot s 0x98).Word64At t.external (s.regValue .r8)
  resultSlot : (slot s 0xa0).Word64At t.external (s.regValue .rdi)
  ciphertext : (messageRegion outPtr plaintext.size).HasBytes t.external
    (ciphertext key nonce plaintext)
  poly : PolyState t (polyBase s) (otk key nonce) (adAcc key nonce associatedData)

structure Cut4 [bindings : Machine.Bindings] (s t : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) (outPtr : BitVec 64) :
    Prop extends Inv s t outPtr plaintext.size where
  rip : t.RIP = 0x100984
  r15 : t.regValue .r15 = polyBase s
  lengthSlot : (slot s 0x10).Word64At t.external (BitVec.ofNat 64 plaintext.size)
  adLengthSlot : (slot s 0x98).Word64At t.external (s.regValue .r8)
  resultSlot : (slot s 0xa0).Word64At t.external (s.regValue .rdi)
  ciphertext : (messageRegion outPtr plaintext.size).HasBytes t.external
    (ciphertext key nonce plaintext)
  poly : PolyState t (polyBase s) (otk key nonce)
    (ctAcc key nonce associatedData plaintext)

structure Cut5 [bindings : Machine.Bindings] (s t : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) (outPtr : BitVec 64) :
    Prop extends Inv s t outPtr plaintext.size where
  rip : t.RIP = 0x1009a8
  r15 : t.regValue .r15 = polyBase s
  resultSlot : (slot s 0xa0).Word64At t.external (s.regValue .rdi)
  ciphertext : (messageRegion outPtr plaintext.size).HasBytes t.external
    (ciphertext key nonce plaintext)
  poly : PolyState t (polyBase s) (otk key nonce)
    (fullAcc key nonce associatedData plaintext)

end ChaCha20Poly1305.Proofs.Core
