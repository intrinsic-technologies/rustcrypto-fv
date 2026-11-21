import ChaCha20Poly1305.Spec
import X86Proofs.Program.Execution
import X86Proofs.Program.Agrees
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Step.ReadyToStep
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Region

namespace ChaCha20Poly1305.Proofs.Callee100a80

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305

def entry : BitVec 64 := 0x100a80

def codeEnd : Nat := 0x1014bc

def frameBytes : Nat := 0x1a0

def cipherBytes : Nat := 0x80

def stateBytes (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    ByteArray :=
  ⟨(serialize (initialState key counter nonce)).toArray⟩

def cipherRegion (s : RamState) : MemoryRegion :=
  ⟨(rdi.read s).toNat, cipherBytes⟩

def wordsRegion (s : RamState) : MemoryRegion :=
  ⟨(rdi.read s).toNat, 0x40⟩

def positionRegion (s : RamState) : MemoryRegion :=
  ⟨(rdi.read s).toNat + 0x40, 1⟩

def counterRegion (s : RamState) : MemoryRegion :=
  ⟨(rdi.read s).toNat + 0x30, 4⟩

def blockRegion (s : RamState) : MemoryRegion :=
  ⟨(rdi.read s).toNat + 0x40, 0x40⟩

def bufRegion (s : RamState) : MemoryRegion :=
  ⟨(rsi.read s).toNat, 24⟩

def inPtrSlot (s : RamState) : MemoryRegion :=
  ⟨(rsi.read s).toNat, 8⟩

def outPtrSlot (s : RamState) : MemoryRegion :=
  ⟨(rsi.read s).toNat + 8, 8⟩

def lengthSlot (s : RamState) : MemoryRegion :=
  ⟨(rsi.read s).toNat + 16, 8⟩

def stackRegion (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - frameBytes, frameBytes + 8⟩

def inputRegion (input : BitVec 64) (length : Nat) : MemoryRegion :=
  ⟨input.toNat, length⟩

def outputRegion (output : BitVec 64) (length : Nat) : MemoryRegion :=
  ⟨output.toNat, length⟩

structure Writable (s : RamState) (region : MemoryRegion) : Prop where
  low : region.start + region.size ≤ 2 ^ 32
  present : ∀ i < region.size,
    (s.external[BitVec.ofNat 64 (region.start + i)]?).isSome
  avoids : region.Avoids fun address => InProgram address ∨ pageTables.Contains address.toNat

abbrev Accepted (counter : UInt32) (length : Nat) : Prop :=
  counter.toNat + (length + 63) / 64 < 2 ^ 32

def callChanges (s : RamState) (output : BitVec 64) (length : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip,
    .mem output length,
    .mem (rdi.read s + 0x30) 4,
    .mem (rdi.read s + 0x40) 0x40,
    .mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes]

structure CallPre [Bindings] (s : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (input output : BitVec 64) (message : ByteArray) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = entry
  df : DirectionFlagUnset s
  stackLow : frameBytes ≤ (stackPtr s).toNat
  stack : Writable s (stackRegion s)
  cipher : Writable s (cipherRegion s)
  words : (wordsRegion s).HasBytes s.external (stateBytes key counter nonce)
  position : (positionRegion s).HasBytes s.external ⟨#[64]⟩
  buf : MemReadable s (rsi.read s) 24
  inPtr : (inPtrSlot s).Word64At s.external input
  outPtr : (outPtrSlot s).Word64At s.external output
  length : (lengthSlot s).Word64At s.external (BitVec.ofNat 64 message.size)
  messageBytes : (inputRegion input message.size).HasBytes s.external message
  messageLow : input.toNat + message.size ≤ 2 ^ 32
  out : Writable s (outputRegion output message.size)
  alias : input = output ∨ (inputRegion input message.size).Disjoint
    (outputRegion output message.size)
  inputCipher : (inputRegion input message.size).Disjoint (cipherRegion s)
  inputStack : (inputRegion input message.size).Disjoint (stackRegion s)
  outCipher : (outputRegion output message.size).Disjoint (cipherRegion s)
  outStack : (outputRegion output message.size).Disjoint (stackRegion s)
  outBuf : (outputRegion output message.size).Disjoint (bufRegion s)
  cipherStack : (cipherRegion s).Disjoint (stackRegion s)
  cipherBuf : (cipherRegion s).Disjoint (bufRegion s)
  bufStack : (bufRegion s).Disjoint (stackRegion s)
  returnLow : (returnBoundary s).rip.toNat < 2 ^ 32
  returnOutside : (returnBoundary s).rip.toNat < entry.toNat ∨
    codeEnd ≤ (returnBoundary s).rip.toNat

structure CallResult [Bindings] (s t : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (output : BitVec 64) (message : ByteArray) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  agrees : AgreesExcept (callChanges s output message.size) s t
  status : if Accepted counter message.size then
      (rax.read t).setWidth 8 = 0 ∧
      (outputRegion output message.size).HasBytes t.external
        (chacha20Encrypt key counter nonce message)
    else
      (rax.read t).setWidth 8 = 1 ∧
      MemoryWriteFrame s t #v[⟨(stackPtr s).toNat - frameBytes, frameBytes⟩]

def retAddress : BitVec 64 := 0x1014bb

structure BodyResult [Bindings] (s t : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (output : BitVec 64) (message : ByteArray) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = retAddress
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept (callChanges s output message.size) s t
  status : if Accepted counter message.size then
      (rax.read t).setWidth 8 = 0 ∧
      (outputRegion output message.size).HasBytes t.external
        (chacha20Encrypt key counter nonce message)
    else
      (rax.read t).setWidth 8 = 1 ∧
      MemoryWriteFrame s t #v[⟨(stackPtr s).toNat - frameBytes, frameBytes⟩]

def savedChanges : List Component := [.reg 3, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15]

def savedSlots : List (BitVec 5 × Nat) :=
  [(3, 0x30), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10), (5, 0x8)]

structure Frame [Bindings] (s t : RamState) (output : BitVec 64) (length : Nat) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 frameBytes
  agrees : AgreesExcept (callChanges s output length ++ savedChanges) s t
  saved : ∀ e ∈ savedSlots,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 e.2) : Operand 64).read t =
      (Operand.reg e.1 : Operand 64).read s

def prologueChanges (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes]

structure Entered [Bindings] (s t : RamState) (output : BitVec 64) (length : Nat) : Prop where
  frame : Frame s t output length
  rip : t.RIP = 0x100a91
  agrees : AgreesExcept (prologueChanges s) s t

def Status (s t : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (output : BitVec 64) (message : ByteArray) : Prop :=
  if Accepted counter message.size then
    (rax.read t).setWidth 8 = 0 ∧
    (outputRegion output message.size).HasBytes t.external
      (chacha20Encrypt key counter nonce message)
  else
    (rax.read t).setWidth 8 = 1 ∧
    MemoryWriteFrame s t #v[⟨(stackPtr s).toNat - frameBytes, frameBytes⟩]

theorem Status.transfer {s t u : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {output : BitVec 64} {message : ByteArray}
    (h : Status s t key counter nonce output message) (hrax : rax.read u = rax.read t)
    (hext : u.external = t.external) : Status s u key counter nonce output message := by
  unfold Status at h ⊢
  split at h <;> rename_i hacc <;> simp only [hacc, ↓reduceIte, hrax] at h ⊢
  · exact ⟨h.1, by rw [hext]; exact h.2⟩
  · refine ⟨h.1, fun a ha ↦ ?_⟩
    have hu : u.external[a]? = t.external[a]? := by rw [hext]
    rw [hu]
    exact h.2 a ha

structure Checked [Bindings] (s u : RamState) (counter : UInt32) (output : BitVec 64)
    (length : Nat) : Prop where
  frame : Frame s u output length
  rip : u.RIP = 0x100ad0
  agrees : AgreesExcept (prologueChanges s ++
    [.reg 0, .reg 1, .reg 2, .reg 8, .reg 10, .reg 11, .reg 12]) s u
  length : (Operand.reg 11 : Operand 64).read u = BitVec.ofNat 64 length
  consumed : (Operand.reg 10 : Operand 64).read u = 0
  position : (Operand.reg 1 : Operand 64).read u = 0x40
  counter : (Operand.reg 12 : Operand 64).read u = counter.toBitVec.setWidth 64

end ChaCha20Poly1305.Proofs.Callee100a80
