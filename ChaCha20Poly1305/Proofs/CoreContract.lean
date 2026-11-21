import ChaCha20Poly1305.Spec
import X86Proofs.Program.Code
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.Stack

namespace ChaCha20Poly1305.Proofs.CoreContract

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs

def coreEntry : BitVec 64 := 0x100650

def coreReturnAddressInPlace : BitVec 64 := 0x10199f

def coreStackBytes : Nat := 992

def resultBytes : Nat := 17

def resultRegion (s : RamState) : MemoryRegion := registerRegion s .rdi resultBytes

def keyRegion (s : RamState) : MemoryRegion := registerRegion s .rsi 32

def nonceRegion (s : RamState) : MemoryRegion := registerRegion s .rdx 12

def associatedDataRegion (s : RamState) : MemoryRegion :=
  registerRegion s .rcx (s.regValue .r8).toNat

def descriptorRegion (s : RamState) : MemoryRegion := registerRegion s .r9 24

def descriptorWord (s : RamState) (index : Nat) : MemoryRegion :=
  ⟨(s.regValue .r9).toNat + 8 * index, 8⟩

def messageRegion (address : BitVec 64) (length : Nat) : MemoryRegion :=
  ⟨address.toNat, length⟩

def coreWritten (s : RamState) (outPtr : BitVec 64) (length : Nat) : List MemoryRegion :=
  [resultRegion s, messageRegion outPtr length, Stack.region s coreStackBytes]

def coreRead (s : RamState) (inPtr outPtr : BitVec 64) (length : Nat) : List MemoryRegion :=
  [keyRegion s, nonceRegion s, associatedDataRegion s, descriptorRegion s] ++
    (if inPtr = outPtr then [] else [messageRegion inPtr length])

structure CorePre [bindings : Machine.Bindings] (s : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray)
    (inPtr outPtr : BitVec 64) : Prop where
  environment : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  code : CodeIn Extracted.programImage s
  entry : s.RIP = coreEntry
  directionFlagUnset : DirectionFlagUnset s
  stack : Stack.Valid s coreStackBytes
  keyInMemory : ValidInput s (keyRegion s) ⟨key.toArray⟩
  nonceInMemory : ValidInput s (nonceRegion s) ⟨nonce.toArray⟩
  associatedDataLength : (s.regValue .r8).toNat = associatedData.size
  associatedDataInMemory : ValidInput s (associatedDataRegion s) associatedData
  descriptorBounded : (descriptorRegion s).Bounded
  inPointer : (descriptorWord s 0).Word64At s.external inPtr
  outPointer : (descriptorWord s 1).Word64At s.external outPtr
  messageLength : (descriptorWord s 2).Word64At s.external (BitVec.ofNat 64 plaintext.size)
  messageInMemory : ValidInput s (messageRegion inPtr plaintext.size) plaintext
  outputInMemory : ValidOutput s (messageRegion outPtr plaintext.size)
  inPlaceOrApart : inPtr = outPtr ∨
    (messageRegion inPtr plaintext.size).Disjoint (messageRegion outPtr plaintext.size)
  resultInMemory : ValidOutput s (resultRegion s)
  separation : MemorySeparation (coreWritten s outPtr plaintext.size)
    (coreRead s inPtr outPtr plaintext.size)

structure CorePost [bindings : Machine.Bindings] (s t : RamState) (key : Vector UInt8 32)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray)
    (outPtr : BitVec 64) : Prop where
  environment : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  calleeSaved : CalleeSavedRegistersUnchanged s t
  directionFlagUnset : DirectionFlagUnset t
  frame : MemoryWriteFrame s t
    #v[resultRegion s, messageRegion outPtr plaintext.size, Stack.region s coreStackBytes]
  resultOk : (⟨(s.regValue .rdi).toNat, 1⟩ : MemoryRegion).HasBytes t.external
    (ByteArray.mk #[0])
  tag : (⟨(s.regValue .rdi).toNat + 1, 16⟩ : MemoryRegion).HasBytes t.external
    ⟨(chacha20AeadEncrypt associatedData key nonce plaintext).2.toArray⟩
  ciphertext : (messageRegion outPtr plaintext.size).HasBytes t.external
    (chacha20AeadEncrypt associatedData key nonce plaintext).1

  allocated : ∀ region ∈ coreWritten s outPtr plaintext.size, region.Allocated t.external

theorem CorePost.grows [bindings : Machine.Bindings] {s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    {outPtr : BitVec 64} (post : CorePost s t key nonce associatedData plaintext outPtr)
    (a : BitVec 64) (ha : (s.external[a]?).isSome) : (t.external[a]?).isSome := by
  classical
  by_cases h : ∃ r ∈ coreWritten s outPtr plaintext.size, r.Contains a.toNat
  · obtain ⟨r, hr, ar⟩ := h
    exact Option.isSome_iff_exists.mpr (post.allocated r hr a ar)
  · rw [post.frame a ?_]
    · exact ha
    · intro r hr ar
      apply h
      refine ⟨r, ?_, ar⟩
      simpa only [coreWritten, Vector.mem_mk, List.mem_toArray] using hr

end ChaCha20Poly1305.Proofs.CoreContract
