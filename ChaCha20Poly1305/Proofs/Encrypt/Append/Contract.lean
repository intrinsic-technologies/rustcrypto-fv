import ChaCha20Poly1305.Proofs.CoreContract

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def appendDescriptor (s : RamState) : MemoryRegion := registerRegion s .rdi 24

def appendSource (s : RamState) : MemoryRegion := registerRegion s .rsi 16

def appendDestination (buffer : BitVec 64) (length : Nat) : MemoryRegion :=
  ⟨buffer.toNat + length, 16⟩

structure AppendPre [bindings : Bindings] (s : RamState) (buffer : BitVec 64)
    (length : Nat) (tag : Vector UInt8 16) : Prop where
  environment : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  code : CodeIn Extracted.programImage s
  entry : s.RIP = 0x101fb0
  directionFlagUnset : DirectionFlagUnset s
  stack : Stack.Valid s 48
  count : s.regValue .rdx = 16
  lengthBound : buffer.toNat + length + 16 < userAddressLimit
  descriptor : ValidOutput s (appendDescriptor s)
  capacity : (⟨(s.regValue .rdi).toNat, 8⟩ : MemoryRegion).Word64At s.external
    (BitVec.ofNat 64 (length + 16))
  pointer : (⟨(s.regValue .rdi).toNat + 8, 8⟩ : MemoryRegion).Word64At s.external buffer
  lengthWord : (⟨(s.regValue .rdi).toNat + 16, 8⟩ : MemoryRegion).Word64At s.external
    (BitVec.ofNat 64 length)
  source : ValidInput s (appendSource s) ⟨tag.toArray⟩
  destination : ValidOutput s (appendDestination buffer length)
  separation : MemorySeparation
    [appendDescriptor s, appendDestination buffer length, Stack.region s 48]
    [appendSource s]

structure AppendPost [bindings : Bindings] (s t : RamState) (buffer : BitVec 64)
    (length : Nat) (tag : Vector UInt8 16) : Prop where
  environment : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  calleeSaved : CalleeSavedRegistersUnchanged s t
  directionFlagUnset : DirectionFlagUnset t
  grows : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  success : t.regValue .rax = 0
  frame : MemoryWriteFrame s t
    #v[⟨(s.regValue .rdi).toNat + 16, 8⟩, appendDestination buffer length, Stack.region s 48]
  lengthWord : (⟨(s.regValue .rdi).toNat + 16, 8⟩ : MemoryRegion).Word64At t.external
    (BitVec.ofNat 64 (length + 16))
  tag : (appendDestination buffer length).HasBytes t.external ⟨tag.toArray⟩

end ChaCha20Poly1305.Proofs.Encrypt
