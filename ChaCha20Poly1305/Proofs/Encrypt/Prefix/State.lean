import ChaCha20Poly1305.Proofs.Encrypt.Contract
import X86Proofs.Program.Entry

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract

structure Common [Bindings] (initial s : RamState) (key : Vector UInt8 32) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  machine : SupportedIntegerMachineState (inferInstance : Bindings).processor s
  direction : DirectionFlagUnset s
  frame : MemoryWriteFrame initial s
    #v[heapRegion encrypt initial, allocatorStateRegion, ⟨(stackPtr initial).toNat - 176, 176⟩]
  grows : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  savedRbp : (localWord initial 8).Word64At s.external (initial.regValue .rbp)
  savedR15 : (localWord initial 16).Word64At s.external (initial.regValue .r15)
  savedR14 : (localWord initial 24).Word64At s.external (initial.regValue .r14)
  savedR13 : (localWord initial 32).Word64At s.external (initial.regValue .r13)
  savedR12 : (localWord initial 40).Word64At s.external (initial.regValue .r12)
  savedRbx : (localWord initial 48).Word64At s.external (initial.regValue .rbx)
  keyBytes : ValidInput s ⟨(stackPtr initial).toNat - 80, 32⟩ ⟨key.toArray⟩

structure BeforeAlloc [Bindings] (initial s : RamState) (key : Vector UInt8 32)
    (length : Nat) : Prop extends Common initial s key where
  rip : s.RIP = 0x1017aa
  rsp : stackPtr s = stackPtr initial - 168
  rbp : s.regValue .rbp = BitVec.ofNat 64 (length + 16)
  r12 : s.regValue .r12 = initial.regValue .rcx
  r13 : s.regValue .r13 = BitVec.ofNat 64 length
  rsi : s.regValue .rsi = initial.regValue .rsi
  rdx : s.regValue .rdx = initial.regValue .rdx
  r9 : s.regValue .r9 = initial.regValue .r9
  zf : (StatusFlags.ofRFLAGS s.RFLAGS).ZF = false
  allocator : (⟨0x300000, 8⟩ : MemoryRegion).Word64At s.external (initial.regValue .r8)
  limit : (⟨0x300008, 8⟩ : MemoryRegion).Word64At s.external
    (let cap := memLoad initial.external (stackPtr initial + 24) 64
     if (initial.regValue .r8).toNat + cap.toNat < 2^64 then initial.regValue .r8 + cap
     else BitVec.allOnes 64)

structure BeforeCoreSetup [Bindings] (initial s : RamState) (key : Vector UInt8 32)
    (plaintext : ByteArray) : Prop extends Common initial s key where
  rip : s.RIP = 0x101828
  rsp : stackPtr s = stackPtr initial - 168
  rbp : s.regValue .rbp = 0
  r13 : s.regValue .r13 = BitVec.ofNat 64 plaintext.size
  r14 : s.regValue .r14 = initial.regValue .rdx
  r15 : s.regValue .r15 = initial.regValue .rsi
  rbx : s.regValue .rbx = initial.regValue .r9
  capacity : (localWord initial 168).Word64At s.external
    (BitVec.ofNat 64 (plaintext.size + 16))
  pointer : (localWord initial 160).Word64At s.external (initial.regValue .r8)
  message : ValidInput s (messageRegion (initial.regValue .r8) plaintext.size) plaintext

structure CoreState [Bindings] (initial s : RamState) (key : Vector UInt8 32)
    (plaintext : ByteArray) : Prop extends Common initial s key where
  atCore : AtCore initial s plaintext.size
  rip : s.RIP = coreEntry
  rsi : s.regValue .rsi = stackPtr initial - 80
  rdx : s.regValue .rdx = initial.regValue .rsi
  rcx : s.regValue .rcx = initial.regValue .rdx
  r8 : s.regValue .r8 = memLoad initial.external (stackPtr initial + 8) 64
  r9 : s.regValue .r9 = stackPtr initial - 104
  input : (localWord initial 104).Word64At s.external (initial.regValue .r8)
  output : (localWord initial 96).Word64At s.external (initial.regValue .r8)
  lengthWord : (localWord initial 88).Word64At s.external (BitVec.ofNat 64 plaintext.size)
  message : ValidInput s (messageRegion (initial.regValue .r8) plaintext.size) plaintext

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
