import ChaCha20Poly1305.Proofs.CoreContract

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract

def localWord (initial : RamState) (offset : Nat) : MemoryRegion :=
  ⟨(stackPtr initial).toNat - offset, 8⟩

def wrapperFrame (initial : RamState) : MemoryRegion :=
  ⟨(stackPtr initial).toNat - 176, 176⟩

structure AtCore (initial s : RamState) (length : Nat) : Prop where
  rsp : stackPtr s = stackPtr initial - 176
  returnAddress : (returnBoundary s).rip = 0x101866
  result : s.regValue .rdi = stackPtr initial - 137
  rbx : s.regValue .rbx = initial.regValue .r9
  capacity : (localWord initial 168).Word64At s.external (BitVec.ofNat 64 (length + 16))
  pointer : (localWord initial 160).Word64At s.external (initial.regValue .r8)
  lengthWord : (localWord initial 152).Word64At s.external (BitVec.ofNat 64 length)
  savedRbp : (localWord initial 8).Word64At s.external (initial.regValue .rbp)
  savedR15 : (localWord initial 16).Word64At s.external (initial.regValue .r15)
  savedR14 : (localWord initial 24).Word64At s.external (initial.regValue .r14)
  savedR13 : (localWord initial 32).Word64At s.external (initial.regValue .r13)
  savedR12 : (localWord initial 40).Word64At s.external (initial.regValue .r12)
  savedRbx : (localWord initial 48).Word64At s.external (initial.regValue .rbx)
  frame : MemoryWriteFrame initial s
    #v[heapRegion encrypt initial, allocatorStateRegion, wrapperFrame initial]
  grows : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome

theorem message_length {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt s [key, nonce, aad, msg]) :
    messageBytes encrypt s = msg.size := by
  have hslot : StackArgument s 1 (BitVec.ofNat 64 msg.size) := hc.lengthArgumentsMatchInputs.2.2.2.1
  have hsrc : (registerRegion s .rcx msg.size).Bounded := hc.inputsInMemory.2.2.2.1.1
  change (s.regValue .rcx).toNat + msg.size < 2^32 at hsrc
  change (match loadBytes s.external (BitVec.ofNat 64 (stackArgumentSlot s 1).start) 8 with
    | .ok value => value.toNat | .error _ => 0) = msg.size
  rw [hslot.2.2]
  exact Nat.mod_eq_of_lt (by omega)

theorem heap_region {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt s [key, nonce, aad, msg]) :
    heapRegion encrypt s = registerRegion s .r8 (msg.size + 16) := by
  change registerRegion s .r8 (messageBytes encrypt s + 16) = _
  rw [message_length hc]

theorem output_region {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall encrypt s [key, nonce, aad, msg]) :
    outputRegion encrypt s = registerRegion s .r9 (msg.size + 16) := by
  have room : hasRoom encrypt s = true := by
    simp [hasRoom, bufferBytes, encrypt, Routine.inPlace]
  simp only [outputRegion, room, ↓reduceIte]
  change registerRegion s .r9 (messageBytes encrypt s + 16) = _
  rw [message_length hc]

end ChaCha20Poly1305.Proofs.Encrypt
