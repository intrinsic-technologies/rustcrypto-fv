import P256.Proofs.Verifying.Message.Hash.Buffered
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Copied [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  rip : t.RIP = 0x10d627
  current : t.regValue .r13 = initial.regValue .rdx
  endPointer : t.regValue .r12 = initial.regValue .rdx + 16
  position : t.regValue .rbx = 0
  length : t.regValue .r15 = BitVec.ofNat 64 message.size
  buffer : (MemoryRegion.mk (frameBase initial + 472).toNat message.size).HasBytes
    t.external message
  hash : SHA256.HashStateAt t (frameBase initial + 536) SHA256.initialHash
  count : loadBytes t.external (frameBase initial + 568) 8 = .ok (0#64)
  savedKey : memLoad t.external (frameBase initial + 456) 64 = initial.regValue .rsi
  savedOutput : memLoad t.external (frameBase initial + 384) 64 = initial.regValue .rdi
  savedSignature : memLoad t.external (frameBase initial + 464) 64 = initial.regValue .r8
  stackFrame : MemoryWriteFrame initial t #v[Stack.region initial 9992]

theorem small_state {t : RamState} {address : BitVec 64} {message : ByteArray}
    (small : message.size < 64)
    (buffer : (MemoryRegion.mk address.toNat message.size).HasBytes t.external message)
    (position : t.external[address + 63]? = some (UInt8.ofNat message.size))
    (hash : SHA256.HashStateAt t (address + 64) SHA256.initialHash)
    (count : loadBytes t.external (address + 96) 8 = .ok (0#64)) :
    HMAC.Sha256StateAt t address message := by
  have quotient : message.size / 64 = 0 := Nat.div_eq_of_lt small
  have remainder : message.size % 64 = message.size := Nat.mod_eq_of_lt small
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [remainder, SHA256.remainderBytes, quotient, Nat.mul_zero,
      ByteArray.extract_zero_size] using buffer
  · simpa only [remainder] using position
  · simpa only [SHA256.compressBlocks, quotient, SHA256.compressBlocksFrom] using hash
  · simpa only [quotient] using count

end P256.Proofs.Verifying.Message.Hash.Short
