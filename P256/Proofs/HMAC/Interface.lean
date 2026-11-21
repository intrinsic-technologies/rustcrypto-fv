import P256.Proofs.HMAC.Blocks
import P256.Proofs.Program.Interface

set_option autoImplicit false

namespace P256.Proofs.HMAC

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Sha256StateAt (s : RamState) (address : BitVec 64) (input : ByteArray) : Prop where
  buffer : (MemoryRegion.mk address.toNat (input.size % 64)).HasBytes s.external
    (SHA256.remainderBytes input)
  position : s.external[address + 63]? = some (UInt8.ofNat (input.size % 64))
  hash : SHA256.HashStateAt s (address + 64)
    (SHA256.compressBlocks SHA256.initialHash input)
  count : loadBytes s.external (address + 96) 8 = .ok (BitVec.ofNat 64 (input.size / 64))

structure HmacStateAt (s : RamState) (address : BitVec 64) (key input : ByteArray) : Prop where
  outer : (MemoryRegion.mk address.toNat 64).HasBytes s.external (keyPad key 0x5c)
  inner : Sha256StateAt s (address + 64) (keyPad key 0x36 ++ input)

structure HashCalleePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) (stateBytes reserve : Nat) : Prop extends
    CalleePre s boundary entry 32 stateBytes reserve where
  digestAvoids : (registerRegion s .rsi 32).Avoids (fun a => InProgram a ∨ InPageTables a)

structure HashCalleeResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (reserve : Nat) (output : ByteArray) : Prop extends CalleeResult s t boundary 32 reserve .rsi where
  outputBytes : (registerRegion s .rsi 32).HasBytes t.external output

structure HmacFinalizePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (key input : ByteArray) : Prop extends HashCalleePre s boundary 0x100f10 168 672 where
  keySize : key.size = 32
  inputSize : input.size = 32 ∨ input.size = 33 ∨ input.size = 97
  state : HmacStateAt s (s.regValue .rdi) key input

end P256.Proofs.HMAC
