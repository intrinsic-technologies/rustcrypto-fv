import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.NewExpand.Expand.Blocks

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LoopState [Bindings] (entry s : RamState) (boundary : ReturnBoundary)
    (key info : ByteArray) (length n : Nat) : Prop extends SavedFrame entry s boundary length where
  contextPtr : slot s 240 = entry.regValue .rdi
  descriptors : slot s 232 = entry.regValue .rsi
  count : slot s 248 = 1
  innerPtr : slot s 424 = entry.regValue .rdi + 64
  outerPtr : slot s 416 = entry.regValue .rdi + 104
  tableEnd : slot s 440 = entry.regValue .rsi + 16
  memcpy : s.regValue .r12 = 0x10dd60
  pc : s.RIP = (if 32 * n < length then 0x10f586 else 0x10f290)
  outputPtr : s.regValue .r15 = entry.regValue .rcx + BitVec.ofNat 64 (min (32 * n) length)
  remaining : s.regValue .rbp = BitVec.ofNat 64 (length - 32 * n)
  counter : slot s 256 = BitVec.ofNat 64 n
  flag : (s.regValue .rax).setWidth 8 = (if n = 0 then 0 else 1)
  previous : (⟨(s.regValue .rsp + 456).toNat, (blocks .sha256 key info n).2.size⟩ : MemoryRegion).HasBytes
    s.external (blocks .sha256 key info n).2
  output : (registerRegion entry .rcx (min (32 * n) length)).HasBytes s.external
    ((blocks .sha256 key info n).1.extract 0 length)

end Hkdf.Proofs.NewExpand.Expand
