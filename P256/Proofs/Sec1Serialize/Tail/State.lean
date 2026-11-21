import P256.Proofs.Sec1Serialize.State

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def bufferRegion (s : RamState) (offset : Nat) : MemoryRegion :=
  ⟨(stackPtr s - BitVec.ofNat 64 offset).toNat, 65⟩

def selectionBytes (infinity : Bool) (bytes : ByteArray) : ByteArray :=
  if infinity then ⟨Array.replicate 65 0⟩ else bytes

structure EncodedEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) (infinity : Bool) : Prop where
  state : FrameState s t 65 328 312
  execution : ∃ n, Advances boundary n s t
  rip : t.RIP = 0x1110cc
  destination : t.regValue .rbp = s.regValue .rdi
  source : (bufferRegion s 113).HasBytes t.external bytes
  savedInput : (Operand.mem (stackPtr s - 192) : Operand 64).read t = s.regValue .rsi
  inputFlag : t.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0)

structure SelectionEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) (infinity : Bool) : Prop where
  state : FrameState s t 65 328 312
  execution : ∃ n, Advances boundary n s t
  rip : t.RIP = 0x1111a0
  choice : (t.regValue .rax).setWidth 8 = if infinity then 1 else 0
  index : t.regValue .rdx = 0
  destination : t.regValue .rbp = s.regValue .rdi
  source : (bufferRegion s 113).HasBytes t.external bytes
  zeroSource : (bufferRegion s 184).HasBytes t.external ⟨Array.replicate 65 0⟩

structure SelectionExit [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop where
  state : FrameState s t 65 328 312
  execution : ∃ n, Advances boundary n s t
  rip : t.RIP = 0x1111ce
  destination : t.regValue .rbp = s.regValue .rdi
  selected : (bufferRegion s 296).HasBytes t.external bytes

end P256.Proofs.Sec1Serialize
