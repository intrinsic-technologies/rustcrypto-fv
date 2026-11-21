import P256.Proofs.Sec1Serialize.Tail.State

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure Preparing [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) (infinity : Bool) : Prop where
  state : FrameState s t 65 328 312
  execution : ∃ n, Advances boundary n s t
  destination : t.regValue .rbp = s.regValue .rdi
  source : (bufferRegion s 113).HasBytes t.external bytes
  savedInput : (Operand.mem (stackPtr s - 192) : Operand 64).read t = s.regValue .rsi
  inputFlag : t.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0)

  zeroSource : (bufferRegion s 184).HasBytes t.external ⟨Array.replicate 65 0⟩

end P256.Proofs.Sec1Serialize
