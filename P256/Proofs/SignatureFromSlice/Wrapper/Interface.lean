import P256.Spec
import P256.Proofs.Program.Interface

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec.Program.Routines P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure DecoderEntry [Bindings] (initial s : RamState) (input : ByteArray)
    (boundary : ReturnBoundary) : Prop where
  pre : CalleePre s boundary 0x109ac0 input.size 72 560
  inputBytes : (registerRegion s .rsi input.size).HasBytes s.external input
  execution : ∃ fuel, Advances boundary fuel initial s
  rsp : stackPtr s = stackPtr initial - 96
  length : s.regValue .rdx = BitVec.ofNat 64 input.size
  destination : s.regValue .rdi = stackPtr initial - 88
  output : s.regValue .rbx = initial.regValue .rcx
  capacity : s.regValue .r14 = initial.regValue .r8
  savedRbx : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .rbx
  savedR14 : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .r14
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  decoderReturn : (returnBoundary s).rip = 0x102280
  otherRegisters : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r15],
    s.regValue r = initial.regValue r
  frame : MemoryWriteFrame initial s
    #v[allocatorStateRegion, randomSourceRegion, callStack signatureFromSlice initial]
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome

end P256.Proofs.SignatureFromSlice.Wrapper
