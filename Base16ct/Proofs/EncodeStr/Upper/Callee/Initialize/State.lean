import Base16ct.Proofs.EncodeStr.Upper.Callee.State

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

structure InitializeState [Bindings] (c : CallContext) (s : RamState) : Prop
    extends CalleeState c s where
  src : s.regValue .rsi = c.initial.regValue .rdi
  length : s.regValue .rdx = BitVec.ofNat 64 c.input.length
  dst : s.regValue .rcx = c.initial.regValue .rcx
  resultLength : s.regValue .rdi = BitVec.ofNat 64 (2 * c.input.length)

end Base16ct.Proofs.EncodeStr.Upper
