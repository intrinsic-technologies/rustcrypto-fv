import Base16ct.Proofs.EncodeStr.Upper.Context
import Base16ct.Proofs.EncodeStr.Upper.Encoding

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

structure CalleeState [Bindings] (c : CallContext) (s : RamState) : Prop where
  invariant : RunInvariant c s
  rsp : stackPtr s = stackPtr c.initial - 32
  result : s.regValue .rax = stackPtr c.initial - 24
  returnAddress : (Operand.mem (stackPtr c.initial - 32) : Operand 64).read s = 0x100476
  rbx : s.regValue .rbx = c.initial.regValue .rdx
  savedRbx : (Operand.mem (stackPtr c.initial - 8) : Operand 64).read s = c.initial.regValue .rbx

structure LoopState [Bindings] (c : CallContext) (i : Nat) (s : RamState) : Prop
    extends CalleeState c s where
  bound : i ≤ c.input.length
  rip : s.RIP = if i < c.input.length then 0x1005f0 else 0x100641
  src : s.regValue .rsi = c.initial.regValue .rdi
  length : s.regValue .rdx = BitVec.ofNat 64 c.input.length
  dst : s.regValue .rcx = c.initial.regValue .rcx
  resultLength : s.regValue .rdi = BitVec.ofNat 64 (2 * c.input.length)
  index : s.regValue .r8 = BitVec.ofNat 64 i
  output : Bytes s.external (c.initial.regValue .rcx) (2 * i)
    (fun j => (encodedBytes c.input).getD j 0)

structure SuccessState [Bindings] (c : CallContext) (s : RamState) : Prop
    extends CalleeState c s where
  rip : s.RIP = 0x100641
  dst : s.regValue .rcx = c.initial.regValue .rcx
  resultLength : s.regValue .rdi = BitVec.ofNat 64 (2 * c.input.length)
  output : Bytes s.external (c.initial.regValue .rcx) (2 * c.input.length)
    (fun j => (encodedBytes c.input).getD j 0)

structure ErrorState [Bindings] (c : CallContext) (s : RamState) : Prop
    extends CalleeState c s where
  rip : s.RIP = 0x1005cc

end Base16ct.Proofs.EncodeStr.Upper
