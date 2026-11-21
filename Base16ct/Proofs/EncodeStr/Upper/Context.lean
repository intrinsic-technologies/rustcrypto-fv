import Base16ct.Spec.Base16
import Base16ct.Proofs.EncodeStr.Upper.Machine

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Standards.RFC.BaseEncodings Prelude X86 X86.Machine X86Proofs

structure CallContext where
  initial : RamState
  input : List UInt8
  capacity : Nat
  valid : ValidCall base16ctUpperEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity)

def CallContext.encoded (c : CallContext) : List UInt8 :=
  (encode .base16Upper .unpadded c.input.toByteArray).data.toList

def CallContext.writeLength (c : CallContext) : Nat :=
  if 2 * c.input.length ≤ c.capacity then 2 * c.input.length else 0

theorem CallContext.writeLength_le_capacity (c : CallContext) : c.writeLength ≤ c.capacity := by
  unfold CallContext.writeLength
  split <;> omega

theorem CallContext.stack32 (c : CallContext) : Stack.Valid c.initial 32 := by
  have hs : Stack.Valid c.initial 160 := c.valid.stack
  have hn : 160 ≤ (stackPtr c.initial).toNat := hs.2.2.1
  have hb : (stackPtr c.initial).toNat - 160 +
      ((stackPtr c.initial).toNat + 8 - ((stackPtr c.initial).toNat - 160)) < 2^32 := hs.1
  refine ⟨?_, ?_, ?_, hs.2.2.2⟩
  · change (stackPtr c.initial).toNat - 32 +
      ((stackPtr c.initial).toNat + 8 - ((stackPtr c.initial).toNat - 32)) < 2^32
    omega
  · intro address ha
    apply hs.2.1 address
    change (stackPtr c.initial).toNat - 32 ≤ address.toNat ∧
      address.toNat < (stackPtr c.initial).toNat - 32 +
        ((stackPtr c.initial).toNat + 8 - ((stackPtr c.initial).toNat - 32)) at ha
    change (stackPtr c.initial).toNat - 160 ≤ address.toNat ∧
      address.toNat < (stackPtr c.initial).toNat - 160 +
        ((stackPtr c.initial).toNat + 8 - ((stackPtr c.initial).toNat - 160))
    omega
  · change 32 ≤ (stackPtr c.initial).toNat
    omega

structure RunInvariant [Bindings] (c : CallContext) (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  agrees : AgreesExcept (encoderComponents c.initial c.writeLength) c.initial s

structure CalleeEntry (c : CallContext) (s : RamState) : Prop where
  rbx : s.regValue .rbx = c.initial.regValue .rdx
  savedRbx : (Operand.mem (stackPtr c.initial - 8) : Operand 64).read s =
    c.initial.regValue .rbx
  rip : s.RIP = 0x1005c0
  rsp : stackPtr s = stackPtr c.initial - 32
  src : s.regValue .rsi = c.initial.regValue .rdi
  length : s.regValue .rdx = BitVec.ofNat 64 c.input.length
  dst : s.regValue .rcx = c.initial.regValue .rcx
  result : s.regValue .rdi = stackPtr c.initial - 24
  capacity : s.regValue .r8 = BitVec.ofNat 64 c.capacity
  returnAddress : (Operand.mem (stackPtr c.initial - 32) : Operand 64).read s = 0x100476

structure CalleeExit (c : CallContext) (s : RamState) : Prop where
  rip : s.RIP = 0x100476
  rsp : stackPtr s = stackPtr c.initial - 24
  result : if 2 * c.input.length ≤ c.capacity then
      (Operand.mem (stackPtr c.initial - 24) : Operand 64).read s =
        c.initial.regValue .rcx ∧
      (Operand.mem (stackPtr c.initial - 16) : Operand 64).read s =
        BitVec.ofNat 64 (2 * c.input.length) ∧
      readOutput c.initial s c.encoded.length = .ok c.encoded.toByteArray
    else
      (Operand.mem (stackPtr c.initial - 24) : Operand 64).read s = 0 ∧
      (Operand.mem (stackPtr c.initial - 16) : Operand 8).read s = 1

  rbx : s.regValue .rbx = c.initial.regValue .rdx
  savedRbx : (Operand.mem (stackPtr c.initial - 8) : Operand 64).read s =
    c.initial.regValue .rbx

end Base16ct.Proofs.EncodeStr.Upper
