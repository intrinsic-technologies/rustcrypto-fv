import P256.Proofs.Signing.Core.State
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

structure Encoded [Bindings] (s t : RamState) (scalar : Nat) : Prop where
  frame : Frame s t
  output : (Operand.mem (frameBase s + 72) : Operand 64).read t = s.regValue .rdi
  secret : (Operand.mem (frameBase s + 80) : Operand 64).read t = s.regValue .rsi
  order : Nat256At t (frameBase s + 272) Operations.domain.n
  bytes : Bytes t.external (frameBase s + 528) 32
    (fun i => UInt8.ofNat (scalar / 256^(31-i) % 256))
  rbp : t.regValue .rbp = frameBase s + 528
  r13 : t.regValue .r13 = s.regValue .rdx
  r12 : t.regValue .r12 = 32
  r14 : t.regValue .r14 = 1
  rbx : t.regValue .rbx = 0

structure CallInput [Bindings] (s t : RamState) (scalar : Nat) : Prop where
  frame : Frame s t
  output : (Operand.mem (frameBase s + 72) : Operand 64).read t = s.regValue .rdi
  secret : (Operand.mem (frameBase s + 80) : Operand 64).read t = s.regValue .rsi
  digest : (Operand.mem (frameBase s + 88) : Operand 64).read t = s.regValue .rdx
  order : Nat256At t (frameBase s + 272) Operations.domain.n
  bytes : Bytes t.external (frameBase s + 528) 32
    (fun i => UInt8.ofNat (scalar / 256^(31-i) % 256))
  rax : t.regValue .rax = frameBase s + 272
  rdi : t.regValue .rdi = frameBase s + 2160
  rsi : t.regValue .rsi = frameBase s + 528
  rdx : t.regValue .rdx = 32
  rcx : t.regValue .rcx = s.regValue .rdx
  r8 : t.regValue .r8 = 32
  r9 : t.regValue .r9 = 1
  rbx : t.regValue .rbx = 0
  r12 : t.regValue .r12 = 32
  rbp : t.regValue .rbp = frameBase s + 528
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = 32

structure Initialized [Bindings] (s t : RamState) (state : Nonce.State) : Prop where
  frame : Frame s t
  output : (Operand.mem (frameBase s + 72) : Operand 64).read t = s.regValue .rdi
  secret : (Operand.mem (frameBase s + 80) : Operand 64).read t = s.regValue .rsi
  digest : (Operand.mem (frameBase s + 88) : Operand 64).read t = s.regValue .rdx
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  r12 : t.regValue .r12 = 32
  rbp : t.regValue .rbp = frameBase s + 528
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = 32

end P256.Proofs.Signing.Core.Initialize
