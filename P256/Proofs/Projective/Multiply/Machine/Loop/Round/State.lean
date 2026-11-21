import P256.Proofs.Projective.Multiply.Machine.Loop.Memory
import P256.Proofs.Projective.Multiply.Loop.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def digits (s : RamState) (i : Nat) : BitVec 8 :=
  memLoad s.external (s.regValue .rcx + BitVec.ofNat 64 i) 8

structure LoopState [Bindings] (s t : RamState) (table : Fin 8 → Projective)
    (n : Nat) : Prop extends FrameState s t 96 1400 376 where
  bound : n ≤ 64
  rip : t.RIP = if n < 64 then 0x103340 else 0x103425
  value : ProjectiveAt t (stackPtr s - 336) (ProjectiveLoop.accumulator table (digits s) n)
  r13 : t.regValue .r13 = stackPtr s - 336
  r14 : t.regValue .r14 = 65
  r15 : t.regValue .r15 = BitVec.ofNat 64 (64-n)
  rbx : t.regValue .rbx = s.regValue .rsi
  r9 : t.regValue .r9 = s.regValue .rcx + BitVec.ofNat 64 (64-n) - 1
  rax : t.regValue .rax = stackPtr s - 144
  count : (Operand.mem (stackPtr s - 376) : Operand 64).read t = 65
  output : (Operand.mem (stackPtr s - 360) : Operand 64).read t = s.regValue .rdi
  table : (Operand.mem (stackPtr s - 352) : Operand 64).read t = s.regValue .rsi

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
