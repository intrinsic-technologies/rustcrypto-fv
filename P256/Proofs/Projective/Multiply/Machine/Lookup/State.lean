import P256.Proofs.Projective.Multiply.Machine.Lookup.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs ProjectiveLookup

structure ScanState [Bindings] (s t : RamState) (digit : BitVec 8) : Prop extends
    FrameState s t where
  rip : t.RIP = 0x1044ed
  value : ProjectiveAt t (stackPtr s - 344) Projective.identity
  magnitude : (t.regValue .r15).setWidth 8 = BitVec.ofNat 8 (digitMagnitude digit)
  r13 : t.regValue .r13 = s.regValue .rsi
  rbp : t.regValue .rbp = stackPtr s - 344
  r14 : t.regValue .r14 = stackPtr s - 216
  digit : (Operand.mem (stackPtr s - 348) : Operand 32).read t =
    (s.regValue .rdx).setWidth 32
  output : (Operand.mem (stackPtr s - 152) : Operand 64).read t = s.regValue .rdi

structure SignState [Bindings] (s t : RamState) (table : Fin 8 → Projective)
    (digit : BitVec 8) : Prop extends FrameState s t where
  rip : t.RIP = 0x10482d
  value : ProjectiveAt t (stackPtr s - 344) (selectMagnitude table (digitMagnitude digit))
  r14 : t.regValue .r14 = stackPtr s - 344
  digit : (Operand.mem (stackPtr s - 348) : Operand 32).read t =
    (s.regValue .rdx).setWidth 32
  output : (Operand.mem (stackPtr s - 152) : Operand 64).read t = s.regValue .rdi


end P256.Proofs.Projective.Multiply.Machine.Lookup
