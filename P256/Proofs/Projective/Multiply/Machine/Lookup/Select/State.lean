import P256.Proofs.Common.Machine.CallReturn
import P256.Proofs.Field.Interface
import P256.Proofs.Program.LimbSelect
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.State
import P256.Proofs.Program.Stack

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scratch (s : RamState) : BitVec 64 := stackPtr s - 40

def outputBytes (s : RamState) (select : Bool) (i : Nat) : Option UInt8 :=
  if select then s.external[s.regValue .rdx + BitVec.ofNat 64 i]?
  else s.external[s.regValue .rsi + BitVec.ofNat 64 i]?

structure SavedState [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[Stack.region s 128]
  registers : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r14, .r15], t.regValue r = s.regValue r
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  rsp : stackPtr t = scratch s
  rbx : t.regValue .rbx = s.regValue .rdi
  savedRbx : (Operand.mem (stackPtr s - 8) : Operand 64).read t = s.regValue .rbx
  returnWord : (Operand.mem (stackPtr s) : Operand 64).read t = (X86Proofs.returnBoundary s).rip

structure CallState [bindings : Bindings] (s t : RamState) (select : Bool) : Prop
    extends SavedState s t where
  rip : t.RIP = 0x1143ba
  rdi : t.regValue .rdi = scratch s
  rsi : t.regValue .rsi = 4
  rdx : t.regValue .rdx = s.regValue .rdx
  rcx : t.regValue .rcx = 4
  r8 : (t.regValue .r8).setWidth 8 = if select then 1 else 0
  copied : ∀ i < 32, t.external[scratch s + BitVec.ofNat 64 i]? =
    s.external[s.regValue .rsi + BitVec.ofNat 64 i]?
  source : ∀ i < 32, t.external[s.regValue .rdx + BitVec.ofNat 64 i]? =
    s.external[s.regValue .rdx + BitVec.ofNat 64 i]?

structure ReturnedState [bindings : Bindings] (s t : RamState) (select : Bool) : Prop
    extends SavedState s t where
  rip : t.RIP = 0x1143bf
  selected : ∀ i < 32, t.external[scratch s + BitVec.ofNat 64 i]? = outputBytes s select i

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
