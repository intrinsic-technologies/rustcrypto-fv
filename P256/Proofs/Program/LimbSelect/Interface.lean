import P256.Proofs.Program.Interface

set_option autoImplicit false

namespace P256.Proofs.Program.LimbSelect

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop
    extends CalleePre s boundary 0x1191c0 0 32 80 where
  leftCount : s.regValue .rsi = 4
  rightCount : s.regValue .rcx = 4
  sourceBounded : (registerRegion s .rdx 32).Bounded
  sourceAllocated : (registerRegion s .rdx 32).Allocated s.external
  sourceOutput : (registerRegion s .rdx 32).Disjoint (registerRegion s .rdi 32)
  sourceStack : (registerRegion s .rdx 32).Disjoint (Stack.region s 80)

def SelectedBytesAt (s t : RamState) (select : Bool) : Prop :=
  ∀ i < 32, t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
    if select then s.external[s.regValue .rdx + BitVec.ofNat 64 i]?
    else s.external[s.regValue .rdi + BitVec.ofNat 64 i]?

end P256.Proofs.Program.LimbSelect
