import P256.Proofs.Program.LimbSelect.Interface
import P256.Proofs.Program.Entry
import P256.Proofs.Program.State
import P256.Proofs.Program.Code
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def registers : List Component :=
  [.reg 0, .reg 1, .reg 4, .reg 8, .reg 9, .flags, .rip]

def components (s : RamState) (count : Nat) : List Component :=
  registers ++ [.mem (stackPtr s - 72) 24, .mem (s.regValue .rdi) (8 * count)]

structure LoopState [Bindings] (s t : RamState) (select : Bool) (count : Nat) : Prop where
  ready : ReadyToStep t
  agrees : AgreesExcept (components s count) s t
  rsp : t.regValue .rsp = s.regValue .rsp - 72
  rax : t.regValue .rax = if select then 1 else 0
  rcx : t.regValue .rcx = BitVec.ofNat 64 count
  selected : ∀ i < 8 * count, t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
    if select then s.external[s.regValue .rdx + BitVec.ofNat 64 i]?
    else s.external[s.regValue .rdi + BitVec.ofNat 64 i]?

end P256.Proofs.Program.LimbSelect
