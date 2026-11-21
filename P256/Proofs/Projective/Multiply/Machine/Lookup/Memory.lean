import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev workRegion (s : RamState) := ScalarFrame.workRegion s 496

theorem stack_address {s t : RamState} (sp : stackPtr t = stackPtr s-360)
    {offset : Nat} (bound : offset ≤ 360) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s-BitVec.ofNat 64 (360-offset) :=
  ScalarFrame.scalar_stack_address (frameOffset := 360) sp (by decide) bound

theorem work_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) {offset len : Nat} {a : BitVec 64}
    (bound : offset ≤ 496) (saved : len+48 ≤ offset)
    (covered : (Component.mem (stackPtr s-BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s).Contains a.toNat := ScalarFrame.work_contains pre bound saved covered

theorem after [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {cs : List Component}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 96,workRegion s])
    (sp : .reg 4 ∉ cs) (df : .df ∉ cs := by component_not_mem)
    (mx : .mxcsr ∉ cs := by component_not_mem) (fcw : .fcw ∉ cs := by component_not_mem) :
    FrameState s u :=
  ScalarFrame.FrameState.after_effect (frameOffset := 360) pre (by decide) state ready agrees writes sp df mx fcw

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    {offset len : Nat} (bound : offset+len ≤ 360) :
    MemReadable t (stackPtr t+BitVec.ofNat 64 offset) len :=
  ScalarFrame.stack_readable (frameOffset := 360) pre state (by decide) bound

theorem stack_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    {offset len : Nat} (bound : offset+len ≤ 360) (positive : 0<len) :
    Common.Instructions.CrossPageStore.Writable t (stackPtr t+BitVec.ofNat 64 offset) len :=
  ScalarFrame.stack_writable (frameOffset := 360) pre state (by decide) bound positive

theorem stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    {offset len codeOffset codeLen : Nat} (bound : offset+len ≤ 360)
    (codeBound : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr t+BitVec.ofNat 64 offset) len
      (P256.Spec.Program.Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen :=
  ScalarFrame.stack_code (frameOffset := 360) pre state (by decide) bound codeBound

end P256.Proofs.Projective.Multiply.Machine.Lookup
