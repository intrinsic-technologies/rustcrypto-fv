import P256.Proofs.Signing.Core.Iteration.Components.Addition.State
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev workRegion (s : RamState) := ScalarFrame.workRegion s 64

theorem scalar_stack_address {s t : RamState} (hsp : stackPtr t = stackPtr s - 64)
    {offset : Nat} (h : offset ≤ 64) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (64-offset) :=
  ScalarFrame.scalar_stack_address hsp (by decide) h

theorem work_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) {offset len : Nat} {a : BitVec 64}
    (ho : offset ≤ 64) (hl : len+48 ≤ offset)
    (covered : (Component.mem (stackPtr s-BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s).Contains a.toNat := ScalarFrame.work_contains pre ho hl covered

theorem FrameState.after_effect [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary 0x113310 32 32 64)
    (state : FrameState s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 32, workRegion s])
    (sp : .reg 4 ∉ cs) (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : FrameState s u :=
  ScalarFrame.FrameState.after_effect pre (by decide) state ready agrees writes sp hdf hmxcsr hfcw

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    {offset len : Nat} (bound : offset+len ≤ 64) :
    MemReadable t (stackPtr t+BitVec.ofNat 64 offset) len :=
  ScalarFrame.stack_readable pre state (by decide) bound

theorem stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    {offset len codeOffset codeLen : Nat} (bound : offset+len ≤ 64)
    (codeBound : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr t+BitVec.ofNat 64 offset) len
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen :=
  ScalarFrame.stack_code pre state (by decide) bound codeBound

theorem writable_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    {offset : Nat} (bound : offset ≤ 15) :
    MemWritable t (stackPtr t+BitVec.ofNat 64 offset) 1 := by
  rw [scalar_stack_address state.rsp (by omega)]
  apply Program.writable_of_grow (s := s) _ state.allocated
  apply stack_sub_writable pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
    (by omega) (by omega) (by decide)
  have := Nat.mod_lt (stackPtr s-BitVec.ofNat 64 (64-offset)).toNat (by decide : 0 < 4096)
  omega

theorem writable_word [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t) :
    MemWritable t (stackPtr t) 8 := by
  rw [state.rsp]
  exact Program.writable_of_grow (stack_sub_writable8 pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) state.allocated

end P256.Proofs.Signing.Core.Iteration.Components.Addition
