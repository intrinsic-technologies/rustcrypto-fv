import P256.Proofs.Sec1.Affine.Uncompressed.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StackWrites (s : RamState) (cs : List Component) : Prop where
  memory : ∀ address len, Component.mem address len ∈ cs →
    ∃ off : Nat, address = stackPtr s + BitVec.ofNat 64 off ∧ off + len ≤ 712
  rsp : .reg 4 ∉ cs
  direction : .df ∉ cs
  mxcsr : .mxcsr ∉ cs
  fp87 : .fcw ∉ cs

theorem after_stack [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {cs : List Component} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : StackWrites t cs) : Frame s u := by
  apply state.after_effect pre.toCalleePre (by decide) ready agrees ?_
    writes.rsp writes.direction writes.mxcsr writes.fp87
  intro c hc a ha
  cases c <;> try exact ha.elim
  case mem address len =>
    obtain ⟨off, rfl, bound⟩ := writes.memory address len hc
    refine ⟨ScalarFrame.workRegion s 3360, by simp, ?_⟩
    rw [ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by omega)] at ha
    exact ScalarFrame.work_contains (offset := 760 - off) pre.toCalleePre (by omega) (by omega) ha

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
