import P256.Proofs.Signing.Core.NextNonce.Memory
import P256.Proofs.Program.ScalarFrame.Input
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open NextNonce (scalarFrame coreFrame base_add base_nat)
open SecretKeyFromBytes.Scalar (Nat256At)

def LocalWrites (s : RamState) (cs : List Component) : Prop :=
  ∀ c ∈ cs, ∀ a, c.Covers a → ∃ offset < 2232, a = frameBase s + BitVec.ofNat 64 offset

theorem after_effect [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u) (writes : LocalWrites s cs)
    (sp : .reg 4 ∉ cs) (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fp87 : Component.fcw ∉ cs := by component_not_mem) : Frame s u := by
  apply coreFrame ((scalarFrame frame).after_effect pre.toCalleePre (by decide)
    ready agrees ?_ sp df mxcsr fp87)
  intro c hc a ha
  obtain ⟨off, bound, rfl⟩ := writes c hc a ha
  refine ⟨ScalarFrame.workRegion s 4584, by simp, ?_⟩
  rw [base_add s (by omega)]
  exact ScalarFrame.work_contains pre.toCalleePre (offset := 2280-off) (len := 1)
    (by omega) (by omega) ⟨0, by decide, by simp⟩

theorem writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) {off : Nat}
    (bound : off+8 ≤ 2280) (aligned : off % 8 = 0) :
    MemWritable t (stackPtr t + BitVec.ofNat 64 off) 8 := by
  apply (ScalarFrame.stack_writable pre.toCalleePre (scalarFrame frame)
    (by decide) bound (by decide)).toMemWritable ?_ (by decide)
  rw [frame.rsp, base_nat pre (by omega)]
  have bottom := stack_bounds pre.stack
  have rem : (stackPtr s).toNat % 8 = 0 := by
    have h := pre.stack.2.2.2
    change (stackPtr s).toNat % 16 = 8 at h
    omega
  omega

theorem scalar_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : SignPre s boundary)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 65, Stack.region s 4584])
    (value : Nat256At s (s.regValue .rsi) x) : Nat256At t (s.regValue .rsi) x := by
  refine ⟨value.1, fun i hi => ?_⟩
  rw [frame _]
  · exact value.2 i hi
  · intro region hr hin
    have inside := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
    have cases : region = registerRegion s .rdi 65 ∨ region = Stack.region s 4584 := by simpa using hr
    rcases cases with rfl | rfl
    · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ inside hin
    · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ inside hin

end P256.Proofs.Signing.Core.Initialize
