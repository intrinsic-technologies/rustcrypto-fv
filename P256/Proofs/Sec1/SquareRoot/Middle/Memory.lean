import P256.Proofs.Sec1.SquareRoot.Call
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame_after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (regs : ∀ r ∈ ([3,4,13] : List (BitVec 5)), .reg r ∉ cs)
    (writes : WritesWithin cs #v[registerRegion s .rdi 40, workRegion s])
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmx : Component.mxcsr ∉ cs := by component_not_mem)
    (hfc : Component.fcw ∉ cs := by component_not_mem) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready agrees (agrees.memoryWriteFrame writes)
    (fun r hr => regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp)) hdf hmx hfc, ?_⟩
  exact (agrees.read (r := 4) (n := 64) (regs 4 (by simp))).trans state.rsp

theorem parameter_copy_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - 216) 112, .rip] t u)
    {offset len i : Nat} (ho : offset ≤ 2176) (hl : len ≤ offset + 8)
    (apart : 216 + len ≤ offset ∨ offset + 112 ≤ 216) (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hv.elim
  obtain ⟨j, hj, he⟩ := hv
  exact stack_sub_apart pre.stack (a := 216) (b := offset) (by decide) ho
    (by decide) hl (Or.symm apart) j hj i hi he.symm

end P256.Proofs.Sec1.SquareRoot.Middle
