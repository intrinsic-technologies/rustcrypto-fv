import P256.Proofs.Sec1.SquareRoot.PrepareInterface
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem stack_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len pc n : Nat}
    (ho : offset ≤ 2176) (hl : len ≤ offset + 8) (hc : pc + n ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 pc) n := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 2176) (by simp) _
    (ScalarFrame.stack_contains pre ho hl ⟨i, hi, rfl⟩)
  apply Or.inl
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (pc+j) (by omega)

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {offset len : Nat} (bound : offset + len ≤ 32) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) len := by
  apply readable_of_grow (s := s) _ grow
  have bounded : (s.regValue .rsi).toNat + 32 < 2^32 := pre.inputBounded
  have addr : (s.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rsi).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · change (s.regValue .rsi).toNat ≤ _
    rw [addr]; omega
  · change _ + len ≤ (s.regValue .rsi).toNat + 32
    rw [addr]; omega

theorem stack_input [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len : Nat}
    (ho : offset ≤ 2176) (hl : len ≤ offset + 8) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len (s.regValue .rsi) 32 := by
  intro i hi j hj he
  apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hj)
  rw [← he]
  exact ScalarFrame.stack_contains pre ho hl ⟨i, hi, rfl⟩

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

end P256.Proofs.Sec1.SquareRoot.Prepare
