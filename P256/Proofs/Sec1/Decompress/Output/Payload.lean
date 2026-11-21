import P256.Proofs.Sec1.Decompress.Output.CopyData
import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x11005f) : CopyPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    have bound : i.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    change MemReadable t (stackPtr t + i) 8
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      ScalarFrame.stack_readable pre state (by decide) bound
  · intro i hi
    have bound : i.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (stackPtr t + i) 8
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      ScalarFrame.stack_writable pre state (by decide) bound (by decide)
  · intro i hi off len hc
    have bound : i.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    change RangeApart (stackPtr t + i) 8 _ len
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      ScalarFrame.stack_code pre state (by decide) bound hc

def copyComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s - 408) 32]

theorem copy_payload [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x11005f) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11008f ∧
      (∀ i < 32, u.external[stackPtr s - 408 + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - 288 + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (copyComponents s) t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := copy_run boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1005f copyBytes
      (by decide) (by decide +kernel)) (copy_pre pre state rip)
  have agrees : AgreesExcept (copyComponents s) t u := by
    simpa only [components, state.rsp, copyComponents] using frame effect
  have writes : WritesWithin (copyComponents s)
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨_, by simp, ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  have finalState := state.after_effect pre (by decide) ready agrees writes (by simp [copyComponents])
  refine ⟨fuel, u, run, finalState, effect.rip, ?_, agrees⟩
  have source := ScalarFrame.stack_readable pre state (offset := 120) (len := 32) (by decide) (by decide)
  have dest := ScalarFrame.stack_readable pre finalState (offset := 0) (len := 32) (by decide) (by decide)
  have hs : stackPtr t + 120 = stackPtr s - 288 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have hd : MemReadable u (stackPtr t) 32 := by
    rw [BitVec.add_zero, finalState.rsp] at dest
    rw [state.rsp]
    exact dest
  intro i hi
  have hb := copy_bytes effect source hd i hi
  rw [hs, state.rsp] at hb
  exact hb

theorem copy_keeps_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592)
    (agrees : AgreesExcept (copyComponents s) t u) {offset len i : Nat}
    (ho : offset ≤ 376) (hl : len ≤ offset + 8) (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  obtain ⟨j, hj, he⟩ := hv
  exact stack_sub_apart pre.stack (a := 408) (b := offset)
    (by decide) (by omega) (by decide) hl (.inl (by omega)) j hj i hi he.symm

end P256.Proofs.Sec1.Decompress.Output
