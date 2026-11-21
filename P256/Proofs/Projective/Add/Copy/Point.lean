import P256.Proofs.Projective.Add.Copy.Stack
set_option autoImplicit false


namespace P256.Proofs.Projective.Add.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem point_region [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (r : Syntax.Reg)
    (hr : r = .rdi ∨ r = .rsi) :
    (registerRegion s r 96).Bounded ∧ (registerRegion s r 96).Allocated s.external ∧
      (registerRegion s r 96).Disjoint (Stack.region s 920) := by
  rcases hr with rfl | rfl
  · exact ⟨pre.outputBounded, pre.outputAllocated,
      pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)⟩
  · exact ⟨pre.inputBounded, pre.inputAllocated,
      pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)⟩

theorem point_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (r : Syntax.Reg) (hr : r = .rdi ∨ r = .rsi) {offset len : Nat}
    (bound : offset + len ≤ 96) :
    MemReadable t (s.regValue r + BitVec.ofNat 64 offset) len := by
  have data := point_region pre r hr
  have whole : MemReadable s (s.regValue r) 96 :=
    memoryRegion_memReadable data.1 data.2.1 (Nat.le_refl _) (Nat.le_refl _)
  exact readable_of_grow (P256.Proofs.Common.Memory.memReadable_sub whole offset len bound) state.allocated

theorem stack_point_apart [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (r : Syntax.Reg) (hr : r = .rdi ∨ r = .rsi) {pointOffset stackOffset : Nat}
    (pointBound : pointOffset + 32 ≤ 96) (stackBound : stackOffset + 32 ≤ 632) :
    RangeApart (stackPtr t + BitVec.ofNat 64 stackOffset) 32
      (s.regValue r + BitVec.ofNat 64 pointOffset) 32 := by
  have data := point_region pre r hr
  rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega)]
  intro i hi j hj he
  have hs : (Stack.region s 920).Contains
      (stackPtr s - BitVec.ofNat 64 (632-stackOffset) + BitVec.ofNat 64 i).toNat :=
    stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩
  have hp : (registerRegion s r 96).Contains
      (s.regValue r + BitVec.ofNat 64 pointOffset + BitVec.ofNat 64 j).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add data.1 (Nat.le_refl _) (Nat.le_refl _) (by change pointOffset + j < 96; omega)
  rw [he] at hs
  exact data.2.2 _ hp hs

theorem point_of_stack [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (r : Syntax.Reg)
    (hr : r = .rdi ∨ r = .rsi) {point : Projective}
    (frame : MemoryWriteFrame t u #v[Stack.region s 920])
    (input : ProjectiveAt t (s.regValue r) point) : ProjectiveAt u (s.regValue r) point := by
  apply input.of_bytes_eq
  intro i hi
  apply frame
  intro region hregion hin
  have he : region = Stack.region s 920 := by simpa using hregion
  subst region
  have data := point_region pre r hr
  exact data.2.2 _ (memoryRegion_contains_add data.1 (Nat.le_refl _) (Nat.le_refl _) hi) hin

theorem work_stack_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (frame : MemoryWriteFrame t u #v[workRegion s 920]) :
    MemoryWriteFrame t u #v[Stack.region s 920] := by
  intro a ha
  apply frame
  intro region hregion hin
  have he : region = workRegion s 920 := by simpa using hregion
  subst region
  apply ha (Stack.region s 920) (by simp)
  change (stackPtr s).toNat - 920 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 920 + 872 at hin
  change (Stack.region s 920).start ≤ a.toNat ∧
    a.toNat < (Stack.region s 920).start + (Stack.region s 920).size
  rw [stack_region_end]
  change (stackPtr s).toNat - 920 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat + 8
  have hb := stack_bounds pre.stack
  constructor <;> omega

end P256.Proofs.Projective.Add.Copy
