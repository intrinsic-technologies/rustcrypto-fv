import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Memory
import Sha2.Proofs.Common.Machine.FrameMemory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

theorem Context.outside (ctx : Context l initial regions reserve) :
    ¬ InProgram (returnBoundary initial).rip :=
  (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2

theorem Context.buffer_toNat (ctx : Context l initial regions reserve) :
    (l.buffer (l.sp initial)).toNat =
      (stackPtr initial).toNat - l.frameBytes + l.bufferOffset :=
  stack_frame_toNat ctx.stack (by have := ctx.wf.capacity; omega)
    (by have := ctx.wf.bufferFits; omega)

theorem Context.below_toNat (ctx : Context l initial regions reserve) {offset : Nat}
    (bound : offset ≤ 344) :
    (l.sp initial - BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - (l.frameBytes + offset) := by
  change (stackPtr initial - BitVec.ofNat 64 l.frameBytes - BitVec.ofNat 64 offset).toNat = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact stack_valid_sub_toNat ctx.stack (by have := ctx.wf.capacity; omega)

theorem Context.buffer_bounded (ctx : Context l initial regions reserve) :
    (⟨(l.buffer (l.sp initial)).toNat, 104⟩ : MemoryRegion).Bounded :=
  stack_frame_bounded ctx.stack (by have := ctx.wf.capacity; omega) ctx.wf.bufferFits

theorem Context.readable (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat} (bound : offset + len ≤ 104) :
    MemReadable s (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len := by
  have result := stack_frame_readable ctx.stack (frame := l.frameBytes)
    (offset := l.bufferOffset + offset) (by have := ctx.wf.capacity; omega) state.allocated
    (by have := ctx.wf.bufferFits; omega : l.bufferOffset + offset + len ≤ l.frameBytes)
  simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using result

theorem Context.writable (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat}
    (bound : offset + len ≤ 104) (positive : 0 < len) :
    MemWritable s (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len := by
  have result := stack_frame_writable ctx.stack (frame := l.frameBytes)
    (offset := l.bufferOffset + offset) (by have := ctx.wf.capacity; omega)
    (fun a ha hp => ctx.avoids a ha (.inr hp)) state.allocated
    (by have := ctx.wf.bufferFits; omega : l.bufferOffset + offset + len ≤ l.frameBytes) positive
  simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using result

theorem Context.buffer_cover (ctx : Context l initial regions reserve)
    {offset len : Nat} (bound : offset + len ≤ 104) {a : BitVec 64}
    (covered : (Component.mem (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len).Covers a) :
    (⟨(l.buffer (l.sp initial)).toNat, 104⟩ : MemoryRegion).Contains a.toNat := by
  apply stack_frame_cover ctx.stack (by have := ctx.wf.capacity; omega) ctx.wf.bufferFits bound
  simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using covered

theorem Context.footprint_subset (ctx : Context l initial regions reserve) :
    ∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
      (Stack.region initial reserve).Contains a := by
  intro region member a contains
  simp only [footprint, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact stack_frame_region_subset ctx.stack (by have := ctx.wf.capacity; omega)
      ctx.wf.bufferFits contains
  · have address : l.sp initial - 344 =
        stackPtr initial - BitVec.ofNat 64 (l.frameBytes + 344) := by
      change stackPtr initial - BitVec.ofNat 64 l.frameBytes - 344 = _
      rw [BitVec.sub_sub, BitVec.ofNat_add]
      rfl
    rw [address] at contains
    exact stack_sub_region_subset ctx.stack ctx.wf.capacity (by omega) contains

theorem Context.footprint_avoids (ctx : Context l initial regions reserve) :
    ∀ region ∈ footprint l (l.sp initial), region.Avoids InProgram := by
  intro region member a contains program
  exact ctx.avoids a (ctx.footprint_subset region member a.toNat contains) (.inl program)

theorem Context.codeApart (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) (stage : Stage) {offset len : Nat}
    (bound : offset + len ≤ 104) :
    RangeApart (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len
      (l.pc stage) (l.bytes stage).length := by
  intro i hi j hj same
  apply ctx.avoids _ (ctx.footprint_subset _ (by simp [footprint]) _
    (ctx.buffer_cover bound ⟨i, hi, rfl⟩))
  apply Or.inl
  rw [same]
  exact loaded_code_inProgram state.loaded (ctx.code.blocks stage)
    (mem_codeRange _ _ j hj)

theorem Context.stage_pre (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) (stage : Stage)
    (rip : s.RIP = l.pc stage) (rsp : stackPtr s = l.sp initial) :
    stage.Pre l (l.sp initial) s :=
  ⟨rip, rsp, Common.Instructions.CrossPageStore.Writable.of_memWritable
      (ctx.writable state (by decide : 63 + 1 ≤ 104) (by decide)),
    Common.Instructions.CrossPageStore.Writable.of_memWritable
      (ctx.writable state (by decide : 96 + 8 ≤ 104) (by decide)),
    ctx.codeApart state stage (by decide : 63 + 1 ≤ 104),
    ctx.codeApart state stage (by decide : 96 + 8 ≤ 104)⟩

theorem Context.stage_writes (ctx : Context l initial regions reserve) (stage : Stage) :
    WritesWithin (stage.effect l (l.sp initial) s).components (footprint l (l.sp initial)) := by
  intro c member a covered
  cases stage
  all_goals simp only [Stage.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false,
    List.nil_append, List.cons_append] at member
  · rcases member with rfl | rfl <;> exact covered.elim
  · rcases member with rfl | rfl | rfl <;> exact covered.elim
  · rcases member with rfl | rfl
    · exact ⟨⟨(l.buffer (l.sp initial)).toNat,104⟩, by simp [footprint],
        ctx.buffer_cover (offset := 63) (len := 1) (by decide) covered⟩
    · exact covered.elim
  · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨⟨(l.buffer (l.sp initial)).toNat,104⟩, by simp [footprint],
      ctx.buffer_cover (offset := 96) (len := 8) (by decide) covered⟩
  · rcases member with rfl | rfl
    · exact ⟨⟨(l.buffer (l.sp initial)).toNat,104⟩, by simp [footprint],
        ctx.buffer_cover (offset := 63) (len := 1) (by decide) covered⟩
    · exact covered.elim
  · rcases member with rfl | rfl | rfl | rfl <;> exact covered.elim

theorem run_stage (ctx : Context l initial regions reserve) {before : RamState}
    (input : Preserved l initial before s regions) (stage : Stage) (rip : s.RIP = l.pc stage) :
    ∃ t, Preserved l initial before t regions ∧ (stage.effect l (l.sp initial) s).Holds s t := by
  obtain ⟨_, t, run, ready, _, effect⟩ := ctx.blocks.run stage (l.sp initial) s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.blocks stage s input.state.loaded)
    (ctx.stage_pre input.state stage rip input.rsp)
  exact ⟨t, input.of_agrees ctx.within ctx.footprint_avoids run ready effect.agrees
    (ctx.stage_writes stage) (stage_preserves_registers stage l _ s)
    (by cases stage <;> simp [Stage.effect, Effect.components, Write.component, Operand.component]), effect⟩

end Sha2.Proofs.Common.SHA256.Absorb.Direct
