import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Data

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

structure Context [bindings : Bindings] (l : Layout) (initial : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (reserve : Nat) : Prop where
  wf : WellFormed l reserve
  flow : Absorb.Flow l.chunk
  chunkCode : Absorb.CodeFacts l.chunk
  targets : Absorb.CallTargets l.chunk
  chunkBlocks : Absorb.BlockContracts l.chunk (returnBoundary initial)
  chunkCorrect : Absorb.Contract l.chunk
  code : CodeFacts l
  blocks : BlockContracts l (returnBoundary initial)
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings initial
  stack : Stack.Valid initial reserve
  avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a)
  returnAddress : ValidReturnAddress initial
  within : ∀ region ∈ footprint l (l.chunk.sp initial), ∀ a, region.Contains a →
    ∃ outer ∈ regions, outer.Contains a

variable [Bindings] {l : Layout} {initial s t : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n}

theorem Context.footprint_avoids (ctx : Context l initial regions reserve) :
    ∀ region ∈ footprint l (l.chunk.sp initial), region.Avoids InProgram := by
  intro region member a ha hp
  exact ctx.avoids a (footprint_subset_stack ctx.wf ctx.stack region member a.toNat ha) (.inl hp)

theorem Context.after_block (ctx : Context l initial regions reserve)
    {fuel : Nat} {components : List Component}
    (state : ExecutionState initial s regions)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (df : .df ∉ components)
    (frame : MemoryWriteFrame s t (footprint l (l.chunk.sp initial))) :
    ExecutionState initial t regions :=
  execution_of_frame state run ready agrees df frame ctx.footprint_avoids ctx.within

theorem Context.readable (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat}
    (fits : offset + len ≤ l.chunk.frameBytes) :
    MemReadable s (l.chunk.sp initial + BitVec.ofNat 64 offset) len :=
  stack_frame_readable ctx.stack (by have := ctx.wf.chunk.capacity; omega) state.allocated fits

theorem Context.writable (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat}
    (fits : offset + len ≤ l.chunk.frameBytes) (positive : 0 < len) :
    Common.Instructions.CrossPageStore.Writable s
      (l.chunk.sp initial + BitVec.ofNat 64 offset) len :=
  Common.Instructions.CrossPageStore.Writable.of_memWritable
    (stack_frame_writable ctx.stack (by have := ctx.wf.chunk.capacity; omega)
      (fun a ha hp => ctx.avoids a ha (.inr hp)) state.allocated fits positive)

theorem Context.chunk_within (ctx : Context l initial regions reserve) :
    ∀ region ∈ Absorb.footprint l.chunk (l.chunk.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a := by
  intro region member a ha
  apply ctx.within region ?_ a ha
  simp only [Absorb.footprint, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [footprint]

end Sha2.Proofs.Common.SHA256.Absorb.Table
