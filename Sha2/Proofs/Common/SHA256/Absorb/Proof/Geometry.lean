import Sha2.Proofs.Common.SHA256.Absorb.Proof.Context
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Code

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

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
      simp only [Layout.sp, BitVec.ofNat_add, BitVec.sub_sub, BitVec.ofNat_eq_ofNat]
    rw [address] at contains
    exact stack_sub_region_subset ctx.stack ctx.wf.capacity (by omega) contains

theorem Context.footprint_avoids (ctx : Context l initial regions reserve) :
    ∀ region ∈ footprint l (l.sp initial), region.Avoids InProgram := by
  intro region member a contains program
  exact ctx.avoids a (ctx.footprint_subset region member a.toNat contains) (.inl program)

theorem Context.buffer_cover (ctx : Context l initial regions reserve)
    {offset len : Nat} (bound : offset + len ≤ 104) {a : BitVec 64}
    (covered : (Component.mem (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len).Covers a) :
    (⟨(l.buffer (l.sp initial)).toNat, 104⟩ : MemoryRegion).Contains a.toNat := by
  apply stack_frame_cover ctx.stack (by have := ctx.wf.capacity; omega) ctx.wf.bufferFits bound
  simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using covered

theorem Context.buffer_writable (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) {offset len : Nat}
    (bound : offset + len ≤ 104) (positive : 0 < len) :
    Common.Instructions.CrossPageStore.Writable s
      (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len := by
  apply Common.Instructions.CrossPageStore.Writable.of_memWritable
  simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using
    (stack_frame_writable ctx.stack (frame := l.frameBytes) (offset := l.bufferOffset + offset)
      (by have := ctx.wf.capacity; omega)
      (fun a ha hp => ctx.avoids a ha (.inr hp)) state.allocated
      (by have := ctx.wf.bufferFits; omega) positive)

theorem Context.stage_codeApart (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) (stage : Stage) {site : Blocks.Site}
    (member : site ∈ l.blocks stage) {offset len : Nat} (bound : offset + len ≤ 104) :
    RangeApart (l.buffer (l.sp initial) + BitVec.ofNat 64 offset) len
      site.pc (Blocks.bytes site.block).length := by
  have inside : ∀ j < (Blocks.bytes site.block).length,
      InProgram (site.pc + BitVec.ofNat 64 j) := by
    intro j hj
    apply Direct.loaded_code_inProgram state.loaded (ctx.code.blocks stage)
    exact List.mem_flatMap.mpr ⟨site, member, mem_codeRange _ _ j hj⟩
  simpa only [Layout.buffer, Layout.sp, BitVec.ofNat_add, BitVec.add_assoc] using
    (stack_frame_codeApart ctx.stack (frame := l.frameBytes) (offset := l.bufferOffset + offset)
      (by have := ctx.wf.capacity; omega)
      (fun a ha hp => ctx.avoids a ha (.inl hp))
      (by have := ctx.wf.bufferFits; omega) inside)

end Sha2.Proofs.Common.SHA256.Absorb
