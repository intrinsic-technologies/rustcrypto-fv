import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Calls

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s t : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n}

theorem Context.buffer_part_toNat (ctx : Context l initial regions reserve)
    {offset : Nat} (bound : offset ≤ 104) :
    (l.buffer (l.sp initial)+BitVec.ofNat 64 offset).toNat =
      (l.buffer (l.sp initial)).toNat+offset := by
  have low : (l.buffer (l.sp initial)).toNat+104 < 2^32 := ctx.buffer_bounded
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]

theorem Context.frame_keeps_buffer (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions) {written width offset len : Nat}
    (frame : MemoryWriteFrame s t #v[
      ⟨(l.buffer (l.sp initial)+BitVec.ofNat 64 written).toNat,width⟩,
      ⟨(l.sp initial-344).toNat,344⟩])
    (readBound : offset+len≤104) (writeBound : written+width≤104)
    (apart : offset+len≤written ∨ written+width≤offset) :
    ∀ i<len, t.external[l.buffer (l.sp initial)+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      s.external[l.buffer (l.sp initial)+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply Table.frame_byte frame (ctx.readable state readBound) ?_ hi
  intro region member a ha hb
  have cases : region = (⟨(l.buffer (l.sp initial)+BitVec.ofNat 64 written).toNat,width⟩ : MemoryRegion) ∨
      region = (⟨(l.sp initial-344).toNat,344⟩ : MemoryRegion) := by simpa using member
  change (l.buffer (l.sp initial)+BitVec.ofNat 64 offset).toNat≤a ∧
    a<(l.buffer (l.sp initial)+BitVec.ofNat 64 offset).toNat+len at ha
  rw [ctx.buffer_part_toNat (by omega)] at ha
  rcases cases with rfl | rfl
  · change (l.buffer (l.sp initial)+BitVec.ofNat 64 written).toNat≤a ∧
      a<(l.buffer (l.sp initial)+BitVec.ofNat 64 written).toNat+width at hb
    rw [ctx.buffer_part_toNat (by omega)] at hb
    rcases apart with apart | apart <;> omega
  · change (l.sp initial-344).toNat≤a ∧ a<(l.sp initial-344).toNat+344 at hb
    have callStack : (l.sp initial-344).toNat=(stackPtr initial).toNat-(l.frameBytes+344) := by
      simpa using ctx.below_toNat (by decide : 344≤344)
    rw [callStack] at hb
    rw [ctx.buffer_toNat] at ha
    have capacity := ctx.wf.capacity
    have bounds := stack_valid_bounds ctx.stack
    omega

theorem Context.store_frame (ctx : Context l initial regions reserve) (stage : Stage)
    (choice : stage = .smallStore ∨ stage = .bulkTail ∨ stage = .bulkSetup)
    (effect : (stage.effect l (l.sp initial) s).Holds s t) :
    MemoryWriteFrame s t #v[
      ⟨(l.buffer (l.sp initial)+BitVec.ofNat 64 (if stage = .bulkSetup then 96 else 63)).toNat,
        if stage = .bulkSetup then 8 else 1⟩,
      ⟨(l.sp initial-344).toNat,344⟩] := by
  have cover {offset len : Nat} (bound : offset+len≤104) {a : BitVec 64}
      (covered : (Component.mem (l.buffer (l.sp initial)+BitVec.ofNat 64 offset) len).Covers a) :
      (⟨(l.buffer (l.sp initial)+BitVec.ofNat 64 offset).toNat,len⟩ : MemoryRegion).Contains a.toNat := by
    obtain ⟨i,hi,rfl⟩ := covered
    apply memoryRegion_contains_add (len := len) ?_ (Nat.le_refl _) (Nat.le_refl _) hi
    change (l.buffer (l.sp initial)+BitVec.ofNat 64 offset).toNat+len<2^32
    rw [ctx.buffer_part_toNat (by omega)]
    have bounded : (l.buffer (l.sp initial)).toNat+104<2^32 := ctx.buffer_bounded
    omega
  apply effect.agrees.memoryWriteFrame
  intro c member a covered
  rcases choice with rfl | rfl | rfl
  all_goals simp only [Stage.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component,Operand.component,List.mem_cons,List.not_mem_nil,or_false,
    List.nil_append,List.cons_append] at member
  · rcases member with rfl | rfl
    · exact ⟨⟨(l.buffer (l.sp initial)+63).toNat,1⟩,by simp,
        cover (offset := 63) (len := 1) (by decide) covered⟩
    · exact covered.elim
  · rcases member with rfl | rfl
    · exact ⟨⟨(l.buffer (l.sp initial)+63).toNat,1⟩,by simp,
        cover (offset := 63) (len := 1) (by decide) covered⟩
    · exact covered.elim
  · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨⟨(l.buffer (l.sp initial)+96).toNat,8⟩,by simp,
      cover (offset := 96) (len := 8) (by decide) covered⟩

theorem Preserved.input_bytes (ctx : Context l initial regions reserve)
    {before : RamState} (input : Preserved l initial before s regions) {source : Input}
    (bytes : source.region.HasBytes before.external source.bytes) (bounded : source.region.Bounded)
    (apart : source.region.Disjoint (Stack.region initial reserve)) :
    source.region.HasBytes s.external source.bytes := by
  apply Common.Memory.hasBytes_of_frame bytes bounded input.memory
  intro region member a ha hb
  exact apart a ha (ctx.footprint_subset region member a hb)

end Sha2.Proofs.Common.SHA256.Absorb.Direct
