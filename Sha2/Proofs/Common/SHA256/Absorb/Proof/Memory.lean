import Sha2.Proofs.Common.SHA256.Absorb.Proof.Geometry
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Memory
import Sha2.Proofs.Wrapper.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem Context.buffer_frame_byte [Bindings] {l : Layout} {initial s t : RamState}
    {n reserve writeOffset count i : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve)
    (frame : MemoryWriteFrame s t #v[
      ⟨(l.buffer (l.sp initial) + BitVec.ofNat 64 writeOffset).toNat, count⟩,
      ⟨(l.sp initial - 344).toNat, 344⟩])
    (writeBound : writeOffset + count ≤ 104) (bound : i < 104)
    (apart : i < writeOffset ∨ writeOffset + count ≤ i) :
    t.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? =
      s.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? := by
  have capacity := ctx.wf.capacity
  have fits := ctx.wf.bufferFits
  have stackBound := stack_valid_bounds ctx.stack
  have base := stack_frame_toNat ctx.stack (frame := l.frameBytes)
    (offset := l.bufferOffset) (by omega) (by omega)
  change (l.buffer (l.sp initial)).toNat = _ at base
  have low : (l.buffer (l.sp initial)).toNat + 104 < 2^32 :=
    stack_frame_bounded ctx.stack (by omega) fits
  have address (j : Nat) (hj : j ≤ 104) :
      (l.buffer (l.sp initial) + BitVec.ofNat 64 j).toNat =
        (l.buffer (l.sp initial)).toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  apply frame
  intro region member contains
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · change _ ≤ _ ∧ _ < _ at contains
    rw [address writeOffset (by omega), address i (by omega)] at contains
    dsimp only at contains
    omega
  · change _ ≤ _ ∧ _ < _ at contains
    have below := stack_frame_below_toNat ctx.stack capacity (below := 344)
    change (l.sp initial - 344).toNat = _ at below
    rw [below, address i (by omega), base] at contains
    dsimp only at contains
    omega

theorem Context.input_bytes [Bindings] {l : Layout} {initial s t : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {input : Input}
    (ctx : Context l initial regions reserve)
    (bytes : input.region.HasBytes s.external input.bytes) (bounded : input.region.Bounded)
    (apart : input.region.Disjoint (Stack.region initial reserve))
    (frame : PhaseFrame l (l.sp initial) s t) :
    input.region.HasBytes t.external input.bytes := by
  apply Common.Memory.hasBytes_of_frame bytes bounded frame.memory
  intro written member a ha hb
  exact apart a ha (ctx.footprint_subset written member a hb)

theorem stage_buffer_byte {l : Layout} {sp : BitVec 64} {s t : RamState} {i : Nat}
    (stage : Stage) (effect : (stage.effect l sp s).Holds s t) (bound : i < 104)
    (tail : stage ∈ [Stage.smallStore, .clearTail, .tailStore] → i ≠ 63)
    (counter : stage ∈ [Stage.increment, .addBlocks] → i < 96) :
    t.external[l.buffer sp + BitVec.ofNat 64 i]? =
      s.external[l.buffer sp + BitVec.ofNat 64 i]? := by
  have apart {offset size : Nat} (small : offset + size ≤ 104)
      (disjoint : i < offset ∨ offset + size ≤ i) :
      ¬ (Component.mem (l.buffer sp + BitVec.ofNat 64 offset) size).Covers
        (l.buffer sp + BitVec.ofNat 64 i) := by
    rintro ⟨j, hj, equal⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_right_inj] at equal
    have same := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at same
    rw [Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by omega : offset + j < 2^64)] at same
    rcases disjoint with disjoint | disjoint <;> omega
  apply effect.agrees.byte
  intro c member covered
  cases stage <;> cases hsave : l.bulkSave <;> cases hrestore : l.bufferRestore <;>
    simp only [Stage.effect, Blocks.effect, testR64R64Effect, branchEffect,
      Common.Instructions.AddByte.addR8R8Effect, Effect.components,
      List.map_cons, List.map_nil, Write.component, Operand.component,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      hsave, hrestore, Option.toList_none, Option.toList_some, List.append_nil,
      List.nil_append, List.map_append] at member
  all_goals repeat' (rcases member with member | member)
  all_goals first
    | exact covered.elim
    | exact apart (offset := 63) (size := 1) (by decide)
        (by have h := tail (by simp); omega) covered
    | exact apart (offset := 96) (size := 8) (by decide)
        (.inl (counter (by simp))) covered

theorem Context.append_buffer_copy [Bindings] {l : Layout} {initial s t : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {front back : ByteArray}
    (ctx : Context l initial regions reserve)
    (bound : front.size + back.size ≤ 64)
    (original : (⟨(l.buffer (l.sp initial)).toNat, front.size⟩ : MemoryRegion).HasBytes s.external front)
    (copied : (⟨(l.buffer (l.sp initial) + BitVec.ofNat 64 front.size).toNat, back.size⟩ : MemoryRegion).HasBytes t.external back)
    (frame : MemoryWriteFrame s t #v[
      ⟨(l.buffer (l.sp initial) + BitVec.ofNat 64 front.size).toNat, back.size⟩,
      ⟨(l.sp initial - 344).toNat, 344⟩]) :
    (⟨(l.buffer (l.sp initial)).toNat, (front ++ back).size⟩ : MemoryRegion).HasBytes t.external (front ++ back) := by
  apply Wrapper.Absorb.hasBytes_append ?_ copied
  refine ⟨rfl, ?_⟩
  intro i
  have same := ctx.buffer_frame_byte frame (by omega) (by have := i.isLt; omega) (.inl i.isLt)
  have old := original.2 i
  change s.external[BitVec.ofNat 64 ((l.buffer (l.sp initial)).toNat + i.val)]? = _ at old
  change t.external[BitVec.ofNat 64 ((l.buffer (l.sp initial)).toNat + i.val)]? = _
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at old ⊢
  exact same.trans old

end Sha2.Proofs.Common.SHA256.Absorb
