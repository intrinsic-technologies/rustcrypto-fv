import Hkdf.Proofs.Standard.Finalize.Suffix.Return.Geometry

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Return

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine

theorem stores_stack [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : State initial boundary s) (effect : (Stores.effect s).Holds s t)
    {depth length : Nat} (within : depth ≤ 1264) (high : length ≤ depth + 8) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 depth) length).Agrees s t := by
  have savedMemory (offset len : Nat) (bound : offset + len ≤ 176) :
      ∀ i < length, ¬ (Component.mem (s.regValue .rbx + BitVec.ofNat 64 offset) len).Covers
        (stackPtr initial - BitVec.ofNat 64 depth + BitVec.ofNat 64 i) := by
    intro i hi covered
    obtain ⟨j, hj, equal⟩ := covered
    rw [state.rbx] at equal
    exact output_apart_stack pre bound (stackOffset := depth) (stackLen := length)
      within high j hj i hi equal.symm
  intro i hi
  apply effect.agrees.memory
  intro c member covered
  simp only [Stores.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covered.elim
  · exact covered.elim
  · exact savedMemory 24 8 (by decide) i hi covered
  · exact savedMemory 16 8 (by decide) i hi covered
  · exact savedMemory 8 8 (by decide) i hi covered
  · apply savedMemory 0 8 (by decide) i hi
    change (Component.mem (s.regValue .rbx + 0#64) 8).Covers _
    rw [BitVec.add_zero]
    exact covered
  · exact savedMemory 95 1 (by decide) i hi covered
  · exact covered.elim

theorem stores_state [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {fuel : Nat} (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : State initial boundary s) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (effect : (Stores.effect s).Holds s t) :
    State initial boundary t := by
  have writesMemory (offset len : Nat) (bound : offset + len ≤ 176) :
      ∀ a, (Component.mem (s.regValue .rbx + BitVec.ofNat 64 offset) len).Covers a →
        ∃ region ∈ #v[registerRegion initial .rdi 176, Stack.region initial 1264],
          region.Contains a.toNat := by
    intro a covered
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨registerRegion initial .rdi 176, by simp, ?_⟩
    rw [state.rbx]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      output_contains pre (offset := offset + i) (by omega)
  have writes : WritesWithin (Stores.effect s).components
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] := by
    intro c member a covered
    simp only [Stores.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact covered.elim
    · exact covered.elim
    · exact writesMemory 24 8 (by decide) a covered
    · exact writesMemory 16 8 (by decide) a covered
    · exact writesMemory 8 8 (by decide) a covered
    · apply writesMemory 0 8 (by decide) a
      change (Component.mem (s.regValue .rbx + 0#64) 8).Covers a
      rw [BitVec.add_zero]
      exact covered
    · exact writesMemory 95 1 (by decide) a covered
    · exact covered.elim
  apply state.of_agrees pre run ready effect.agrees writes
  · intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Stores.effect, Effect.components]
  · exact stores_stack pre state effect (depth := 40) (by decide) (by decide)

theorem stores_bytes [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : State initial boundary s) (effect : (Stores.effect s).Holds s t)
    (digestBytes : (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes s.external digest) :
    (registerRegion initial .rdi 32).HasBytes t.external digest := by
  have size : digest.size = 32 := digestBytes.1
  have sp : rspOf s = stackPtr initial - 408 := state.rsp
  have words : ∀ j < 4, memLoad t.external
      (initial.regValue .rdi + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (stackPtr initial - 192 + BitVec.ofNat 64 (8*j)) 64 := by
    have h := effect.writes
    change t.regValue .rax = _ ∧ t.regValue .rcx = _ ∧
      memLoad t.external (s.regValue .rbx + 24) 64 = _ ∧
      memLoad t.external (s.regValue .rbx + 16) 64 = _ ∧
      memLoad t.external (s.regValue .rbx + 8) 64 = _ ∧
      memLoad t.external (s.regValue .rbx) 64 = _ ∧ _ at h
    rw [state.rbx] at h
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, sp, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero] using h.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, sp, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero] using h.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, sp, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero] using h.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, sp, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero] using h.2.2.1
  have allocated : ∀ i < 32,
      (t.external[initial.regValue .rdi + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    exact effect.agrees.grow _ (state.running.allocated _ (Option.isSome_iff_exists.mpr
      (pre.outputAllocated _ (output_contains pre (by omega)))))
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < 32 := by omega
  have same := memByte_of_memLoad_eq (words (i.val / 8) (by omega)) (i.val % 8) (by omega)
  have index : 8 * (i.val / 8) + i.val % 8 = i.val := by omega
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, index,
    BitVec.add_assoc, ← BitVec.ofNat_add, index] at same
  have source : s.external[stackPtr initial - 192 + BitVec.ofNat 64 i.val]? = some digest[i.val] := by
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using digestBytes.2 i
  have result := Bytes.of_isSome allocated i.val hi
  dsimp only at result
  rw [same] at result
  change t.external[_]? = some ((s.external[_]?).getD 0) at result
  rw [source] at result
  simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, Option.getD_some] using result

theorem stores_tailLength [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : State initial boundary s) (effect : (Stores.effect s).Holds s t) :
    t.external[initial.regValue .rdi + 95]? = some 0 := by
  have word : memLoad t.external (s.regValue .rbx + 95) 8 = 0 :=
    effect.writes.2.2.2.2.2.2
  rw [state.rbx] at word
  have byte := Bytes.of_memLoad (m := t.external) (n := 8) (a := initial.regValue .rdi + 95)
    (fun i hi ↦ by
      have iz : i = 0 := by omega
      subst i
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      exact effect.agrees.grow _ (state.running.allocated _ (Option.isSome_iff_exists.mpr
        (pre.outputAllocated _ (output_contains pre (offset := 95) (by decide))))))
  rw [word] at byte
  have zero : storedByte (0#8) 0 = (0 : UInt8) := by decide +kernel
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, zero] using byte 0 (by decide)

end Hkdf.Proofs.Standard.Finalize.Suffix.Return
