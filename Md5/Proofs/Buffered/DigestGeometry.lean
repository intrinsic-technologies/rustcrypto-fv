import Md5.Proofs.Buffered.DigestContracts
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Output

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {input : ByteArray}

theorem DigestPrepared.stackNat (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes) :
    (stackPtr s).toNat = (stackPtr initial).toNat - 296 := by
  rw [h.stack, BitVec.toNat_sub_of_le]
  · rfl
  · have hn : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
    change 296 ≤ (stackPtr initial).toNat
    omega

theorem DigestPrepared.stackAddress (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes) {offset : Nat} (ho : offset ≤ 304) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hn := h.stackNat hs
  have hb : (stackPtr initial).toNat - 616 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616)) < 2^32 := hs.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2^64 by omega),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by omega)]

theorem DigestPrepared.stackContains (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes) {offset : Nat} (ho : offset < 304) :
    (Stack.region initial Digest.minStackBytes).Contains
      (stackPtr s + BitVec.ofNat 64 offset).toNat := by
  rw [h.stackAddress hs (by omega), h.stackNat hs]
  change (stackPtr initial).toNat - 616 ≤ (stackPtr initial).toNat - 296 + offset ∧
    (stackPtr initial).toNat - 296 + offset < (stackPtr initial).toNat - 616 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616))
  have hn : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
  omega

theorem DigestPrepared.stackReadable (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes) (offset len : Nat) (ho : offset + len ≤ 304) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  refine ⟨?_, ?_⟩
  · rw [h.stackAddress hs (by omega), h.stackNat hs]
    have hb : (stackPtr initial).toNat - 616 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616)) < 2^32 := hs.1
    have hn : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
    omega
  · intro i hi
    apply h.agrees.grow
    apply Option.isSome_iff_exists.mpr
    apply hs.2.1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.stackContains hs (by omega)

theorem DigestPrepared.frame (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes) :
    MemoryWriteFrame initial s #v[Stack.region initial Digest.minStackBytes] := by
  apply h.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [digestPreparationChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
  exact ⟨_, by simp, Block.contains_of_mem_covers hs.1 ha⟩

set_option maxRecDepth 2048 in
theorem DigestPrepared.finalizeStackSubset (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes) {a : Nat}
    (ha : (Finalize.Kind.digest.stackRegion s).Contains a) :
    (Stack.region initial Digest.minStackBytes).Contains a := by
  change (stackPtr s).toNat - 320 ≤ a ∧ a < (stackPtr s).toNat - 320 + (320 + 264) at ha
  rw [h.stackNat hs] at ha
  change (stackPtr initial).toNat - 616 ≤ a ∧
    a < (stackPtr initial).toNat - 616 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616))
  have hn : 616 ≤ (stackPtr initial).toNat := hs.2.2.1
  clear h hs
  omega

theorem DigestPrepared.finalizeSaved (h : DigestPrepared initial boundary input s)
    (hs : Stack.Valid initial Digest.minStackBytes)
    (hq : Finalize.Post .digest boundary input s t) {offset : Nat}
    (hl : 264 ≤ offset) (hh : offset + 8 ≤ 304) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  rw [hq.rsp]
  apply memLoad_congr
  intro i hi
  unfold memByte
  apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
  apply hq.frame h.pre.toStorage
  intro region hr ha
  simp only [Vector.mem_singleton] at hr
  subst region
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.stackAddress hs (by omega)] at ha
  change (stackPtr s).toNat - 320 ≤ (stackPtr s).toNat + (offset + i) ∧
    (stackPtr s).toNat + (offset + i) < (stackPtr s).toNat - 320 + (320 + 264) at ha
  have := h.pre.stackLow
  omega

theorem DigestPrepared.outputPointer (h : DigestPrepared initial boundary input s)
    (hq : Finalize.Post .digest boundary input s t) : t.regValue .rbx = initial.regValue .rdx := by
  apply Eq.trans _ h.output
  exact hq.agrees.read (n := 64) (r := 3)
    (by simp [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges])

theorem outputWritable (hCall : Digest.ValidCall bindings initial input) :
    Memory.MemWritable initial (initial.regValue .rdx) 16 := by
  apply Memory.MemWritable.of_region hCall.outputInMemory.2.1 hCall.outputInMemory.2.2
    (fun a ha hp ↦ (hCall.outputSeparation.2 _ (by simp)).2 a ha (.inr hp))
  · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem outputAvoids (hCall : Digest.ValidCall bindings initial input) :
    ∀ i < 16, ¬ InProgram (initial.regValue .rdx + BitVec.ofNat 64 i) := by
  intro i hi hp
  apply (hCall.outputSeparation.2 (Digest.outputRegion initial) (by simp)).2 _ _ (.inl hp)
  apply Block.contains_of_mem_covers hCall.outputInMemory.2.1
  refine ⟨i, hi, ?_⟩
  simp [Digest.outputRegion, registerRegion]

theorem DigestPrepared.outputFrame {u : RamState}
    (h : DigestPrepared initial boundary input s)
    (hCall : Digest.ValidCall bindings initial input)
    (hq : Finalize.Post .digest boundary input s t)
    (ho : AgreesExcept (digestOutputChanges t) t u) :
    MemoryWriteFrame t u #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] := by
  apply ho.memoryWriteFrame
  intro c hc a ha
  simp only [digestOutputChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨Stack.region initial Digest.minStackBytes, by simp, ?_⟩
    rw [hq.rsp]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add] using
      h.stackContains hCall.stackAvailable (offset := 120 + i) (by omega)
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨Stack.region initial Digest.minStackBytes, by simp, ?_⟩
    rw [hq.rsp]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, ← BitVec.ofNat_add] using
      h.stackContains hCall.stackAvailable (offset := 112 + i) (by omega)
  · refine ⟨Digest.outputRegion initial, by simp, ?_⟩
    obtain ⟨i, hi, rfl⟩ := ha
    apply Block.contains_of_mem_covers hCall.outputInMemory.2.1
    refine ⟨8 + i, by change 8 + i < 16; omega, ?_⟩
    simp only [h.outputPointer hq, Digest.outputRegion, registerRegion,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat]
  · refine ⟨Digest.outputRegion initial, by simp, ?_⟩
    apply Block.contains_of_mem_covers hCall.outputInMemory.2.1
    obtain ⟨i, hi, he⟩ := ha
    refine ⟨i, by change i < 16; omega, ?_⟩
    simpa only [h.outputPointer hq, Digest.outputRegion, registerRegion,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using he

theorem DigestPrepared.outputSaved {u : RamState}
    (h : DigestPrepared initial boundary input s)
    (hCall : Digest.ValidCall bindings initial input)
    (hq : Finalize.Post .digest boundary input s t)
    (ho : AgreesExcept (digestOutputChanges t) t u) {offset : Nat}
    (hl : 264 ≤ offset) (hh : offset + 8 ≤ 304) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read u =
      (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t := by
  apply memLoad_congr
  intro i hi
  unfold memByte
  apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
  apply ho.byte
  intro c hc ha
  simp only [digestOutputChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨j, hj, he⟩ := ha
    exact RangeApart.offsets (stackPtr t) (a := offset) (b := 120)
      (len := 8) (count := 8) (by omega) (by decide) (.inr (by omega)) i hi j hj he
  · obtain ⟨j, hj, he⟩ := ha
    exact RangeApart.offsets (stackPtr t) (a := offset) (b := 112)
      (len := 8) (count := 8) (by omega) (by decide) (.inr (by omega)) i hi j hj he
  all_goals
    have hs : (Stack.region initial Digest.minStackBytes).Contains
        (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
      rw [hq.rsp, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h.stackContains hCall.stackAvailable (by omega)
    refine hCall.outputSeparation.1 0 1 (by decide) _ ?_ hs
    apply Block.contains_of_mem_covers hCall.outputInMemory.2.1
  · obtain ⟨j, hj, he⟩ := ha
    refine ⟨8 + j, by change 8 + j < 16; omega, ?_⟩
    rw [he, h.outputPointer hq]
    simp [Digest.outputRegion, registerRegion, BitVec.ofNat_add, BitVec.add_assoc]
  · obtain ⟨j, hj, he⟩ := ha
    refine ⟨j, by change j < 16; omega, ?_⟩
    simpa only [h.outputPointer hq, Digest.outputRegion, registerRegion,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using he

end Md5.Proofs.Buffered
