import P256.Proofs.Sec1.SquareRoot.Square.Wide.Prologue
import P256.Proofs.Program.Stack
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add memoryRegion_memReadable)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field.SquareRoot

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entry : BitVec 64}

omit [Bindings] in
theorem scratch_address (s : RamState) {offset : Nat} (ho : offset ≤ 88) :
    stackPtr s - 88 + BitVec.ofNat 64 offset =
      stackPtr s - BitVec.ofNat 64 (88-offset) := by
  have he : (88 : BitVec 64) = BitVec.ofNat 64 (88-offset) + BitVec.ofNat 64 offset := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel ho]
    rfl
  rw [he, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem scratch_inside (pre : CalleePre s boundary entry 32 64 88)
    {offset len : Nat} (h : offset+len ≤ 88) {a : BitVec 64}
    (ha : (Component.mem (stackPtr s-88+BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region s 88).Contains a.toNat := by
  rw [scratch_address s (by omega)] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack (by omega)]
    change (stackPtr s).toNat-88 ≤ (stackPtr s).toNat-(88-offset)
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack (by omega)]
    have := (stack_bounds pre.stack).1
    omega

theorem output_writable (pre : CalleePre s boundary entry 32 64 88)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 64 := by
  have hr : MemReadable t (s.regValue .rdi) 64 :=
    P256.Proofs.Program.readable_of_grow
      (memoryRegion_memReadable pre.outputBounded pre.outputAllocated
        (Nat.le_refl _) (Nat.le_refl _)) grow
  refine ⟨hr, tables_of_not_reserved (by decide) hr.low ?_⟩
  intro i hi hin
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hin)

def frame (s : RamState) : List Component :=
  (List.range 16).map (fun i => Component.reg (BitVec.ofNat 5 i)) ++
    [.flags, .rip, .mem (stackPtr s-88) 88, .mem (s.regValue .rdi) 64]

theorem frame_within (pre : CalleePre s boundary entry 32 64 88) :
    WritesWithin (frame s) #v[registerRegion s .rdi 64, Stack.region s 88] := by
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact ha.elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact ha.elim
    · refine ⟨Stack.region s 88, by simp, ?_⟩
      apply scratch_inside pre (offset := 0) (len := 88) (by decide)
      simpa only [BitVec.add_zero] using ha
    · obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨registerRegion s .rdi 64, by simp,
        memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi⟩

theorem loaded_of_frame (pre : CalleePre s boundary entry 32 64 88)
    (h : AgreesExcept (frame s) s t) : ProgramLoaded t := by
  intro a b hb
  rw [h.memory a]
  · exact pre.loaded a b hb
  · intro c hc ha
    obtain ⟨r, hr, hin⟩ := frame_within pre c hc a ha
    apply pre.avoids r _ a hin (.inl ⟨b, hb⟩)
    simpa using hr

omit [Bindings] in
theorem prologue_frame {s t : RamState}
    (h : AgreesExcept (Multiply.prologueComponents s) s t) : AgreesExcept (frame s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [Multiply.prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [frame, List.range_succ, Component.isMem]
  · intro a c hc ha
    simp only [Multiply.prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      refine ⟨.mem (stackPtr s-88) 88, by simp [frame], ?_⟩
      obtain ⟨i, hi, rfl⟩ := ha
    · exact ⟨80+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 80) (by decide)]
        rfl⟩
    · exact ⟨72+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 72) (by decide)]
        rfl⟩
    · exact ⟨64+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 64) (by decide)]
        rfl⟩
    · exact ⟨56+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 56) (by decide)]
        rfl⟩
    · exact ⟨48+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 48) (by decide)]
        rfl⟩
    · exact ⟨40+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 40) (by decide)]
        rfl⟩

theorem input_bytes (pre : CalleePre s boundary entry 32 64 88)
    (h : AgreesExcept (frame s) s t) {i : Nat} (hi : i < 32) :
    t.external[s.regValue .rsi+BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi+BitVec.ofNat 64 i]? := by
  apply h.memoryWriteFrame (frame_within pre)
  intro r hr
  have hin : (registerRegion s .rsi 32).Contains
      (s.regValue .rsi+BitVec.ofNat 64 i).toNat :=
    memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : r = registerRegion s .rdi 64 ∨ r = Stack.region s 88 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin

end P256.Proofs.Sec1.SquareRoot.Square.Wide
