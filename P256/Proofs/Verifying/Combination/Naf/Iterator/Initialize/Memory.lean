import P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize.Prologue
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {reserve : Nat}

theorem input_readable (pre : CalleePre s boundary 0x118290 32 40 reserve)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    MemReadable t (s.regValue .rsi) 16 := by
  apply readable_of_grow _ grow
  exact memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (by change (s.regValue .rsi).toNat + 16 ≤ (s.regValue .rsi).toNat + 32; omega)

theorem output_writable (pre : CalleePre s boundary 0x118290 32 40 reserve)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    Writable t (s.regValue .rdi) 40 := by
  have hr : MemReadable t (s.regValue .rdi) 40 :=
    readable_of_grow
      (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)) grow
  refine ⟨hr, tables_of_not_reserved (by decide) hr.low ?_⟩
  intro i hi hin
  exact pre.avoids (registerRegion s .rdi 40) (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hin)

theorem output_apart (pre : CalleePre s boundary 0x118290 32 40 reserve) :
    RangeApart (s.regValue .rdi) 40 0x1182c5 26 := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 40) (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inl ?_)
  rw [he]
  have hp := inProgram_of_textOffset (0x182c5 + j) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hp
  exact hp

theorem input_read_of_frame (pre : CalleePre s boundary 0x118290 32 40 reserve)
    (frame : MemoryWriteFrame s t #v[Stack.region s reserve])
    (offset : Nat) (bound : offset + 8 ≤ 32) :
    memLoad t.external (s.regValue .rsi + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (t.external[s.regValue .rsi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[s.regValue .rsi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [frame _]
  intro region hr hin
  have he : region = Stack.region s reserve := by simpa using hr
  subst region
  apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hin
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) (by change offset + i < 32; omega)

theorem output_frame (pre : CalleePre s boundary 0x118290 32 40 reserve)
    {u : RamState} (pointer : t.regValue .rbx = s.regValue .rdi)
    (effect : (initializeStoreEffect t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a cover
  simp only [initializeStoreEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨i, hi, rfl⟩ := cover
  all_goals refine ⟨registerRegion s .rdi 40, by simp, ?_⟩
  all_goals
    rw [pointer]
    have hb : (s.regValue .rdi).toNat + 40 < 2^32 := pre.outputBounded
    change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + 40
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega

theorem output_read_stack (pre : CalleePre s boundary 0x118290 32 40 reserve)
    {u : RamState} (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 40])
    (offset : Nat) (bound : offset ≤ reserve) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [frame _]
  intro region hr hin
  have he : region = registerRegion s .rdi 40 := by simpa using hr
  subst region
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack bound
  change (stackPtr s).toNat - reserve ≤ _ ∧
    (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
      (Stack.region s reserve).start + (Stack.region s reserve).size
  rw [stack_region_end, toNat_add_ofNat _ _ (by rw [low]; omega), low]
  constructor <;> omega

end P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize
