import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

variable {initial t : RamState} {reserve offset len : Nat}

theorem stack_buffer_contains (stack : Stack.Valid initial reserve)
    (within : offset ≤ reserve) (extent : len ≤ offset + 8) {a : Nat}
    (contained : (MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 offset).toNat len).Contains a) :
    (Stack.region initial reserve).Contains a := by
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack within
  change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
    a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + len at contained
  rw [low] at contained
  change (stackPtr initial).toNat - reserve ≤ a ∧
    a < (Stack.region initial reserve).start + (Stack.region initial reserve).size
  rw [stack_region_end]
  constructor <;> omega

theorem stack_buffer_bounded (stack : Stack.Valid initial reserve)
    (within : offset ≤ reserve) (extent : len ≤ offset + 8) :
    (MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 offset).toNat len).Bounded := by
  have bounds := stack_bounds stack
  change (stackPtr initial - BitVec.ofNat 64 offset).toNat + len < 2^32
  rw [stack_sub_toNat stack within]
  omega

theorem stack_buffer_avoids (stack : Stack.Valid initial reserve)
    (avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (within : offset ≤ reserve) (extent : len ≤ offset + 8) :
    (MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 offset).toNat len).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
  intro a ha
  exact avoids a (stack_buffer_contains stack within extent ha)

theorem stack_buffer_writable (stack : Stack.Valid initial reserve)
    (avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (grown : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (within : offset ≤ reserve) (extent : len ≤ offset + 8) (positive : 0 < len) :
    CrossPageStore.Writable t (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have readable := readable_of_grow (stack_sub_readable stack within extent) grown
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi reserved
  apply avoids _ ?_ (.inr reserved)
  exact stack_buffer_contains stack within extent
    (memoryRegion_contains_add (stack_buffer_bounded stack within extent)
      (Nat.le_refl _) (Nat.le_refl _) hi)

theorem stack_buffer_code_apart (stack : Stack.Valid initial reserve)
    (avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (within : offset ≤ reserve) (extent : len ≤ offset + 8)
    {codeOffset codeLength : Nat} (codeBound : codeOffset + codeLength ≤ 118431) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLength := by
  intro i hi j hj eq
  apply avoids _ (stack_buffer_contains stack within extent
    (memoryRegion_contains_add (stack_buffer_bounded stack within extent)
      (Nat.le_refl _) (Nat.le_refl _) hi))
  apply Or.inl
  rw [eq]
  have program := inProgram_of_textOffset (codeOffset+j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using program

end P256.Proofs.Program
