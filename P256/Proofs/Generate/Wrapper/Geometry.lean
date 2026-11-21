import P256.Proofs.Generate.Wrapper.State
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Instructions

theorem stack_buffer_contains {initial : RamState} {offset len a : Nat}
    (stack : Stack.Valid initial 4024) (bound : offset ≤ 4024) (size : len ≤ offset+8)
    (contained : (MemoryRegion.mk (stackPtr initial-BitVec.ofNat 64 offset).toNat len).Contains a) :
    (Stack.region initial 4024).Contains a := by
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack bound
  change (stackPtr initial-BitVec.ofNat 64 offset).toNat ≤ a ∧
    a < (stackPtr initial-BitVec.ofNat 64 offset).toNat + len at contained
  rw [low] at contained
  change (stackPtr initial).toNat-4024 ≤ a ∧
    a < (Stack.region initial 4024).start + (Stack.region initial 4024).size
  rw [stack_region_end]
  constructor <;> omega

theorem stack_buffer_bounded {initial : RamState} {offset len : Nat}
    (stack : Stack.Valid initial 4024) (bound : offset ≤ 4024) (size : len ≤ offset+8) :
    (MemoryRegion.mk (stackPtr initial-BitVec.ofNat 64 offset).toNat len).Bounded := by
  have bounds := stack_bounds stack
  change (stackPtr initial-BitVec.ofNat 64 offset).toNat+len < 2^32
  rw [stack_sub_toNat stack bound]
  omega

theorem stack_buffer_writable [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {offset len : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (grown : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (bound : offset ≤ 4024) (size : len ≤ offset+8) (positive : 0 < len) :
    CrossPageStore.Writable s (stackPtr initial-BitVec.ofNat 64 offset) len := by
  have readable := readable_of_grow (stack_sub_readable call.stackAvailable.1 bound size) grown
  refine ⟨readable,?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi reserved
  apply call_stack_avoids call _ ?_ (.inr reserved)
  exact stack_buffer_contains call.stackAvailable.1 bound size
    (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1 bound size)
      (Nat.le_refl _) (Nat.le_refl _) hi)

theorem stack_buffer_avoids [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {offset len : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (bound : offset ≤ 4024) (size : len ≤ offset+8) :
    (MemoryRegion.mk (stackPtr initial-BitVec.ofNat 64 offset).toNat len).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
  intro a ha
  exact call_stack_avoids call a (stack_buffer_contains call.stackAvailable.1 bound size ha)

theorem stack_buffer_code_apart [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {offset len codeOffset codeLen : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (bound : offset ≤ 4024) (size : len ≤ offset+8)
    (code : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr initial-BitVec.ofNat 64 offset) len
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj eq
  apply stack_buffer_avoids call bound size _
    (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1 bound size)
      (Nat.le_refl _) (Nat.le_refl _) hi) (.inl ?_)
  rw [eq,BitVec.add_assoc,← BitVec.ofNat_add]
  exact inProgram_of_textOffset _ (by omega)

end P256.Proofs.Generate.Wrapper
