import P256.Proofs.Program.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

open P256.Proofs.Program (CalleePre inProgram_of_textOffset memoryRegion_contains_add memoryRegion_memReadable)

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}

variable {inputRegister : Syntax.Reg}

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister) (positive : 0 < outputBytes)
    (allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) outputBytes := by
  have readable := P256.Proofs.Program.readable_of_grow
    (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
    allocated
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi hreserved
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hreserved)

theorem output_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister) {offset len : Nat}
    (bound : offset + len ≤ 118431) : RangeApart (s.regValue .rdi) outputBytes
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + j) (by omega)

theorem output_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister) {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ outputBytes)
    (covered : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion s .rdi outputBytes).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show offset + i < outputBytes by omega)

end P256.Proofs.Program.ScalarFrame
