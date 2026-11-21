import P256.Proofs.Projective.Double.Values
import P256.Proofs.Projective.Double.Memory
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

theorem point_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    {offset len : Nat} (bound : offset + len ≤ 96) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi + BitVec.ofNat 64 offset) len := by
  have readable := point_readable pre state bound
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi hreserved
  apply pre.avoids (registerRegion s .rdi 96) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change offset + i < 96; omega)

theorem point_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    {offset len codeOffset codeLen : Nat} (bound : offset + len ≤ 96)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 96) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change offset + i < 96; omega)
  · left
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)

theorem stack_read_of_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset : Nat} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 96])
    (bound : offset ≤ 1016) (positive : 8 ≤ offset) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [frame _]
  intro region hr hin
  have he : region = registerRegion s .rdi 96 := by simpa using hr
  subst region
  exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    (stack_contains pre bound (by omega) ⟨i, hi, rfl⟩)

theorem point_write_within [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {n offset : Nat} {regions : Vector MemoryRegion n}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (region : registerRegion s .rdi 96 ∈ regions) (bound : offset + 8 ≤ 96) :
    WritesWithin [.mem (s.regValue .rdi + BitVec.ofNat 64 offset) 8, .rip] regions := by
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨registerRegion s .rdi 96, region, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (by change offset + i < 96; omega)
  · exact ha.elim

theorem stackSlot_read_of_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset : Nat} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 96]) (bound : offset + 8 ≤ 728) :
    memLoad u.external (stackSlot s offset) 64 = memLoad t.external (stackSlot s offset) 64 := by
  rw [stackSlot_eq s (by omega)]
  exact stack_read_of_point pre frame (by omega) (by omega)

end P256.Proofs.Projective.Double
