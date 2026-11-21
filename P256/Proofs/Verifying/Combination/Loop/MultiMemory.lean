import P256.Proofs.Verifying.Combination.Loop.MultiPrologue
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Memory [Bindings] (s t : RamState) (tables digits : BitVec 64)
    (p q : Projective) (u v : Nat) : Prop extends FrameState s t 96 1432 408 where
  leftTable : Table.TableAt t tables (Table.oddTable p)
  rightTable : Table.TableAt t (tables + 768) (Table.oddTable q)
  leftDigits : Naf.NafAt t digits u
  rightDigits : Naf.NafAt t (digits + 272) v

theorem memory_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (pre : MultiPre s boundary tables digits) (state : State s t)
    (leftTable : Table.TableAt s tables (Table.oddTable p))
    (rightTable : Table.TableAt s (tables + 768) (Table.oddTable q))
    (leftDigits : Naf.NafAt s digits u) (rightDigits : Naf.NafAt s (digits + 272) v) :
    Memory s t tables digits p q u v := by
  have tableBytes : ∀ i < 1536,
      t.external[tables + BitVec.ofNat 64 i]? = s.external[tables + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame_read state.frame (region := tablesRegion tables)
    · intro region hr
      have h : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1432 := by simpa using hr
      rcases h with rfl | rfl
      · exact pre.tablesOutput
      · exact pre.tablesStack
    · exact memoryRegion_contains_add pre.tablesBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have digitBytes : ∀ i < 544,
      t.external[digits + BitVec.ofNat 64 i]? = s.external[digits + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame_read state.frame (region := digitsRegion digits)
    · intro region hr
      have h : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1432 := by simpa using hr
      rcases h with rfl | rfl
      · exact pre.digitsOutput
      · exact pre.digitsStack
    · exact memoryRegion_contains_add pre.digitsBounded (Nat.le_refl _) (Nat.le_refl _) hi
  refine ⟨state, leftTable.of_copy (fun i hi => tableBytes i (by omega)), ?_,
    leftDigits.of_copy (fun i hi => digitBytes i (by omega)), ?_⟩
  · apply rightTable.of_copy
    intro i hi
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using tableBytes (768+i) (by omega)
  · apply rightDigits.of_copy
    intro i hi
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using digitBytes (272+i) (by omega)

theorem metadata_read [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits) (state : State s t)
    (offset : Nat) (bound : offset + 8 ≤ 48) :
    memLoad t.external (s.regValue .rsi + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 offset) 64 := by
  have limit : (s.regValue .rsi).toNat + 48 < 2^32 := pre.inputBounded
  have addr : (s.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rsi).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply frame_memLoad state.frame (region := registerRegion s .rsi 48)
  · intro region hr
    have h : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1432 := by simpa using hr
    rcases h with rfl | rfl
    · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide)
    · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)
  · exact pre.inputBounded
  · change (s.regValue .rsi).toNat ≤ _
    rw [addr]
    omega
  · change _ + 8 ≤ (s.regValue .rsi).toNat + 48
    rw [addr]
    omega

theorem metadata_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits) (state : State s t)
    (offset : Nat) (bound : offset + 8 ≤ 48) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) 8 := by
  apply readable_of_grow (s := s) _ state.allocated
  have limit : (s.regValue .rsi).toNat + 48 < 2^32 := pre.inputBounded
  have addr : (s.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rsi).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · change (s.regValue .rsi).toNat ≤ _
    rw [addr]
    omega
  · change _ + 8 ≤ (s.regValue .rsi).toNat + 48
    rw [addr]
    omega

end P256.Proofs.Verifying.Combination.Loop.Multi
