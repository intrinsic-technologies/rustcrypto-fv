import P256.Proofs.Verifying.Combination.Loop.MultiSelection.State
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem read_digit [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v (k+1) point left)
    (bound : k < 257) :
    ∃ w, Advances boundary 1 t w ∧
      DigitState s w tables digits p q u v (k+1) point left 0x10f2d4 ∧
      w.regValue .rdi = (BitVec.ofInt 8 (((Naf.digits (if left then u else v))[k]?).getD 0)).setWidth 64 := by
  let index : Nat := (if left then 0 else 272) + 8 + k
  have addr : (AddrMode.base 13 (.d8 0)).addr t 0x10f2d4 = digits + BitVec.ofNat 64 index := by
    change t.regValue .r13 + 0#64 = _
    rw [state.cursor, BitVec.add_zero]
    have h : k+1+7 = 8+k := by omega
    rw [h]
    cases left <;> simp only [index, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.add_zero]
  have hi : index + 1 ≤ 544 := by cases left <;> dsimp [index] <;> omega
  have read : MemReadable t (digits + BitVec.ofNat 64 index) 1 := by
    apply readable_of_grow (s := s) _ state.allocated
    have bounds : digits.toNat + 544 < 2^32 := pre.digitsBounded
    have hn : (digits + BitVec.ofNat 64 index).toNat = digits.toNat + index :=
      by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
    apply memoryRegion_memReadable pre.digitsBounded pre.digitsAllocated
    · change digits.toNat ≤ _
      rw [hn]; omega
    · change _ + 1 ≤ digits.toNat + 544
      rw [hn]; omega
  obtain ⟨w, run, ready, effect⟩ :=
    (movzx_r32_m8_rex_effect_step 0x10f2cf 0x41 (by simp [RexNoWPrefix]) 7 (.base 13 (.d8 0))
      (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf2cf [0x41,0x0f,0xb6,0x7d,0]
        (by decide) (by decide +kernel))
      ⟨state.rip, by change MemReadable t ((AddrMode.base 13 (.d8 0)).addr t 0x10f2d4) 1; rw [addr]; exact read⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2d4 (by decide)))
  have frame : AgreesExcept [.reg 7, .rip] t w := effect.agrees
  refine ⟨w, run, state_after_registers state ready frame
    (by simp [Component.Covers]) (by simp) effect.rip, ?_⟩
  have digit : memLoad t.external (digits + BitVec.ofNat 64 index) 8 =
      BitVec.ofInt 8 (((Naf.digits (if left then u else v))[k]?).getD 0) := by
    cases left
    · simpa only [index, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
        using state.rightDigits.digit k bound
    · simpa only [index, ↓reduceIte, Nat.zero_add, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
        using state.leftDigits.digit k bound
  have h := effect.writes
  change w.regValue .rdi = (memLoad t.external ((AddrMode.base 13 (.d8 0)).addr t 0x10f2d4) 8).setWidth 64 at h
  rw [addr, digit] at h
  exact h

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
