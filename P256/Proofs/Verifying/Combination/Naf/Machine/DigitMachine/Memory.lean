import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.State
import P256.Proofs.Verifying.Combination.Naf.Machine.Frame
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Steps

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem output_readable (pre : Pre s boundary) (frame : FrameState s t)
    {i len : Nat} (bound : i+len ≤ 257) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 i) len := by
  exact P256.Proofs.Program.readable_of_grow
    (Iterator.readable_subrange
      (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
      i len bound) frame.allocated

theorem output_writable (pre : Pre s boundary) (frame : FrameState s t)
    {i : Nat} (bound : i < 257) :
    MemWritable t (s.regValue .rdi + BitVec.ofNat 64 i) 1 := by
  have hr := output_readable pre frame (i := i) (len := 1) (by omega)
  apply MemWritable.of_not_reserved (by decide) hr.low hr.mem
  intro j hj hin
  apply pre.avoids (registerRegion s .rdi 257) (by simp) _ ?_ (.inr hin)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
    (show i+j < 257 by omega)

theorem output_code (pre : Pre s boundary) {i len pc codeLen : Nat}
    (bound : i+len ≤ 257) (codeBound : pc+codeLen ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 i) len
      (Extracted.textAddress+BitVec.ofNat 64 pc) codeLen := by
  intro j hj k hk he
  apply pre.avoids (registerRegion s .rdi 257) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 i + BitVec.ofNat 64 j)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show i+j < 257 by omega)
  · left
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)

theorem output_contains (pre : Pre s boundary) {i len : Nat} (bound : i+len ≤ 257)
    {a : BitVec 64} (covers : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 i) len).Covers a) :
    (digitRegion s i len).Contains a.toNat := by
  obtain ⟨j, hj, rfl⟩ := covers
  have low : (s.regValue .rdi).toNat+257 < 2^32 := pre.outputBounded
  have base : (s.regValue .rdi + BitVec.ofNat 64 i).toNat = (s.regValue .rdi).toNat+i :=
    toNat_add_ofNat _ _ (by omega)
  change (s.regValue .rdi + BitVec.ofNat 64 i).toNat ≤ _ ∧
    _ < (s.regValue .rdi + BitVec.ofNat 64 i).toNat+len
  rw [toNat_add_ofNat (s.regValue .rdi + BitVec.ofNat 64 i) j (by rw [base]; omega)]
  omega


theorem output_after (pre : Pre s boundary) (frame : FrameState s t)
    {cs : List Component} {i len : Nat} (bound : i+len ≤ 257)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (s.regValue .rdi + BitVec.ofNat 64 i) len).Covers a)
    (sp : .reg 4 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    FrameState s u ∧ MemoryWriteFrame t u #v[digitRegion s i len] := by
  have within : WritesWithin cs #v[digitRegion s i len] := by
    intro c hc a ha
    exact ⟨_, by simp, output_contains pre bound (writes c hc a ha)⟩
  refine ⟨after pre.toCalleePre frame ready agrees ?_ sp, agrees.memoryWriteFrame within⟩
  intro c hc a ha
  obtain ⟨j, hj, rfl⟩ := writes c hc a ha
  refine ⟨registerRegion s .rdi 257, by simp, ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
    (show i+j < 257 by omega)

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
