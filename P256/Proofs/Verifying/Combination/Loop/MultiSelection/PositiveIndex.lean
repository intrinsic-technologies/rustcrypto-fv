import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Arithmetic
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.State
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false


namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open Naf.Iterator.Advance (branch8 branch32)

set_option maxRecDepth 4096 in
theorem select_positive_index [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v k point left 0x10f2e4)
    (digit : Int) (hd : Naf.ValidDigit digit) (positive : 0 < digit)
    (rdi : t.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64)
    (rax : t.regValue .rax = (BitVec.ofInt 8 digit).setWidth 64) :
    ∃ w, Advances boundary 3 t w ∧
      DigitState s w tables digits p q u v k point left 0x10f2ea ∧
      w.regValue .rdi = BitVec.ofNat 64 (digit.natAbs / 2) := by
  let off : Nat := 0xf2e4
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (shr_r32_one_effect_step (Extracted.textAddress + BitVec.ofNat 64 off) 0xef rfl rfl).advances
      (boundary := boundary) (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) off [0xd1, 0xef]
        (by decide) (by decide +kernel))
      state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2e6 (by decide)))
  have frameA : AgreesExcept [.reg 7, .flags, .rip] t a := effectA.agrees
  have stateA := state_after_registers state readyA frameA (by simp [Component.Covers]) (by simp) effectA.rip
  have raxA : a.regValue .rax = (BitVec.ofInt 8 digit).setWidth 64 :=
    (frameA.read (n := 64) (r := 0) (by simp)).trans rax
  have rdiA : a.regValue .rdi = BitVec.ofNat 64 (digit.natAbs / 2) := by
    have h := effectA.writes
    change a.regValue .rdi = ((t.regValue .rdi).setWidth 32 >>> 1).setWidth 64 at h
    rw [rdi] at h
    apply h.trans
    rcases validDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | decide +kernel
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (cmp_al_imm8_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+2)) 15).advances
      (boundary := boundary) readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) (off+2) [0x3c, 0x0f]
        (by decide) (by decide +kernel))
      (by simpa only [shrR32Effect, BitVec.ofNat_add, BitVec.add_assoc] using effectA.rip)
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+2) + 2) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
          BitVec.reduceAdd, Extracted.textAddress] using
          boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2e8 (by decide)))
  have frameB : AgreesExcept [.flags, .rip] a b := effectB.agrees
  have stateB := state_after_registers stateA readyB frameB (by simp [Component.Covers]) (by simp) effectB.rip
  have ripB : b.RIP = 0x10f2e8 := by
    simpa [cmpAlImm8Effect, off, Extracted.textAddress] using effectB.rip
  have cond : condHolds 7 (StatusFlags.ofRFLAGS b.RFLAGS) = false := by
    have cf := effectB.flags.1
    have zf := effectB.flags.2.2.2.1
    change _ = decide ((a.regValue .rax).setWidth 8 < 15#8) at cf
    change _ = ((a.regValue .rax).setWidth 8 - 15#8 == 0#8) at zf
    change (!( _ || _ )) = false
    rw [cf, zf, raxA]
    rcases validDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | decide +kernel
  obtain ⟨w, runW, readyW, _, ripW, frameW⟩ := branch8 (offset := 0xf2e8) 7 0x3e false
    readyB stateB.loaded ripB cond (by decide) (by decide +kernel) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf2ea (by decide)))
  exact ⟨w, (runA.trans runB).trans runW,
    state_after_registers stateB readyW frameW (by simp [Component.Covers]) (by simp) ripW,
    (frameW.read (n := 64) (r := 7) (by simp)).trans
      ((frameB.read (n := 64) (r := 7) (by simp)).trans rdiA)⟩

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
