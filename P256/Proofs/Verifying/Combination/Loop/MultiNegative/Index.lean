import P256.Proofs.Verifying.Combination.Loop.Digit.Arithmetic
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.Negate
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.Shift
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.SignExtend
import P256.Proofs.Common.Curve.LinearCombination.Loop.Instructions.Compare
import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Sub
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false


namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Curve.LinearCombination.Loop.Instructions
open Negative.Instructions
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)
open Naf.Iterator.Advance (branch32)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
theorem select_negative_index [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (left : Bool) (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (rip : t.RIP = 0x10f1d0)
    (digit : Int) (hd : Naf.ValidDigit digit) (negative : digit < 0)
    (rdi : t.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64)
    (rax : (t.regValue .rax).setWidth 8 = BitVec.ofInt 8 digit) :
    ∃ w, Advances boundary 7 t w ∧
      DigitData s w tables digits p q u v k point left ∧ w.RIP = 0x10f1e8 ∧
      w.regValue .rdi = BitVec.ofNat 64 (digit.natAbs / 2) := by
  let off : Nat := 0xf1d0
  have low0 : (t.regValue .rax).setWidth 8 = BitVec.ofInt 8 digit := rax
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (neg_al_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+0))).advances (boundary := boundary)
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) (off+0) [0xf6,0xd8]
        (by decide) (by decide +kernel))
      rip
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+0) + 2) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1d2 (by decide)))
  have rip1 : t1.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+2) := by
    simpa only [negAlEffect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, Int.reduceToNat] using effect1.rip
  have frame1 : AgreesExcept [.reg 0, .flags, .rip] t t1 := effect1.agrees
  have state1 := state.after_registers ready1 frame1 (by simp [Component.Covers]) (by simp)
  have rdi1 : t1.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 :=
    (frame1.read (n := 64) (r := 7) (by simp)).trans rdi
  have low1 : (t1.regValue .rax).setWidth 8 = -(BitVec.ofInt 8 digit) := by
    have h := effect1.writes
    change t1.regValue .rax = mergeGPR 8 (-((t.regValue .rax).setWidth 8)) (t.regValue .rax) at h
    have hlow := congrArg (BitVec.setWidth 8) h
    simpa only [mergeGPR_low8, low0] using hlow
  obtain ⟨t2, run2, ready2, effect2⟩ :=
    (shr_al_seven_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+2))).advances (boundary := boundary)
      ready1
      (programText_slice (programLoaded_codeIn state1.loaded) (off+2) [0xc0,0xe8,7]
        (by decide) (by decide +kernel))
      rip1
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+2) + 3) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1d5 (by decide)))
  have rip2 : t2.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+5) := by
    simpa only [shrAlSevenEffect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, Int.reduceToNat] using effect2.rip
  have frame2 : AgreesExcept [.reg 0, .flags, .rip] t1 t2 := effect2.agrees
  have state2 := state1.after_registers ready2 frame2 (by simp [Component.Covers]) (by simp)
  have rdi2 : t2.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 :=
    (frame2.read (n := 64) (r := 7) (by simp)).trans rdi1
  have low2 : (t2.regValue .rax).setWidth 8 = (-(BitVec.ofInt 8 digit)) >>> 7 := by
    have h := effect2.writes
    change t2.regValue .rax = mergeGPR 8 (((t1.regValue .rax).setWidth 8) >>> 7) (t1.regValue .rax) at h
    have hlow := congrArg (BitVec.setWidth 8) h
    simpa only [mergeGPR_low8, low1] using hlow
  obtain ⟨t3, run3, ready3, effect3⟩ :=
    (sub_r8_r8_rex_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+5)) 0x40 0xf8 (by simp [RexPrefix]) rfl).advances (boundary := boundary)
      ready2
      (programText_slice (programLoaded_codeIn state2.loaded) (off+5) [0x40,0x28,0xf8]
        (by decide) (by decide +kernel))
      rip2
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+5) + 3) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1d8 (by decide)))
  have rip3 : t3.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+8) := by
    simpa only [subR8R8Effect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, Int.reduceToNat] using effect3.rip
  have frame3 : AgreesExcept [.reg 0, .flags, .rip] t2 t3 := effect3.agrees
  have state3 := state2.after_registers ready3 frame3 (by simp [Component.Covers]) (by simp)
  have rdi3 : t3.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 :=
    (frame3.read (n := 64) (r := 7) (by simp)).trans rdi2
  have low3 : (t3.regValue .rax).setWidth 8 = ((-(BitVec.ofInt 8 digit)) >>> 7) - BitVec.ofInt 8 digit := by
    have h := effect3.writes
    change t3.regValue .rax = mergeGPR 8 (((t2.regValue .rax).setWidth 8) - (t2.regValue .rdi).setWidth 8) (t2.regValue .rax) at h
    have hlow := congrArg (BitVec.setWidth 8) h
    simpa only [mergeGPR_low8, low2, rdi2, BitVec.setWidth_setWidth_of_le (k := 8) (l := 64) _ (by decide), BitVec.setWidth_eq] using hlow
  obtain ⟨t4, run4, ready4, effect4⟩ :=
    (sar_al_one_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+8))).advances (boundary := boundary)
      ready3
      (programText_slice (programLoaded_codeIn state3.loaded) (off+8) [0xd0,0xf8]
        (by decide) (by decide +kernel))
      rip3
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+8) + 2) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1da (by decide)))
  have rip4 : t4.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+10) := by
    simpa only [sarAlOneEffect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, Int.reduceToNat] using effect4.rip
  have frame4 : AgreesExcept [.reg 0, .flags, .rip] t3 t4 := effect4.agrees
  have state4 := state3.after_registers ready4 frame4 (by simp [Component.Covers]) (by simp)
  have rdi4 : t4.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 :=
    (frame4.read (n := 64) (r := 7) (by simp)).trans rdi3
  have low4 : (t4.regValue .rax).setWidth 8 = ((((-(BitVec.ofInt 8 digit)) >>> 7) - BitVec.ofInt 8 digit).sshiftRight 1) := by
    have h := effect4.writes
    change t4.regValue .rax = mergeGPR 8 (((t3.regValue .rax).setWidth 8).sshiftRight 1) (t3.regValue .rax) at h
    have hlow := congrArg (BitVec.setWidth 8) h
    simpa only [mergeGPR_low8, low3] using hlow
  obtain ⟨t5, run5, ready5, effect5⟩ :=
    (movsx_rdi_al_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+10))).advances (boundary := boundary)
      ready4
      (programText_slice (programLoaded_codeIn state4.loaded) (off+10) [0x48,0x0f,0xbe,0xf8]
        (by decide) (by decide +kernel))
      rip4
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+10) + 4) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1de (by decide)))
  have rip5 : t5.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+14) := by
    simpa only [movsxRdiAlEffect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, Int.reduceToNat] using effect5.rip
  have frame5 : AgreesExcept [.reg 7, .rip] t4 t5 := effect5.agrees
  have state5 := state4.after_registers ready5 frame5 (by simp [Component.Covers]) (by simp)
  have index : t5.regValue .rdi = BitVec.ofNat 64 (digit.natAbs / 2) := by
    have h := effect5.writes
    change t5.regValue .rdi = ((t4.regValue .rax).setWidth 8).signExtend 64 at h
    rw [low4] at h
    apply h.trans
    rcases validDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | decide +kernel
  obtain ⟨t6, run6, ready6, effect6⟩ :=
    (cmp_dil_seven_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+14))).advances (boundary := boundary)
      ready5
      (programText_slice (programLoaded_codeIn state5.loaded) (off+14) [0x40,0x80,0xff,7]
        (by decide) (by decide +kernel))
      rip5
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+14) + 4) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1e2 (by decide)))
  have rip6 : t6.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+18) := by
    simpa only [cmpDilSevenEffect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, Int.reduceToNat] using effect6.rip
  have frame6 : AgreesExcept [.flags, .rip] t5 t6 := effect6.agrees
  have state6 := state5.after_registers ready6 frame6 (by simp [Component.Covers]) (by simp)
  have cond : condHolds 7 (StatusFlags.ofRFLAGS t6.RFLAGS) = false := by
    have cf := effect6.flags.1
    have zf := effect6.flags.2.2.2.1
    change _ = decide ((t5.regValue .rdi).setWidth 8 < 7#8) at cf
    change _ = ((t5.regValue .rdi).setWidth 8 - 7#8 == 0#8) at zf
    change (!( _ || _ )) = false
    rw [cf, zf, index]
    rcases validDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | decide +kernel
  obtain ⟨w, runW, readyW, _, ripW, frameW⟩ := branch32 (offset := 0xf1e2) 7 0x151 false
    ready6 state6.loaded rip6 cond (by decide) (by decide +kernel) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1e8 (by decide)))
  exact ⟨w, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans runW,
    state6.after_registers readyW frameW (by simp [Component.Covers]) (by simp), ripW,
    (frameW.read (n := 64) (r := 7) (by simp)).trans
      ((frame6.read (n := 64) (r := 7) (by simp)).trans index)⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
