import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false


namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Instructions.ShiftLeft

set_option maxHeartbeats 600000 in
set_option maxRecDepth 8192 in
theorem select_negative_scale [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (left : Bool) (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (rip : t.RIP = 0x10f1e8)
    (i : Fin 8) (rdi : t.regValue .rdi = BitVec.ofNat 64 i.val) :
    ∃ w, Advances boundary 2 t w ∧ DigitData s w tables digits p q u v k point left ∧
      w.RIP = 0x10f1f0 ∧ w.regValue .rax = BitVec.ofNat 64 (96*i.val) := by
  let off : Nat := 0xf1e8
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (lea_r64_effect_step (Extracted.textAddress + BitVec.ofNat 64 off) 0x48
      (by simp [RexWPrefix]) 0 (.sib 7 (some 7) 1 .none) (by decide +kernel) rfl rfl).advances
      (boundary := boundary) (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) off [0x48,0x8d,0x04,0x7f]
        (by decide) (by decide +kernel))
      rip
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 off + 4) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1ec (by decide)))
  have frameA : AgreesExcept [.reg 0, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have bpA : a.regValue .rax = BitVec.ofNat 64 i.val + (BitVec.ofNat 64 i.val <<< 1) := by
    have h := effectA.writes
    change a.regValue .rax = t.regValue .rdi + (t.regValue .rdi <<< 1) + 0 at h
    simpa [rdi] using h
  have ripA : a.RIP = Extracted.textAddress + BitVec.ofNat 64 (off+4) := by
    have h := effectA.rip
    change a.RIP = Extracted.textAddress + BitVec.ofNat 64 off + (4 : BitVec 64) at h
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using h
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (shl_r64_imm8_effect_step (Extracted.textAddress + BitVec.ofNat 64 (off+4)) 0x48 0xe0 5
      (by simp [RexWPrefix]) rfl rfl).advances (boundary := boundary) readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) (off+4) [0x48,0xc1,0xe0,5]
        (by decide) (by decide +kernel)) ripA
      (by
        change (Extracted.textAddress + BitVec.ofNat 64 (off+4) + 4) ≠ boundary.rip
        simpa only [off, Nat.reduceAdd, Extracted.textAddress, BitVec.ofNat_eq_ofNat,
          BitVec.reduceAdd, Int.reduceToNat] using boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0xf1f0 (by decide)))
  have frameW : AgreesExcept [.reg 0, .flags, .rip] a w := effectW.agrees
  refine ⟨w, runA.trans runW,
    stateA.after_registers readyW frameW (by simp [Component.Covers]) (by simp),
    ?_, ?_⟩
  · simpa only [shlR64Effect, off, Nat.reduceAdd, Extracted.textAddress,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Int.reduceToNat] using effectW.rip
  · have h := effectW.writes
    change w.regValue .rax = a.regValue .rax <<< 5 at h
    rw [bpA] at h
    apply h.trans
    exact (show ∀ i : Fin 8, (BitVec.ofNat 64 i.val + (BitVec.ofNat 64 i.val <<< 1)) <<< 5 =
      BitVec.ofNat 64 (96*i.val) from by decide +kernel) i

end P256.Proofs.Verifying.Combination.Loop.Multi
