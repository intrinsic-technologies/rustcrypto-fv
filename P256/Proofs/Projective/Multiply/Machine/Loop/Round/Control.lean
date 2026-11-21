import P256.Proofs.Projective.Multiply.Machine.Loop.Round.EndArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem skip_table_loop [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (rip : t.RIP = 0x1033be) (rbx : t.regValue .rbx = 0)
    (r14 : t.regValue .r14 = 65) :
    ∃ u, Advances boundary 4 t u ∧ FrameState s u 96 1400 376 ∧ u.RIP = 0x1033ce ∧
      AgreesExcept [.reg 3, .reg 15, .flags, .rip] t u := by
  obtain ⟨u₁, run₁, ready₁, effect₁⟩ :=
    (add_r64_imm8_effect_step 0x1033be 0x48 0xc3 65 (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x33be [0x48,0x83,0xc3,0x41]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x33c2 (by decide)))
  have frame₁ : AgreesExcept [.reg 3, .flags, .rip] t u₁ := effect₁.agrees
  have state₁ := state.after_registers ready₁ frame₁ (by simp [Component.Covers]) (by simp)
  have rbx₁ : u₁.regValue .rbx = 65 := by
    have h := effect₁.writes
    change u₁.regValue .rbx = t.regValue .rbx + 65 at h
    rw [rbx] at h
    exact h
  obtain ⟨u₂, run₂, ready₂, effect₂⟩ :=
    (add_r64_imm32_effect_step 0x1033c2 0x49 0xc7 768 (by simp [RexWPrefix]) rfl rfl).advances
      ready₁ (programText_slice (programLoaded_codeIn state₁.loaded) 0x33c2
        [0x49,0x81,0xc7,0,3,0,0] (by decide) (by decide +kernel)) effect₁.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x33c9 (by decide)))
  have frame₂ : AgreesExcept [.reg 15, .flags, .rip] u₁ u₂ := effect₂.agrees
  have state₂ := state₁.after_registers ready₂ frame₂ (by simp [Component.Covers]) (by simp)
  have rbx₂ : u₂.regValue .rbx = 65 :=
    (frame₂.read (n := 64) (r := 3) (by simp)).trans rbx₁
  have r14₂ : u₂.regValue .r14 = 65 :=
    (frame₂.read (n := 64) (r := 14) (by simp)).trans
      ((frame₁.read (n := 64) (r := 14) (by simp)).trans r14)
  obtain ⟨u₃, run₃, ready₃, effect₃⟩ :=
    (cmp_r64_r64_effect_step 0x1033c9 0x49 0xde (by simp [RexWPrefix]) rfl).advances ready₂
      (programText_slice (programLoaded_codeIn state₂.loaded) 0x33c9 [0x49,0x39,0xde]
        (by decide) (by decide +kernel)) effect₂.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x33cc (by decide)))
  have frame₃ : AgreesExcept [.flags, .rip] u₂ u₃ := effect₃.agrees
  have state₃ := state₂.after_registers ready₃ frame₃ (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS u₃.RFLAGS).ZF = true := by
    have h := effect₃.flags.2.2.2.1
    change _ = ((u₂.regValue .r14 - u₂.regValue .rbx) == 0#64) at h
    simpa only [r14₂, rbx₂, BitVec.sub_self, BEq.rfl] using h
  have next : (jccEffect 0x1033cc 2 5 ((0xb2 : BitVec 8).signExtend 64) u₃).rip = 0x1033ce := by
    simp [jccEffect, branchEffect, condHolds, zf]
  obtain ⟨u, run₄, ready₄, effect₄⟩ := (jcc_rel8_effect_step 0x1033cc 5 0xb2).advances ready₃
    (programText_slice (programLoaded_codeIn state₃.loaded) 0x33cc [0x75,0xb2]
      (by decide) (by decide +kernel)) ⟨effect₃.rip, by intro h; decide +kernel⟩
    (by rw [next]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x33ce (by decide)))
  have frame₄ : AgreesExcept [.rip] u₃ u := effect₄.agrees
  have frame : AgreesExcept [.reg 3, .reg 15, .flags, .rip] t u :=
    (((frame₁.trans frame₂).trans frame₃).trans frame₄).mono (by simp)
  exact ⟨u, ((run₁.trans run₂).trans run₃).trans run₄,
    state.after_registers ready₄ frame (by simp [Component.Covers]) (by simp), effect₄.rip.trans next, frame⟩

theorem end_iteration [Bindings] {s t : RamState} {boundary : ReturnBoundary} {remaining : Nat}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (rip : t.RIP = 0x1033ce) (bound : remaining < 64)
    (counter : (Operand.mem (stackPtr s - 344) : Operand 64).read t = BitVec.ofNat 64 remaining) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1400 376 ∧
      u.RIP = (if remaining = 0 then 0x103425 else 0x103340) ∧
      u.regValue .r9 = (Operand.mem (stackPtr s - 368) : Operand 64).read t - 1 ∧
      u.regValue .r15 = BitVec.ofNat 64 remaining ∧
      u.regValue .rbx = (Operand.mem (stackPtr s-352) : Operand 64).read t ∧
      AgreesExcept [.reg 9, .reg 15, .reg 3, .flags, .rip] t u := by
  obtain ⟨fuel, v, run, ready, _, effect⟩ := end_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x33ce endSetupBytes
      (by decide) (by decide +kernel))
    ⟨rip, stack_readable pre.toCalleePre state (by decide) (by decide),
      stack_readable pre.toCalleePre state (by decide) (by decide),
      stack_readable pre.toCalleePre state (by decide) (by decide)⟩
  have frame : AgreesExcept [.reg 9, .reg 15, .reg 3, .flags, .rip] t v := effect.agrees
  have stateV := state.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have cursorAddr : stackPtr t + 8 = stackPtr s - 368 := scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have countAddr : stackPtr t + 32 = stackPtr s - 344 := scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have writes : v.regValue .r9 = (Operand.mem (stackPtr t + 8) : Operand 64).read t - 1 ∧
      v.regValue .r15 = (Operand.mem (stackPtr t + 32) : Operand 64).read t ∧
      v.regValue .rbx = (Operand.mem (stackPtr t + 24) : Operand 64).read t := effect.writes
  rw [cursorAddr, countAddr, counter] at writes
  have zf : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (remaining = 0) := by
    have h := effect.flags.2.2.2.1
    change _ = (((Operand.mem (stackPtr t + 32) : Operand 64).read t) == 0) at h
    rw [countAddr, counter] at h
    exact h.trans ((show ∀ i : Fin 64,
      (BitVec.ofNat 64 i.val == 0) = decide (i.val = 0) by decide +kernel) ⟨remaining, bound⟩)
  have next : (jccEffect 0x1033e3 6 5 ((0xffffff57 : BitVec 32).signExtend 64) v).rip =
      (if remaining = 0 then 0x1033e9 else 0x103340) := by
    by_cases zero : remaining = 0 <;> simp [jccEffect, branchEffect, condHolds, zf, zero, branchTarget]
  obtain ⟨w, runW, readyW, effectW⟩ := (jcc_rel32_effect_step 0x1033e3 5 0xffffff57).advances ready
    (programText_slice (programLoaded_codeIn stateV.loaded) 0x33e3 [0x0f,0x85,0x57,0xff,0xff,0xff]
      (by decide) (by decide +kernel)) ⟨effect.rip, by intro h; decide +kernel⟩
    (by rw [next]; split
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x33e9 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3340 (by decide)))
  have frameW : AgreesExcept [.rip] v w := effectW.agrees
  have combined : AgreesExcept [.reg 9, .reg 15, .reg 3, .flags, .rip] t w := (frame.trans frameW).mono (by simp)
  have stateW := state.after_registers readyW combined (by simp [Component.Covers]) (by simp)
  have cursorW : w.regValue .r9 = (Operand.mem (stackPtr s - 368) : Operand 64).read t - 1 :=
    (frameW.read (n := 64) (r := 9) (by simp)).trans writes.1
  have counterW : w.regValue .r15 = BitVec.ofNat 64 remaining :=
    (frameW.read (n := 64) (r := 15) (by simp)).trans writes.2.1
  have tableAddr : stackPtr t+24 = stackPtr s-352 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have tableW : w.regValue .rbx = (Operand.mem (stackPtr s-352) : Operand 64).read t := by
    exact (frameW.read (n := 64) (r := 3) (by simp)).trans
      (writes.2.2.trans (congrArg (fun x => (Operand.mem x : Operand 64).read t) tableAddr))
  by_cases zero : remaining = 0
  · obtain ⟨u, runU, readyU, effectU⟩ := (jmp_rel8_effect_step 0x1033e9 0x3a (by decide +kernel)).advances readyW
      (programText_slice (programLoaded_codeIn stateW.loaded) 0x33e9 [0xeb,0x3a]
        (by decide) (by decide +kernel))
      (by simpa only [zero, ↓reduceIte] using effectW.rip.trans next)
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3425 (by decide)))
    have frameU : AgreesExcept [.rip] w u := effectU.agrees
    refine ⟨fuel+1+1, u, (run.trans runW).trans runU,
      stateW.after_registers readyU frameU (by simp [Component.Covers]) (by simp), ?_,
      (frameU.read (n := 64) (r := 9) (by simp)).trans cursorW,
      (frameU.read (n := 64) (r := 15) (by simp)).trans counterW,
      (frameU.read (n := 64) (r := 3) (by simp)).trans tableW,
      (combined.trans frameU).mono (by simp)⟩
    simp only [zero, ↓reduceIte]
    exact effectU.rip
  · refine ⟨fuel+1, w, run.trans runW, stateW, ?_, cursorW, counterW, tableW, combined⟩
    simpa only [zero, ↓reduceIte] using effectW.rip.trans next

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
