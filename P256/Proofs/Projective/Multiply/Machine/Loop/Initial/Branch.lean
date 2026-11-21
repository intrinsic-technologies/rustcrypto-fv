import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import P256.Proofs.Program.ScalarFrame.State
import P256.Proofs.Program.Code
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import P256.Proofs.Common.EffectCompose.Conditions
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem count_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : P256.Proofs.Program.CalleePre s boundary 0x103250 768 96 1400)
    (state : P256.Proofs.Program.ScalarFrame.FrameState s t 96 1400 376)
    (rip : t.RIP = 0x103280) (rdx : t.regValue .rdx = 1) (r8 : t.regValue .r8 = 1) :
    ∃ fuel u, Advances boundary fuel t u ∧ P256.Proofs.Program.ScalarFrame.FrameState s u 96 1400 376 ∧ u.RIP = 0x103290 ∧
      u.regValue .rdx = 1 ∧ AgreesExcept [.reg 2, .flags, .rip] t u := by
  obtain ⟨v, a1, ready1, e1⟩ :=
    (cmp_r64_r64_effect_step 0x103280 0x49 0xd0 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x3280 [0x49,0x39,0xd0]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3283 (by decide)))
  change (cmpR64R64Effect 0x103280 8 2 t).Holds t v at e1
  have sv := state.after_registers ready1 e1.agrees
    (by simp [Component.Covers]) (by simp)
  obtain ⟨w, a2, ready2, e2⟩ :=
    (cmov_r64_r64_effect_step 0x103283 0x49 0x42 0xd0
      (by simp [RexWPrefix]) (Or.inl rfl) rfl).advances ready1
      (programText_slice (programLoaded_codeIn sv.loaded) 0x3283 [0x49,0x0f,0x42,0xd0]
        (by decide) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3287 (by decide)))
  change (cmovR64R64Effect 0x103283 2 2 8 v).Holds v w at e2
  have e2a : AgreesExcept [.reg 2, .rip] v w := e2.agrees
  have sw := sv.after_registers ready2 e2a (by simp [Component.Covers]) (by simp)
  have dx : w.regValue .rdx = 1 := by
    have hvd : v.regValue .rdx = 1 := (e1.agrees.read (n := 64) (r := 2) (by simp)).trans rdx
    have hv8 : v.regValue .r8 = 1 := (e1.agrees.read (n := 64) (r := 8) (by simp)).trans r8
    have hw := e2.writes
    change w.regValue .rdx = (if condHolds 2 (StatusFlags.ofRFLAGS v.RFLAGS) then
      v.regValue .r8 else v.regValue .rdx) at hw
    rw [hw, hvd, hv8]
    simp
  obtain ⟨x, a3, ready3, e3⟩ :=
    (test_r64_r64_effect_step 0x103287 0x48 0xd2 (by simp [RexWPrefix]) rfl).advances ready2
      (programText_slice (programLoaded_codeIn sw.loaded) 0x3287 [0x48,0x85,0xd2]
        (by decide) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x328a (by decide)))
  change (testR64R64Effect 0x103287 2 2 w).Holds w x at e3
  have sx := sw.after_registers ready3 e3.agrees (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS x.RFLAGS).ZF = false := by
    have h := e3.flags.2.2.2.1
    change _ = ((w.regValue .rdx &&& w.regValue .rdx) == 0) at h
    simpa [dx] using h
  have next : (jccEffect 0x10328a 6 4 ((0x15b : BitVec 32).signExtend 64) x).rip = 0x103290 := by
    simp [jccEffect, branchEffect, condHolds, zf]
  obtain ⟨u, a4, ready4, e4⟩ := (jcc_rel32_effect_step 0x10328a 4 0x15b).advances ready3
    (programText_slice (programLoaded_codeIn sx.loaded) 0x328a
      [0x0f,0x84,0x5b,1,0,0] (by decide) (by decide +kernel))
    ⟨e3.rip, by intro h; decide +kernel⟩
    (by rw [next]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3290 (by decide)))
  have e4a : AgreesExcept [.rip] x u := e4.agrees
  have agr : AgreesExcept [.reg 2, .flags, .rip] t u :=
    (((e1.agrees.trans e2a).trans e3.agrees).trans e4a).mono (by simp)
  refine ⟨4, u, ((a1.trans a2).trans a3).trans a4,
    state.after_registers ready4 agr (by simp [Component.Covers]) (by simp),
    e4.rip.trans next, ?_, agr⟩
  exact (e4a.read (n := 64) (r := 2) (by simp)).trans
    ((e3.agrees.read (n := 64) (r := 2) (by simp)).trans dx)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
