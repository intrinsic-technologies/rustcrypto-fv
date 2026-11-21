import P256.Proofs.Verifying.Combination.Loop.MultiMemory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem read_indices [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10efe1) (input : t.regValue .rsi = s.regValue .rsi) :
    ∃ w, Advances boundary 3 t w ∧ State s w ∧ w.RIP = 0x10efec ∧
      w.regValue .rax = s.regValue .rsi ∧ w.regValue .rdx = 0 ∧ w.regValue .rsi = 2 ∧
      AgreesExcept [.reg 0, .reg 2, .reg 6, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r64_r64_effect_step 0x10efe1 0x48 0xf0 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xefe1 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xefe4 (by decide)))
  have frameA : AgreesExcept [.reg 0, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have inputA : a.regValue .rsi = s.regValue .rsi :=
    (frameA.read (n := 64) (r := 6) (by simp)).trans input
  have axA : a.regValue .rax = s.regValue .rsi := effectA.writes.trans input
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (mov_r64_m64_effect_step 0x10efe4 0x48 (by simp [RexWPrefix]) 2
      (.base 6 (.d8 32)) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xefe4 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by
        change MemReadable a (a.regValue .rsi + 32) 8
        rw [inputA]
        exact metadata_readable pre stateA 32 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xefe8 (by decide)))
  have frameB : AgreesExcept [.reg 2, .rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB frameB (by simp [Component.Covers]) (by simp)
  have inputB : b.regValue .rsi = s.regValue .rsi :=
    (frameB.read (n := 64) (r := 6) (by simp)).trans inputA
  have dxB : b.regValue .rdx = 0 := by
    have h := effectB.writes
    change b.regValue .rdx = memLoad a.external (a.regValue .rsi + 32) 64 at h
    rw [inputA] at h
    exact h.trans ((metadata_read pre stateA 32 (by decide)).trans pre.startIndex)
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (mov_r64_m64_effect_step 0x10efe8 0x48 (by simp [RexWPrefix]) 6
      (.base 6 (.d8 40)) (by decide +kernel) rfl rfl).advances readyB
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xefe8 _
        (by decide) (by decide +kernel))
      ⟨effectB.rip, by
        change MemReadable b (b.regValue .rsi + 40) 8
        rw [inputB]
        exact metadata_readable pre stateB 40 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xefec (by decide)))
  have frameW : AgreesExcept [.reg 6, .rip] b w := effectW.agrees
  have frame : AgreesExcept [.reg 0, .reg 2, .reg 6, .rip] t w :=
    ((frameA.trans frameB).trans frameW).mono (by simp)
  refine ⟨w, (runA.trans runB).trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip,
    (frameW.read (n := 64) (r := 0) (by simp)).trans
      ((frameB.read (n := 64) (r := 0) (by simp)).trans axA),
    (frameW.read (n := 64) (r := 2) (by simp)).trans dxB, ?_, frame⟩
  have h := effectW.writes
  change w.regValue .rsi = memLoad b.external (b.regValue .rsi + 40) 64 at h
  rw [inputB] at h
  exact h.trans ((metadata_read pre stateB 40 (by decide)).trans pre.endIndex)

theorem compute_count [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10efec)
    (first : t.regValue .rdx = 0) (last : t.regValue .rsi = 2) :
    ∃ w, Advances boundary 2 t w ∧ State s w ∧ w.RIP = 0x10eff2 ∧
      w.regValue .rcx = 2 ∧
      (StatusFlags.ofRFLAGS w.RFLAGS).CF = false ∧
      (StatusFlags.ofRFLAGS w.RFLAGS).ZF = false ∧
      AgreesExcept [.reg 1, .flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r64_r64_effect_step 0x10efec 0x48 0xf1 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xefec _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xefef (by decide)))
  have frameA : AgreesExcept [.reg 1, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have countA : a.regValue .rcx = 2 := effectA.writes.trans last
  have firstA : a.regValue .rdx = 0 :=
    (frameA.read (n := 64) (r := 2) (by simp)).trans first
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (sub_r64_r64_effect_step 0x10efef 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xefef _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeff2 (by decide)))
  have frameW : AgreesExcept [.reg 1, .flags, .rip] a w := effectW.agrees
  have frame : AgreesExcept [.reg 1, .flags, .rip] t w :=
    (frameA.trans frameW).mono (by simp)
  refine ⟨w, runA.trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp),
    effectW.rip, ?_, ?_, ?_, frame⟩
  · have h := effectW.writes
    change w.regValue .rcx = a.regValue .rcx - a.regValue .rdx at h
    rw [countA, firstA] at h
    exact h.trans (by decide +kernel)
  · have h := effectW.flags.1
    change (StatusFlags.ofRFLAGS w.RFLAGS).CF =
      decide ((a.regValue .rcx).toNat < (a.regValue .rdx).toNat) at h
    rw [countA, firstA] at h
    exact h.trans (by decide +kernel)
  · have h := effectW.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS w.RFLAGS).ZF =
      (a.regValue .rcx - a.regValue .rdx == 0#64) at h
    rw [countA, firstA] at h
    exact h.trans (by decide +kernel)

end P256.Proofs.Verifying.Combination.Loop.Multi
