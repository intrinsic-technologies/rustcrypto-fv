import P256.Proofs.Projective.Multiply.Machine.Loop.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.CompareMemory.Register
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initial_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376) (rip : t.RIP = 0x103302)
    (r13 : t.regValue .r13 = 0)
    (counter : (Operand.mem (stackPtr s - 376) : Operand 64).read t = 65) :
    ∃ u, Advances boundary 4 t u ∧ FrameState s u 96 1400 376 ∧ u.RIP = 0x103313 ∧
      AgreesExcept [.reg 13, .reg 15, .flags, .rip] t u := by
  obtain ⟨v, a1, r1, e1⟩ :=
    (add_r64_imm8_effect_step 0x103302 0x49 0xc5 65 (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x3302 [0x49,0x83,0xc5,0x41]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3306 (by decide)))
  change (addR64Imm8Effect 0x103302 13 65 t).Holds t v at e1
  have sv := state.after_registers r1 e1.agrees (by simp [Component.Covers]) (by simp)
  have bpV : v.regValue .r13 = 65 := by
    have h : v.regValue .r13 = t.regValue .r13 + 65 := e1.writes
    rw [h, r13]
    rfl
  obtain ⟨w, a2, r2, e2⟩ :=
    (add_r64_imm32_effect_step 0x103306 0x49 0xc7 768 (by simp [RexWPrefix]) rfl rfl).advances r1
      (programText_slice (programLoaded_codeIn sv.loaded) 0x3306 [0x49,0x81,0xc7,0,3,0,0]
        (by decide) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x330d (by decide)))
  change (addR64Imm32Effect 0x103306 15 768 v).Holds v w at e2
  have sw := sv.after_registers r2 e2.agrees (by simp [Component.Covers]) (by simp)
  have bpW : w.regValue .r13 = 65 := (e2.agrees.read (n := 64) (r := 13) (by simp)).trans bpV
  have memW : w.external = t.external :=
    (e1.agrees.trans e2.agrees).external (by simp [Component.Covers])
  have readW : MemReadable w (stackPtr w) 8 := by
    simpa using stack_readable pre.toCalleePre sw (offset := 0) (len := 8) (by decide) (by decide)
  obtain ⟨x, a3, r3, e3⟩ :=
    (P256.Proofs.Common.Instructions.cmp_m64_r64_effect_step 0x10330d 0x4c (by simp [RexWPrefix]) 5
      (.sib 4 none 0 .none) (by decide +kernel) rfl rfl).advances r2
      (programText_slice (programLoaded_codeIn sw.loaded) 0x330d [0x4c,0x39,0x2c,0x24]
        (by decide) (by decide +kernel))
      ⟨e2.rip, by change MemReadable w (stackPtr w + 0) 8; simpa using readW⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3311 (by decide)))
  have agr3 : AgreesExcept [.flags, .rip] w x := e3.agrees
  have sx := sw.after_registers r3 agr3 (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS x.RFLAGS).ZF = true := by
    have h := e3.flags.2.2.2.1
    change _ = (((Operand.mem (stackPtr w + 0) : Operand 64).read w - w.regValue .r13) == 0) at h
    have count : (Operand.mem (stackPtr w + 0) : Operand 64).read w = 65 := by
      have address : stackPtr w + 0 = stackPtr s - 376 := by simpa using sw.rsp
      rw [address]
      change memLoad w.external _ 64 = _
      rw [memW]
      exact counter
    have count' : (Operand.mem (stackPtr w) : Operand 64).read w = 65 := by simpa using count
    simpa [count', bpW] using h
  have next : (jccEffect 0x103311 2 5 ((0x9d : BitVec 8).signExtend 64) x).rip = 0x103313 := by
    simp [jccEffect, branchEffect, condHolds, zf]
  obtain ⟨u, a4, r4, e4⟩ := (jcc_rel8_effect_step 0x103311 5 0x9d).advances r3
    (programText_slice (programLoaded_codeIn sx.loaded) 0x3311 [0x75,0x9d]
      (by decide) (by decide +kernel)) ⟨e3.rip, by intro h; decide +kernel⟩
    (by rw [next]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3313 (by decide)))
  have agr4 : AgreesExcept [.rip] x u := e4.agrees
  have agr : AgreesExcept [.reg 13, .reg 15, .flags, .rip] t u :=
    (((e1.agrees.trans e2.agrees).trans agr3).trans agr4).mono (by simp)
  exact ⟨u, ((a1.trans a2).trans a3).trans a4,
    state.after_registers r4 agr (by simp [Component.Covers]) (by simp),
    e4.rip.trans next, agr⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
