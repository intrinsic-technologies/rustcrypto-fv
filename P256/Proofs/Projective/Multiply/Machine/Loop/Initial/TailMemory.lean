import P256.Proofs.Projective.Multiply.Machine.Loop.Interface
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Counter
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem tail_install [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (rip : t.RIP = 0x10332a)
    (counter : (Operand.mem (stackPtr s - 376) : Operand 64).read t = 65) :
    ∃ u, Advances boundary 3 t u ∧ FrameState s u 96 1400 376 ∧ u.RIP = 0x103340 ∧
      u.regValue .r14 = 65 ∧
      (Operand.mem (stackPtr s - 352) : Operand 64).read u = t.regValue .rbx ∧
      AgreesExcept [.mem (stackPtr s - 352) 8, .reg 14, .rip] t u := by
  obtain ⟨v, a1, ready1, e1⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x10332a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24))
      (by decide) rfl rfl).advances (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x332a [0x48,0x89,0x5c,0x24,0x18]
        (by decide) (by decide +kernel))
      ⟨rip, stack_writable pre.toCalleePre state (by decide) (by decide) (by decide),
        stack_code pre.toCalleePre state (offset := 24) (len := 8)
          (codeOffset := 0x332a) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x332f (by decide)))
  have address : stackPtr t + 24 = stackPtr s - 352 :=
    scalar_stack_address state.rsp (by decide) (by decide)
  have agr1 : AgreesExcept [.mem (stackPtr s - 352) 8, .rip] t v := by
    have h := e1.agrees
    simp only [movM64R64Effect_components] at h
    change AgreesExcept [.mem (stackPtr t + 24) 8, .rip] t v at h
    rwa [address] at h
  have writes : WritesWithin [.mem (stackPtr s - 352) 8, .rip]
      #v[registerRegion s .rdi 96, workRegion s 1400] := by
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, work_contains pre.toCalleePre (by decide) (by decide) covered⟩
    · exact covered.elim
  have frame := state.after_effect pre.toCalleePre (by decide) ready1 agr1 writes (by simp)
  have stored : (Operand.mem (stackPtr s - 352) : Operand 64).read v = t.regValue .rbx := by
    have h := e1.writes
    change (Operand.mem (stackPtr t + 24) : Operand 64).read v = t.regValue .rbx at h
    rwa [address] at h
  have countV : (Operand.mem (stackPtr s - 376) : Operand 64).read v = 65 := by
    change memLoad v.external _ 64 = _
    rw [memLoad_agrees_apart agr1]
    · exact counter
    · intro a len member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, or_false] at member
      obtain ⟨rfl, rfl⟩ := member
      exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide)
        (Or.inr (by decide))
  obtain ⟨w, a2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x10332f 0x4c (by simp [RexWPrefix]) 6
      (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready1
      (programText_slice (programLoaded_codeIn frame.loaded) 0x332f [0x4c,0x8b,0x34,0x24]
        (by decide) (by decide +kernel))
      ⟨e1.rip, stack_readable pre.toCalleePre frame (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3333 (by decide)))
  have agr2 : AgreesExcept [.reg 14, .rip] v w := e2.agrees
  have frameW := frame.after_registers ready2 agr2 (by simp [Component.Covers]) (by simp)
  have r14 : w.regValue .r14 = 65 := by
    have h := e2.writes
    change w.regValue .r14 = (Operand.mem (stackPtr v + 0) : Operand 64).read v at h
    have addr : stackPtr v + 0 = stackPtr s - 376 := by simpa using frame.rsp
    rw [addr] at h
    exact h.trans countV
  obtain ⟨u, a3, ready3, e3⟩ :=
    (nop_m_effect_step 0x103333 [0x66,0x66,0x66,0x66,0x2e]
      (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl).advances ready2
      (programText_slice (programLoaded_codeIn frameW.loaded) 0x3333
        [0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]
        (by decide) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x3340 (by decide)))
  have agr3 : AgreesExcept [.rip] w u := e3.agrees
  have memory := (agr2.trans agr3).external (by simp [Component.Covers])
  refine ⟨u, (a1.trans a2).trans a3,
    frameW.after_registers ready3 agr3 (by simp [Component.Covers]) (by simp), e3.rip,
    (agr3.read (n := 64) (r := 14) (by simp)).trans r14, ?_,
    ((agr1.trans agr2).trans agr3).mono (by simp)⟩
  change memLoad u.external _ 64 = _
  rw [memory]
  exact stored

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
