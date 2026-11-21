import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem choice [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x1100b1) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧ u.RIP = 0x1100b6 ∧
      u.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept (ScalarFrame.choiceClobbers s 408) t u := by
  obtain ⟨u, run, ready, sp, ip, ax, agrees⟩ := ScalarFrame.choice_step pre
    (frameOffset := 408) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp
    0x100b1 0x8fba (by decide) (by decide +kernel) (by decide) rip
  have narrow : AgreesExcept [.reg 0, .flags, .rip,
      .mem (stackPtr s - 416) 8, .mem (stackPtr s - 417) 1] t u := by
    apply agrees.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0, .flags, .rip,
      .mem (stackPtr s - 416) 8, .mem (stackPtr s - 417) 1]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨ScalarFrame.workRegion s 2592, by simp,
      ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  exact ⟨u, run, state.after_effect pre (by decide) ready narrow writes
    (by simp), ip, ax, agrees⟩


theorem choice_keeps_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592)
    (agrees : AgreesExcept (ScalarFrame.choiceClobbers s 408) t u)
    {i : Nat} (hi : i < 80) :
    u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  have writes : WritesWithin (ScalarFrame.choiceClobbers s 408) #v[Stack.region s 2592] := by
    intro c hc a ha
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨_, by simp, ScalarFrame.stack_contains pre (by decide) (by decide) ha⟩
  apply frame_read (agrees.memoryWriteFrame writes) (region := registerRegion s .rdi 80)
  · intro other member
    have he : other = Stack.region s 2592 := by simpa using member
    subst other
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
  · exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi


end P256.Proofs.Sec1.Decompress.Output
