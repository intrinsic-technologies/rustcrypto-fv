import P256.Proofs.SHA256.Return.Store

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.CrossPageStore (mov_m32_r32_effect_step_any mov_m32_r32_legacy_effect_step_any)

theorem store_output_words [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : OutputState initial current hash []) (rip : current.RIP = 0x11817c) :
    ∃ next, Advances boundary 8 current next ∧ ScalarFrame.FrameState initial next 32 336 336 ∧
      next.RIP = 0x118197 ∧ HashStateAt next (initial.regValue .rdi) hash := by
  obtain ⟨s1, run1, state1, rip1⟩ := output_store pre state (i := 1) (pc := 0x1817c)
    (reg := 14) (bytes := [0x44,0x89,0x77,0x04]) (by decide) rip state.registers.b
    (by decide +kernel) (by decide)
    (mov_m32_r32_effect_step_any 0x11817c 0x44 (by simp [RexNoWPrefix]) 6
      (.base 7 (.d8 4)) (by decide) rfl rfl)
  obtain ⟨s2, run2, state2, rip2⟩ := output_store pre state1 (i := 2) (pc := 0x18180)
    (reg := 0) (bytes := [0x89,0x47,0x08]) (by decide) rip1 state1.registers.c
    (by decide +kernel) (by decide)
    (mov_m32_r32_legacy_effect_step_any 0x118180 0 (.base 7 (.d8 8)) (by decide) rfl rfl)
  obtain ⟨s3, run3, state3, rip3⟩ := output_store pre state2 (i := 3) (pc := 0x18183)
    (reg := 9) (bytes := [0x44,0x89,0x4f,0x0c]) (by decide) rip2 state2.registers.d
    (by decide +kernel) (by decide)
    (mov_m32_r32_effect_step_any 0x118183 0x44 (by simp [RexNoWPrefix]) 1
      (.base 7 (.d8 12)) (by decide) rfl rfl)
  obtain ⟨s4, run4, state4, rip4⟩ := output_store pre state3 (i := 4) (pc := 0x18187)
    (reg := 8) (bytes := [0x44,0x89,0x47,0x10]) (by decide) rip3 state3.registers.e
    (by decide +kernel) (by decide)
    (mov_m32_r32_effect_step_any 0x118187 0x44 (by simp [RexNoWPrefix]) 0
      (.base 7 (.d8 16)) (by decide) rfl rfl)
  obtain ⟨s5, run5, state5, rip5⟩ := output_store pre state4 (i := 5) (pc := 0x1818b)
    (reg := 10) (bytes := [0x44,0x89,0x57,0x14]) (by decide) rip4 state4.registers.f
    (by decide +kernel) (by decide)
    (mov_m32_r32_effect_step_any 0x11818b 0x44 (by simp [RexNoWPrefix]) 2
      (.base 7 (.d8 20)) (by decide) rfl rfl)
  obtain ⟨s6, run6, state6, rip6⟩ := output_store pre state5 (i := 6) (pc := 0x1818f)
    (reg := 2) (bytes := [0x89,0x57,0x18]) (by decide) rip5 state5.registers.g
    (by decide +kernel) (by decide)
    (mov_m32_r32_legacy_effect_step_any 0x11818f 2 (.base 7 (.d8 24)) (by decide) rfl rfl)
  obtain ⟨s7, run7, state7, rip7⟩ := output_store pre state6 (i := 7) (pc := 0x18192)
    (reg := 1) (bytes := [0x89,0x4f,0x1c]) (by decide) rip6 state6.registers.h
    (by decide +kernel) (by decide)
    (mov_m32_r32_legacy_effect_step_any 0x118192 1 (.base 7 (.d8 28)) (by decide) rfl rfl)
  obtain ⟨next, run8, state8, rip8⟩ := output_store pre state7 (i := 0) (pc := 0x18195)
    (reg := 3) (bytes := [0x89,0x1f]) (by decide) rip7 state7.registers.a
    (by decide +kernel) (by decide)
    (mov_m32_r32_legacy_effect_step_any 0x118195 3 (.base 7 .none) (by decide) rfl rfl)
  refine ⟨next, (((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8),
    state8.toFrameState, rip8, state8.registers.size, ?_⟩
  intro i hi
  apply loadBytes32_of_bytes (state8.words i hi ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

end P256.Proofs.SHA256
