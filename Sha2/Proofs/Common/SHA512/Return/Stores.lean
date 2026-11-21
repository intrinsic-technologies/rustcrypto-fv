import Sha2.Proofs.Common.SHA512.Return.Store

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem store_output_words [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt64} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : OutputState initial current hash []) (rip : current.RIP = 0x11181c) :
    ∃ next, Advances boundary 8 current next ∧ FrameState initial next ∧
      next.RIP = 0x11183b ∧ HashStateAt next (initial.regValue .rdi) hash := by
  obtain ⟨s1, run1, state1, rip1⟩ := output_store pre state (i := 1) (pc := 0x1181c)
    (reg := 1) (bytes := [0x48,0x89,0x4a,0x8]) (by decide) rip state.registers.b
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x11181c 0x48 (by simp [RexWPrefix]) 1
      (.base 2 (.d8 8)) (by decide) rfl rfl)
  obtain ⟨s2, run2, state2, rip2⟩ := output_store pre state1 (i := 2) (pc := 0x11820)
    (reg := 10) (bytes := [0x4c,0x89,0x52,0x10]) (by decide) rip1 state1.registers.c
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x111820 0x4c (by simp [RexWPrefix]) 2
      (.base 2 (.d8 16)) (by decide) rfl rfl)
  obtain ⟨s3, run3, state3, rip3⟩ := output_store pre state2 (i := 3) (pc := 0x11824)
    (reg := 0) (bytes := [0x48,0x89,0x42,0x18]) (by decide) rip2 state2.registers.d
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x111824 0x48 (by simp [RexWPrefix]) 0
      (.base 2 (.d8 24)) (by decide) rfl rfl)
  obtain ⟨s4, run4, state4, rip4⟩ := output_store pre state3 (i := 4) (pc := 0x11828)
    (reg := 3) (bytes := [0x48,0x89,0x5a,0x20]) (by decide) rip3 state3.registers.e
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x111828 0x48 (by simp [RexWPrefix]) 3
      (.base 2 (.d8 32)) (by decide) rfl rfl)
  obtain ⟨s5, run5, state5, rip5⟩ := output_store pre state4 (i := 5) (pc := 0x1182c)
    (reg := 9) (bytes := [0x4c,0x89,0x4a,0x28]) (by decide) rip4 state4.registers.f
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x11182c 0x4c (by simp [RexWPrefix]) 1
      (.base 2 (.d8 40)) (by decide) rfl rfl)
  obtain ⟨s6, run6, state6, rip6⟩ := output_store pre state5 (i := 6) (pc := 0x11830)
    (reg := 8) (bytes := [0x4c,0x89,0x42,0x30]) (by decide) rip5 state5.registers.g
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x111830 0x4c (by simp [RexWPrefix]) 0
      (.base 2 (.d8 48)) (by decide) rfl rfl)
  obtain ⟨s7, run7, state7, rip7⟩ := output_store pre state6 (i := 7) (pc := 0x11834)
    (reg := 13) (bytes := [0x4c,0x89,0x6a,0x38]) (by decide) rip6 state6.registers.h
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x111834 0x4c (by simp [RexWPrefix]) 5
      (.base 2 (.d8 56)) (by decide) rfl rfl)
  obtain ⟨next, run8, state8, rip8⟩ := output_store pre state7 (i := 0) (pc := 0x11838)
    (reg := 11) (bytes := [0x4c,0x89,0x1a]) (by decide) rip7 state7.registers.a
    (by decide +kernel) (by decide)
    (mov_m64_r64_effect_step 0x111838 0x4c (by simp [RexWPrefix]) 3
      (.base 2 .none) (by decide) rfl rfl)
  refine ⟨next, (((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8),
    state8.toFrameState, rip8, state8.registers.size, ?_⟩
  intro i hi
  apply (state8.words i hi ?_).loadBytes64
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

end Sha2.Proofs.Common.SHA512
