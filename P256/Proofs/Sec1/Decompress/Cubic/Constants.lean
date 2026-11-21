import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Sec1.Decompress.Cubic.StoreA
import P256.Proofs.Sec1.Decompress.Cubic.StoreB

set_option autoImplicit false

open P256.Proofs.Sec1.Decompress.Cubic (APre aBytes aEffect store_a)

namespace P256.Proofs.Sec1.Decompress.Cubic
open P256.Proofs.Program P256.Proofs.Field P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def constantComponents (s : RamState) : List Component :=
  [.reg 0, .rip, .mem (stackPtr s - 408) 32]

theorem constant_frame [Bindings] {s t u : RamState} (state : FrameState s t)
    (frame : AgreesExcept [.reg 0, .mem (stackPtr t+0) 8, .mem (stackPtr t+8) 8,
      .mem (stackPtr t+16) 8, .mem (stackPtr t+24) 8, .rip] t u) :
    AgreesExcept (constantComponents s) t u := by
  apply agrees_of_footprint frame
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [constantComponents]
    all_goals simp [Component.isMem] at hm
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s - 408) 32, by simp [constantComponents], ?_⟩
      rw [state.rsp]
    · exact ⟨i, by omega, by
        change (stackPtr s - 408#64) + 0#64 + BitVec.ofNat 64 i =
          (stackPtr s - 408#64) + BitVec.ofNat 64 i
        rw [BitVec.add_zero]⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem constant_after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (ready : ReadyToStep u) (frame : AgreesExcept (constantComponents s) t u) :
    FrameState s u := by
  apply ScalarFrame.FrameState.after_effect pre (by decide) state ready frame ?_ (by simp [constantComponents])
  intro c hc a ha
  simp only [constantComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · exact ha.elim
  · exact ⟨ScalarFrame.workRegion s 2592, by simp, ScalarFrame.work_contains pre (by decide) (by decide) ha⟩

theorem store_a_value [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (rip : t.RIP = 0x10fe25) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10fe54 ∧
      MontgomeryAt u (stackPtr s - 408) P256.Spec.Operations.domain.a ∧
      AgreesExcept (constantComponents s) t u := by
  have hp : APre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      have bound : i.toNat + 8 ≤ 408 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        ScalarFrame.stack_writable pre state (by decide) bound (by decide)
    · intro i hi off len hc
      have bound : i.toNat + 8 ≤ 408 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_code pre state (by decide) bound hc
  obtain ⟨fuel, u, run, ready, _, effect⟩ := store_a boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfe25 aBytes
      (by decide +kernel) (by decide +kernel)) hp
  have frame : AgreesExcept (constantComponents s) t u := by
    apply constant_frame state
    apply effect.agrees.mono
    simp [aEffect, Effect.components, Write.component, Operand.component]
  have stateU := constant_after pre state ready frame
  refine ⟨fuel, u, run, stateU, effect.rip, ?_, frame⟩
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at values
  rcases values with ⟨_, h24, h8, h16, h0⟩
  change memLoad u.external (stackPtr t + 0#64) 64 = 0xfffffffffffffffc#64 at h0
  change memLoad u.external (stackPtr t + 8#64) 64 = 0x3ffffffff#64 at h8
  change memLoad u.external (stackPtr t + 16#64) 64 = 0#64 at h16
  change memLoad u.external (stackPtr t + 24#64) 64 = 0xfffffffc00000004#64 at h24
  have allocated := ScalarFrame.stack_readable pre stateU (by decide) (offset := 0) (len := 32) (by decide)
  rw [BitVec.add_zero, stateU.rsp] at allocated
  have hread : Field.readLimbs u (stackPtr s - 408) =
      ⟨0xfffffffffffffffc#64, 0x3ffffffff#64, 0#64, 0xfffffffc00000004#64⟩ := by
    unfold Field.readLimbs
    congr 1
    · have hh := h0
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408) 64 = _
      simpa only [BitVec.add_zero] using hh
    · have hh := h8
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408 + 8#64) 64 = _
      exact hh
    · have hh := h16
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408 + 16#64) 64 = _
      exact hh
    · have hh := h24
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408 + 24#64) 64 = _
      exact hh
  have nat := Field.nat256At_readLimbs allocated.mem
  rw [hread] at nat
  have value : (P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk 0xfffffffffffffffc#64 0x3ffffffff#64 0#64 0xfffffffc00000004#64).toNat =
      P256.Spec.Operations.domain.a * 2^256 % P256.Spec.Operations.domain.p := by decide +kernel
  rw [value] at nat
  exact ⟨by decide +kernel, nat⟩

theorem store_b_value [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (rip : t.RIP = 0x10fe7d) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10feb8 ∧
      MontgomeryAt u (stackPtr s - 408) P256.Spec.Operations.domain.b ∧
      AgreesExcept (constantComponents s) t u := by
  have hp : BPre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      have bound : i.toNat + 8 ≤ 408 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        ScalarFrame.stack_writable pre state (by decide) bound (by decide)
    · intro i hi off len hc
      have bound : i.toNat + 8 ≤ 408 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_code pre state (by decide) bound hc
  obtain ⟨fuel, u, run, ready, _, effect⟩ := store_b boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfe7d bBytes
      (by decide +kernel) (by decide +kernel)) hp
  have frame : AgreesExcept (constantComponents s) t u := by
    apply constant_frame state
    apply effect.agrees.mono
    simp [bEffect, Effect.components, Write.component, Operand.component]
  have stateU := constant_after pre state ready frame
  refine ⟨fuel, u, run, stateU, effect.rip, ?_, frame⟩
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at values
  rcases values with ⟨_, h24, h16, h8, h0⟩
  change memLoad u.external (stackPtr t + 0#64) 64 = 0xd89cdf6229c4bddf#64 at h0
  change memLoad u.external (stackPtr t + 8#64) 64 = 0xacf005cd78843090#64 at h8
  change memLoad u.external (stackPtr t + 16#64) 64 = 0xe5a220abf7212ed6#64 at h16
  change memLoad u.external (stackPtr t + 24#64) 64 = 0xdc30061d04874834#64 at h24
  have allocated := ScalarFrame.stack_readable pre stateU (by decide) (offset := 0) (len := 32) (by decide)
  rw [BitVec.add_zero, stateU.rsp] at allocated
  have hread : Field.readLimbs u (stackPtr s - 408) =
      ⟨0xd89cdf6229c4bddf#64, 0xacf005cd78843090#64, 0xe5a220abf7212ed6#64, 0xdc30061d04874834#64⟩ := by
    unfold Field.readLimbs
    congr 1
    · have hh := h0
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408) 64 = _
      simpa only [BitVec.add_zero] using hh
    · have hh := h8
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408 + 8#64) 64 = _
      exact hh
    · have hh := h16
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408 + 16#64) 64 = _
      exact hh
    · have hh := h24
      rw [state.rsp] at hh
      change memLoad u.external (stackPtr s - 408 + 24#64) 64 = _
      exact hh
  have nat := Field.nat256At_readLimbs allocated.mem
  rw [hread] at nat
  have value : (P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk 0xd89cdf6229c4bddf#64 0xacf005cd78843090#64 0xe5a220abf7212ed6#64 0xdc30061d04874834#64).toNat =
      P256.Spec.Operations.domain.b * 2^256 % P256.Spec.Operations.domain.p := by decide +kernel
  rw [value] at nat
  exact ⟨by decide +kernel, nat⟩

end P256.Proofs.Sec1.Decompress.Cubic
