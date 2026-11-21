import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Prologue
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Proofs.Program (saveFrame)

theorem guard_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109530 32 32 128) (stage : Stage s t boundary)
    (rip : t.RIP = 0x10953e) (count : t.regValue .rdx = 0) :
    ∃ u, Stage s u boundary ∧ u.RIP = 0x10954a ∧ AgreesExcept [.flags, .rip] t u := by
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (cmp_r32_imm32_effect_step 0x10953e 0xfa 256 rfl rfl).advances stage.ready
      (programText_slice (programLoaded_codeIn stage.loaded) 0x953e
        [0x81, 0xfa, 0, 1, 0, 0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9544 (by decide)))
  have frameU : AgreesExcept [.flags, .rip] t u := effectU.agrees
  have stageU := stage.of_effect pre runU readyU effectU
    (by intro c hc; simp only [cmpR32Imm32Effect_components, List.mem_cons,
          List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl <;> trivial)
    (by simp)
  have cf : (StatusFlags.ofRFLAGS u.RFLAGS).CF = true := by
    have h := effectU.flags.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide (((t.regValue .rdx).setWidth 32).toNat < 256) at h
    simpa [count] using h
  have next : (jccEffect 0x109544 6 3 ((0x199 : BitVec 32).signExtend 64) u).rip = 0x10954a := by
    change (if !(StatusFlags.ofRFLAGS u.RFLAGS).CF then (0x1096e3 : BitVec 64) else 0x10954a) = _
    rw [cf]
    rfl
  obtain ⟨v, runV, readyV, effectV⟩ :=
    (jcc_rel32_effect_step 0x109544 3 0x199).advances readyU
      (programText_slice (programLoaded_codeIn stageU.loaded) 0x9544
        [0x0f, 0x83, 0x99, 1, 0, 0] (by decide) (by decide +kernel))
      ⟨effectU.rip, fun _ => by decide⟩
      (by rw [next]; exact boundary_ne_program pre.outerBoundary
            (inProgram_of_textOffset 0x954a (by decide)))
  have stageV := stageU.of_effect pre runV readyV effectV
    (by intro c hc; change c ∈ [.rip] at hc; simp only [List.mem_singleton] at hc; subst c; trivial)
    (by change Component.reg 4 ∉ [.rip]; simp)
  have frameV : AgreesExcept [.rip] u v := effectV.agrees
  exact ⟨v, stageV, effectV.rip.trans next, (frameU.trans frameV).mono (by simp)⟩

theorem prologue_stack_covers [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    {c : Component} (hc : c ∈ saveFrame s ++ [.flags])
    {address : BitVec 64} (ha : c.Covers address) :
    (Stack.region s 128).Contains address.toNat := by
  simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact ha.elim
  · exact ha.elim
  · exact stack_contains pre (offset := 8) (by decide) (by decide) ha
  · exact stack_contains pre (offset := 16) (by decide) (by decide) ha
  · exact stack_contains pre (offset := 24) (by decide) (by decide) ha
  · exact stack_contains pre (offset := 32) (by decide) (by decide) ha
  · exact stack_contains pre (offset := 40) (by decide) (by decide) ha
  · exact stack_contains pre (offset := 48) (by decide) (by decide) ha
  · exact ha.elim

theorem prepare_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : CalleePre s boundary 0x109530 32 32 128) (count : s.regValue .rdx = 0)
    (integer : Nat256At s (s.regValue .rsi) value) :
    ∃ t a, PreparedState s t boundary a ∧ a.toNat = value := by
  obtain ⟨t, stage, rip, _, small⟩ := allocate_frame pre
  have countT : t.regValue .rdx = 0 :=
    (small.read (r := 2) (n := 64) (by simp [saveFrame])).trans count
  obtain ⟨u, stageU, ripU, frameU⟩ := guard_correct pre stage rip countT
  have inputT : Nat256At t (s.regValue .rsi) value := by
    refine ⟨integer.1, fun i hi => ?_⟩
    rw [small.byte]
    · exact integer.2 i hi
    · intro c hc ha
      exact (pre.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)) _
        (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
        (prologue_stack_covers pre hc ha)
  have memory : u.external = t.external := frameU.external (by simp [Component.Covers])
  have inputU : Nat256At u (s.regValue .rsi) value := by
    simpa only [Nat256At, memory] using inputT
  refine ⟨u, readLimbs u (s.regValue .rsi), ?_, readLimbs_toNat inputU⟩
  refine ⟨stageU, ripU, ?_, ?_, ?_, rfl⟩
  · exact (frameU.read (r := 6) (n := 64) (by simp)).trans
      (small.read (r := 6) (n := 64) (by simp [saveFrame]))
  · exact (frameU.read (r := 7) (n := 64) (by simp)).trans
      (small.read (r := 7) (n := 64) (by simp [saveFrame]))
  · exact (frameU.read (r := 2) (n := 64) (by simp)).trans countT

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
