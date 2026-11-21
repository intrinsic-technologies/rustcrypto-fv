import P256.Proofs.Verifying.Message.Convert.Identity
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Common.Instructions.LegacyLoad

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.LegacyLoad

structure Chosen [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (x y : Nat) : Prop extends Context initial s boundary message where
  rip : s.RIP = 0x10da01
  yPointer : s.regValue .rbx = frameBase initial + 32
  zPointer : s.regValue .r14 = frameBase initial + 64
  identityPointer : s.regValue .r15 = frameBase initial + 128
  x : MontgomeryAt s (frameBase initial + 0) x
  y : MontgomeryAt s (frameBase initial + 32) y
  z : MontgomeryAt s (frameBase initial + 64) 1
  identity : ProjectiveAt s (frameBase initial + 128) Projective.identity
  choice : (s.regValue .rax).setWidth 8 = 0

theorem choose [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y r scalarS : Nat} (pre : Pre initial boundary message)
    (input : InputAt initial (.affine x y) r scalarS)
    (state : IdentityCopied initial s boundary message x y) :
    ∃ t, Chosen initial t boundary message x y := by
  have readable : MemReadable s (s.regValue .rdx + 64) 4 := by
    rw [state.source]
    exact key_readable pre state.toFrameState (by decide)
  obtain ⟨v, runV, readyV, effectV⟩ :=
    (mov_r32_m32_legacy_effect_step 0x10d9f9 7 (.base 2 (.d8 64)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xd9f9 _
        (by decide) (by decide +kernel)) ⟨state.rip, readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd9fc (by decide)))
  change (movR32M32LegacyEffect 0x10d9f9 7 (.base 2 (.d8 64)) s).Holds s v at effectV
  have contextV := state.toContext.after_registers runV readyV effectV.agrees
    (by simp [movR32M32LegacyEffect, Effect.components, Component.Covers])
    (by simp [movR32M32LegacyEffect, Effect.components])
    (by simp [movR32M32LegacyEffect, Effect.components])
    (by simp [movR32M32LegacyEffect, Effect.components])
    (by simp [movR32M32LegacyEffect, Effect.components])
  have memoryV : v.external = s.external := effectV.agrees.external
    (by simp [movR32M32LegacyEffect, Effect.components, Component.Covers])
  have di : (v.regValue .rdi).setWidth 8 = 0 := by
    have value : v.regValue .rdi = (memLoad s.external (s.regValue .rdx+64) 32).setWidth 64 := effectV.writes
    rw [value, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), state.source]
    have key := (input_preserved pre input state.stackFrame).1
    simpa only [reduceCtorEq, ite_false] using key_flag key
  obtain ⟨t, runT, readyT, sp, ip, ax, agrees⟩ := ScalarFrame.choice_step pre.toCalleePre
    (frameOffset := 1176) (by decide) (by decide) readyV contextV.loaded contextV.allocated contextV.rsp
    0xd9fc 0xb66f (by decide) (by decide +kernel) (by decide) effectV.rip
  have narrow : AgreesExcept [.reg 0, .flags, .rip,
      .mem (stackPtr initial-1184) 8, .mem (stackPtr initial-1185) 1] v t := by
    apply agrees.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0, .flags, .rip,
      .mem (stackPtr initial-1184) 8, .mem (stackPtr initial-1185) 1]
      #v[workRegion initial 9992] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion initial 9992, by simp,
      work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  have frame := contextV.toFrameState.after_effect pre.toCalleePre (by decide) readyT narrow
    (by
      intro c hc a ha
      obtain ⟨region, member, inside⟩ := writes c hc a ha
      exact ⟨region, by simpa using Or.inr member, inside⟩) (by simp)
  have keep (offset len : Nat) (bound : offset + len ≤ 1176) {i : Nat} (hi : i < len) :
      t.external[frameBase initial+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        v.external[frameBase initial+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    rw [frame_address initial offset (by omega)]
    apply agrees.byte
    intro c hc covered
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j, hj, eq⟩ := covered
    · exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) (by omega)
        (.inl (by omega)) j hj i hi eq.symm
    · exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) (by omega)
        (.inl (by omega)) j hj i hi eq.symm
  have context := contextV.advance runT frame
    (work_frame_stack pre.toCalleePre (narrow.memoryWriteFrame writes))
    (fun i hi => keep 384 88 (by decide) hi)
  have keepOriginal (offset len : Nat) (bound : offset + len ≤ 1176) :
      ∀ i < len, t.external[frameBase initial+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        s.external[frameBase initial+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro i hi
    rw [← memoryV]
    exact keep offset len bound hi
  refine ⟨t, context, ip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp [choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 3) (by simp [movR32M32LegacyEffect, Effect.components])).trans state.yPointer)
  · exact (agrees.read (n := 64) (r := 14) (by simp [choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 14) (by simp [movR32M32LegacyEffect, Effect.components])).trans state.zPointer)
  · exact (agrees.read (n := 64) (r := 15) (by simp [choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 15) (by simp [movR32M32LegacyEffect, Effect.components])).trans state.identityPointer)
  · exact state.x.of_bytes_eq (keepOriginal 0 32 (by decide))
  · exact state.y.of_bytes_eq (keepOriginal 32 32 (by decide))
  · exact state.z.of_bytes_eq (keepOriginal 64 32 (by decide))
  · apply state.identity.of_bytes_eq
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using keepOriginal 128 96 (by decide)
  · rw [ax, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    exact di

end P256.Proofs.Verifying.Message.Convert
