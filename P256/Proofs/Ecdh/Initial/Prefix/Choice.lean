import P256.Proofs.Ecdh.Initial.Prefix.Copy
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Common.Instructions.LegacyLoad

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Standards.SECG.ECC
open P256.Proofs.Common.Instructions.LegacyLoad

theorem choice [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Curve.Point}
    (pre : Ecdh.Pre s boundary) (state : IdentityCopied s t point)
    (peer : Sec1.AffineAt s (s.regValue .rdx) point) :
    ∃ u, Advances boundary 7 t u ∧ Copied s u point := by
  have readable : MemReadable t (t.regValue .rdx + 64) 4 := by
    rw [state.peer]
    exact peer_readable pre state.toFrameState (by decide)
  obtain ⟨v,runV,readyV,effectV⟩ :=
    (mov_r32_m32_legacy_effect_step 0x1000de 7 (.base 2 (.d8 64)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xde _
        (by decide) (by decide +kernel)) ⟨state.rip,readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe1 (by decide)))
  change (movR32M32LegacyEffect 0x1000de 7 (.base 2 (.d8 64)) t).Holds t v at effectV
  have frameV := state.toFrameState.after_registers readyV effectV.agrees
    (by simp [movR32M32LegacyEffect,Effect.components,Component.Covers])
    (by simp [movR32M32LegacyEffect,Effect.components])
  have memoryV : v.external = t.external := effectV.agrees.external
    (by simp [movR32M32LegacyEffect,Effect.components,Component.Covers])
  have di : (v.regValue .rdi).setWidth 8 = if point = .infinity then 1 else 0 := by
    have value : v.regValue .rdi = (memLoad t.external (t.regValue .rdx+64) 32).setWidth 64 :=
      effectV.writes
    rw [value,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),state.peer]
    exact peer_flag pre state.toFrameState peer
  obtain ⟨u,runU,readyU,sp,ip,ax,agrees⟩ := ScalarFrame.choice_step pre.toCalleePre
    (frameOffset := 2056) (by decide) (by decide) readyV frameV.loaded frameV.allocated frameV.rsp
    0xe1 0x18f8a (by decide) (by decide +kernel) (by decide) effectV.rip
  have narrow : AgreesExcept [.reg 0,.flags,.rip,
      .mem (stackPtr s-2064) 8,.mem (stackPtr s-2065) 1] v u := by
    apply agrees.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0,.flags,.rip,
      .mem (stackPtr s-2064) 8,.mem (stackPtr s-2065) 1]
      #v[registerRegion s .rdi 32,workRegion s 3464] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s 3464,by simp,work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  have frameU := frameV.after_effect pre.toCalleePre (by decide) readyU narrow writes (by simp)
  have keep (offset len : Nat) (ho : offset ≤ 2056) (hl : len ≤ offset+8) {i : Nat} (hi : i < len) :
      u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    rw [← memoryV]
    apply agrees.byte
    intro c hc covered
    simp only [ScalarFrame.choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,eq⟩ := covered
    · exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) hl (.inl (by omega)) j hj i hi eq.symm
    · exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) hl (.inl (by omega)) j hj i hi eq.symm
  refine ⟨u,runV.trans runU,frameU,ip,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp [ScalarFrame.choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 3) (by simp [movR32M32LegacyEffect,Effect.components])).trans state.output)
  · have eq : memLoad u.external (frameBase s+8) 64 = memLoad t.external (frameBase s+8) 64 := by
      rw [show frameBase s+8 = stackPtr s-2048 from frame_address s 8 (by decide)]
      apply memLoad_congr
      intro i hi
      change (u.external[stackPtr s-2048#64+BitVec.ofNat 64 i]?).getD 0 = _
      rw [keep 2048 8 (by decide) (by decide) hi]
      rfl
    exact eq.trans state.scalar
  · apply state.source.of_bytes_eq
    intro i hi
    rw [show frameBase s+248 = stackPtr s-1808 from frame_address s 248 (by decide)]
    exact keep 1808 96 (by decide) (by decide) hi
  · apply state.identity.of_bytes_eq
    intro i hi
    rw [show frameBase s+1016 = stackPtr s-1040 from frame_address s 1016 (by decide)]
    exact keep 1040 96 (by decide) (by decide) hi
  · exact (agrees.read (n := 64) (r := 14) (by simp [ScalarFrame.choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 14) (by simp [movR32M32LegacyEffect,Effect.components])).trans state.r14)
  · exact (agrees.read (n := 64) (r := 12) (by simp [ScalarFrame.choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 12) (by simp [movR32M32LegacyEffect,Effect.components])).trans state.r12)
  · exact (agrees.read (n := 64) (r := 13) (by simp [ScalarFrame.choiceClobbers])).trans
      ((effectV.agrees.read (n := 64) (r := 13) (by simp [movR32M32LegacyEffect,Effect.components])).trans state.r13)
  · change (u.regValue .rax).setWidth 8 = _
    rw [ax,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    exact di

end P256.Proofs.Ecdh.Initial.Prefix
