import P256.Proofs.Verifying.Message.Convert.SelectY

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Selected [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (xValue yValue : Nat) : Prop extends Selecting initial s boundary message xValue yValue where
  rip : s.RIP = 0x10da4d
  outputX : MontgomeryAt s (frameBase initial + 1000) xValue
  outputY : MontgomeryAt s (frameBase initial + 1032) yValue
  outputZ : MontgomeryAt s (frameBase initial + 1064) 1

theorem select_z [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} (pre : Pre initial boundary message)
    (state : XYSelected initial s boundary message x y) :
    ∃ t, Selected initial t boundary message x y := by
  obtain ⟨fuel, v, runV, readyV, _, effectV⟩ := third_setup boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xda33 thirdBytes
      (by decide) (by decide +kernel)) state.rip
  have selecting := state.toSelecting.after_registers runV readyV effectV.agrees
    (by simp [thirdEffect, Effect.components, Component.Covers])
    (by simp [thirdEffect, Effect.components]) (by simp [thirdEffect, Effect.components])
    (by simp [thirdEffect, Effect.components]) (by simp [thirdEffect, Effect.components])
    (by simp [thirdEffect, Effect.components]) (by simp [thirdEffect, Effect.components])
    (by simp [thirdEffect, Effect.components]) (by simp [thirdEffect, Effect.components])
  have memoryV : v.external = s.external := effectV.agrees.external
    (by simp [thirdEffect, Effect.components, Component.Covers])
  have stack : s.regValue .rsp = frameBase initial := state.rsp
  have input : v.regValue .rsi = stackPtr initial - 1112 := by
    have value : v.regValue .rsi = s.regValue .r14 := effectV.writes.2.2.1
    rw [value, state.zPointer]
    exact frame_address initial 64 (by decide)
  have right : v.regValue .rdx = stackPtr initial - 984 := by
    have value : v.regValue .rdx = s.regValue .rsp + 192 := effectV.writes.1
    rw [value, stack]
    exact frame_address initial 192 (by decide)
  have output : v.regValue .rdi = stackPtr initial - 112 := by
    have value : v.regValue .rdi = s.regValue .rsp + 1064 := effectV.writes.2.1
    rw [value, stack]
    exact frame_address initial 1064 (by decide)
  have zValue : MontgomeryAt v (stackPtr initial - 1112) 1 := by
    have value := selecting.z
    change MontgomeryAt v (frameBase initial + BitVec.ofNat 64 64) 1 at value
    rwa [frame_address initial 64 (by decide)] at value
  have identityValue : MontgomeryAt v (stackPtr initial - 984) 0 := by
    have value := selecting.identity.2.2
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at value
    change MontgomeryAt v (frameBase initial + BitVec.ofNat 64 192) 0 at value
    rwa [frame_address initial 192 (by decide)] at value
  have flag : (v.regValue .rcx).setWidth 8 = 0 := by
    have value : v.regValue .rcx = ((s.regValue .rbp).setWidth 32).setWidth 64 := effectV.writes.2.2.2
    rw [value, state.choice]
    rfl
  obtain ⟨t, result⟩ := select_call (select := false) pre.toCalleePre selecting.toFrameState
    thirdSite effectV.rip input right output zValue identityValue flag
  have selected := selecting.after_select pre result (by decide)
  refine ⟨t, selected, result.rip, ?_, ?_, ?_⟩
  · apply result.preserve_field (offset := 1000) (by decide) (by decide)
    exact state.outputX.of_bytes_eq (by intro i hi; rw [memoryV] <;> rfl)
  · apply result.preserve_field (offset := 1032) (by decide) (by decide)
    exact state.outputY.of_bytes_eq (by intro i hi; rw [memoryV] <;> rfl)
  · change MontgomeryAt t (frameBase initial + BitVec.ofNat 64 1064) 1
    rw [frame_address initial 1064 (by decide)]
    exact result.value

end P256.Proofs.Verifying.Message.Convert
