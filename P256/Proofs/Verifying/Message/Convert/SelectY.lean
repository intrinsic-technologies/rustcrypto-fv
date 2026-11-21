import P256.Proofs.Verifying.Message.Convert.SelectX

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure XYSelected [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (xValue yValue : Nat) : Prop extends Selecting initial s boundary message xValue yValue where
  rip : s.RIP = 0x10da33
  outputX : MontgomeryAt s (frameBase initial + 1000) xValue
  outputY : MontgomeryAt s (frameBase initial + 1032) yValue

theorem select_y [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} (pre : Pre initial boundary message)
    (state : XSelected initial s boundary message x y) :
    ∃ t, XYSelected initial t boundary message x y := by
  obtain ⟨fuel, v, runV, readyV, _, effectV⟩ := second_setup boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xda19 secondBytes
      (by decide) (by decide +kernel)) state.rip
  have selecting := state.toSelecting.after_registers runV readyV effectV.agrees
    (by simp [secondEffect, Effect.components, Component.Covers])
    (by simp [secondEffect, Effect.components]) (by simp [secondEffect, Effect.components])
    (by simp [secondEffect, Effect.components]) (by simp [secondEffect, Effect.components])
    (by simp [secondEffect, Effect.components]) (by simp [secondEffect, Effect.components])
    (by simp [secondEffect, Effect.components]) (by simp [secondEffect, Effect.components])
  have memoryV : v.external = s.external := effectV.agrees.external
    (by simp [secondEffect, Effect.components, Component.Covers])
  have stack : s.regValue .rsp = frameBase initial := state.rsp
  have input : v.regValue .rsi = stackPtr initial - 1144 := by
    have value : v.regValue .rsi = s.regValue .rbx := effectV.writes.2.2.1
    rw [value, state.yPointer]
    exact frame_address initial 32 (by decide)
  have right : v.regValue .rdx = stackPtr initial - 1016 := by
    have value : v.regValue .rdx = s.regValue .rsp + 160 := effectV.writes.1
    rw [value, stack]
    exact frame_address initial 160 (by decide)
  have output : v.regValue .rdi = stackPtr initial - 144 := by
    have value : v.regValue .rdi = s.regValue .rsp + 1032 := effectV.writes.2.1
    rw [value, stack]
    exact frame_address initial 1032 (by decide)
  have yValue : MontgomeryAt v (stackPtr initial - 1144) y := by
    have value := selecting.y
    change MontgomeryAt v (frameBase initial + BitVec.ofNat 64 32) y at value
    rwa [frame_address initial 32 (by decide)] at value
  have identityValue : MontgomeryAt v (stackPtr initial - 1016) 1 := by
    have value := selecting.identity.2.1
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at value
    change MontgomeryAt v (frameBase initial + BitVec.ofNat 64 160) 1 at value
    rwa [frame_address initial 160 (by decide)] at value
  have flag : (v.regValue .rcx).setWidth 8 = 0 := by
    have value : v.regValue .rcx = ((s.regValue .rbp).setWidth 32).setWidth 64 := effectV.writes.2.2.2
    rw [value, state.choice]
    rfl
  obtain ⟨t, result⟩ := select_call (select := false) pre.toCalleePre selecting.toFrameState
    secondSite effectV.rip input right output yValue identityValue flag
  have selected := selecting.after_select pre result (by decide)
  refine ⟨t, selected, result.rip, ?_, ?_⟩
  · apply result.preserve_field (offset := 1000) (by decide) (by decide)
    exact state.outputX.of_bytes_eq (by intro i hi; rw [memoryV] <;> rfl)
  · change MontgomeryAt t (frameBase initial + BitVec.ofNat 64 1032) y
    rw [frame_address initial 1032 (by decide)]
    exact result.value

end P256.Proofs.Verifying.Message.Convert
