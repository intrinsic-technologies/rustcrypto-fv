import P256.Proofs.Verifying.Message.Convert.Choice
import P256.Proofs.Verifying.Message.Convert.SelectionState
import P256.Proofs.Verifying.Message.Convert.Setup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure XSelected [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (xValue yValue : Nat) : Prop extends Selecting initial s boundary message xValue yValue where
  rip : s.RIP = 0x10da19
  outputX : MontgomeryAt s (frameBase initial + 1000) xValue

theorem select_x [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} (pre : Pre initial boundary message)
    (state : Chosen initial s boundary message x y) :
    ∃ t, XSelected initial t boundary message x y := by
  obtain ⟨fuel, v, runV, readyV, _, effectV⟩ := first_setup boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xda01 firstBytes
      (by decide) (by decide +kernel)) state.rip
  have contextV := state.toContext.after_registers runV readyV effectV.agrees
    (by simp [firstEffect, Effect.components, Component.Covers])
    (by simp [firstEffect, Effect.components]) (by simp [firstEffect, Effect.components])
    (by simp [firstEffect, Effect.components]) (by simp [firstEffect, Effect.components])
  have memoryV : v.external = s.external := effectV.agrees.external
    (by simp [firstEffect, Effect.components, Component.Covers])
  have stack : s.regValue .rsp = frameBase initial := state.rsp
  have choice : v.regValue .rbp = 0 := by
    have value : v.regValue .rbp = ((s.regValue .rax).setWidth 8).setWidth 64 := effectV.writes.1
    rw [value, state.choice]
    rfl
  have identityPointer : v.regValue .r15 = frameBase initial + 128 :=
    (effectV.agrees.read (n := 64) (r := 15) (by simp [firstEffect, Effect.components])).trans
      state.identityPointer
  have selecting : Selecting initial v boundary message x y := by
    refine ⟨contextV, ?_, ?_, identityPointer, choice, ?_, ?_, ?_, ?_⟩
    · exact (effectV.agrees.read (n := 64) (r := 3) (by simp [firstEffect, Effect.components])).trans state.yPointer
    · exact (effectV.agrees.read (n := 64) (r := 14) (by simp [firstEffect, Effect.components])).trans state.zPointer
    · exact state.x.of_bytes_eq (by intro i hi; rw [memoryV])
    · exact state.y.of_bytes_eq (by intro i hi; rw [memoryV])
    · exact state.z.of_bytes_eq (by intro i hi; rw [memoryV])
    · exact state.identity.of_bytes_eq (by intro i hi; rw [memoryV])
  have input : v.regValue .rsi = stackPtr initial - 1176 := by
    have value : v.regValue .rsi = s.regValue .rsp := effectV.writes.2.2.1
    rw [value, stack]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using frame_address initial 0 (by decide)
  have right : v.regValue .rdx = stackPtr initial - 1048 :=
    (effectV.writes.2.2.2.1.trans state.identityPointer).trans (frame_address initial 128 (by decide))
  have output : v.regValue .rdi = stackPtr initial - 176 := by
    have value : v.regValue .rdi = s.regValue .rsp + 1000 := effectV.writes.2.1
    rw [value, stack]
    exact frame_address initial 1000 (by decide)
  have xValue : MontgomeryAt v (stackPtr initial - 1176) x := by
    have value := selecting.x
    change MontgomeryAt v (frameBase initial + BitVec.ofNat 64 0) x at value
    rwa [frame_address initial 0 (by decide)] at value
  have identityValue : MontgomeryAt v (stackPtr initial - 1048) 0 := by
    have value := selecting.identity.1
    change MontgomeryAt v (frameBase initial + BitVec.ofNat 64 128) 0 at value
    rwa [frame_address initial 128 (by decide)] at value
  have flag : (v.regValue .rcx).setWidth 8 = 0 := by
    have value : v.regValue .rcx = ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64 :=
      effectV.writes.2.2.2.2
    rw [value, state.choice]
    rfl
  obtain ⟨t, result⟩ := select_call (select := false) pre.toCalleePre selecting.toFrameState
    firstSite effectV.rip input right output xValue identityValue flag
  have selected := selecting.after_select pre result (by decide)
  refine ⟨t, selected, result.rip, ?_⟩
  change MontgomeryAt t (frameBase initial + BitVec.ofNat 64 1000) x
  rw [frame_address initial 1000 (by decide)]
  exact result.value

end P256.Proofs.Verifying.Message.Convert
