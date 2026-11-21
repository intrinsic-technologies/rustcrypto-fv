import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.State
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Zero
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Argument

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem zero_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : FrameState s t)
    (rip : t.RIP = 0x10fa6c) : ZeroPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    all_goals exact Program.ScalarFrame.stack_writable (frameOffset := 152) pre state (by decide) (by decide) (by decide)
  · intro off ho codeOffset codeLen hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    all_goals exact Program.ScalarFrame.stack_code (frameOffset := 152) pre state (by decide) (by decide) hb

theorem prepare_correct [Bindings] {s u : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : CopiedState s u boundary input) :
    ∃ t, EntryState s t boundary input := by
  obtain ⟨v, runV, readyV, ev⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_imm32_legacy_effect_step_any 0x10fa64
      (.sib 4 none 0 (.d8 4)) (by decide +kernel) rfl rfl 256).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xfa64 _
        (by decide +kernel) (by decide +kernel))
      ⟨state.rip, Program.ScalarFrame.stack_writable (frameOffset := 152) pre state.toFrameState (by decide) (offset := 4) (len := 4) (by decide) (by decide),
        Program.ScalarFrame.stack_code (frameOffset := 152) pre state.toFrameState (by decide) (offset := 4) (len := 4) (codeOffset := 0xfa64) (codeLen := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfa6c (by decide)))
  have fv : AgreesExcept [.mem (stackPtr u + 4) 4, .rip] u v := by
    have address : storeAddrAt 0x10fa64 (.sib 4 none 0 (.d8 4)) 8 u = stackPtr u + 4 := by
      x86_norm [stackPtr, Operand.read_reg64]
    simpa only [P256.Proofs.Common.Instructions.CrossPageStore.movM32Imm32LegacyEffect,
      storeEffect_components, Nat.reduceDiv, show 6 + (AddrMode.sib 4 none 0 (.d8 4)).tail.length = 8 by rfl,
      address] using ev.agrees
  have writesV : WritesWithin [.mem (stackPtr u + 4) 4, .rip]
      #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro c hc a hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have ha : stackPtr u + 4 = stackPtr s - 148 := Program.ScalarFrame.scalar_stack_address (frameOffset := 152) state.rsp (by decide) (by decide)
      rw [ha] at hv
      exact ⟨Program.ScalarFrame.workRegion s 288, by simp, Program.ScalarFrame.work_contains pre (by decide) (by decide) hv⟩
    · exact hv.elim
  have stateV := state.toStage.after pre runV readyV fv writesV (by simp) (by simp) (by simp)
  have spV : stackPtr v = stackPtr u := fv.read (n := 64) (r := 4) (by simp)
  obtain ⟨m, w, runW, readyW, _, ew⟩ := zero_correct boundary pre.outerBoundary v readyV
    (programText_slice (programLoaded_codeIn stateV.loaded) 0xfa6c zeroBytes
      (by decide +kernel) (by decide +kernel)) (zero_pre pre stateV.toFrameState ev.rip)
  have writesW : WritesWithin (zeroEffect v).components
      #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro c hc a hv
    simp only [zeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Nat.reduceDiv, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals refine ⟨Program.ScalarFrame.workRegion s 288, by simp, ?_⟩
    · change (Component.mem (stackPtr v + 64) 8).Covers a at hv
      have ha : stackPtr v + 64 = stackPtr s - 88 := Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateV.rsp (by decide) (by decide)
      rw [ha] at hv
      exact Program.ScalarFrame.work_contains pre (by decide) (by decide) hv
    · change (Component.mem (stackPtr v + 56) 8).Covers a at hv
      have ha : stackPtr v + 56 = stackPtr s - 96 := Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateV.rsp (by decide) (by decide)
      rw [ha] at hv
      exact Program.ScalarFrame.work_contains pre (by decide) (by decide) hv
    · change (Component.mem (stackPtr v + 48) 8).Covers a at hv
      have ha : stackPtr v + 48 = stackPtr s - 104 := Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateV.rsp (by decide) (by decide)
      rw [ha] at hv
      exact Program.ScalarFrame.work_contains pre (by decide) (by decide) hv
    · change (Component.mem (stackPtr v + 40) 8).Covers a at hv
      have ha : stackPtr v + 40 = stackPtr s - 112 := Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateV.rsp (by decide) (by decide)
      rw [ha] at hv
      exact Program.ScalarFrame.work_contains pre (by decide) (by decide) hv
  have stateW := stateV.after pre runW readyW ew.agrees writesW
    (by simp [zeroEffect, Effect.components]) (by simp [zeroEffect, Effect.components])
    (by simp [zeroEffect, Effect.components])
  obtain ⟨k, t, runT, readyT, _, et⟩ := argument_correct boundary pre.outerBoundary
    w readyW (programText_slice (programLoaded_codeIn stateW.loaded) 0xfa90 argumentBytes
      (by decide +kernel) (by decide +kernel)) ew.rip
  have stateT := stateW.after_registers runT readyT et.agrees
    (by simp [argumentEffect, Effect.components, Component.Covers])
    (by simp [argumentEffect, Effect.components]) (by simp [argumentEffect, Effect.components])
    (by simp [argumentEffect, Effect.components])
  refine ⟨t, ⟨stateT, et.rip,
    et.writes.1.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateW.rsp (by decide) (by decide)),
    et.writes.2.1.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 152) stateW.rsp (by decide) (by decide)),
    et.writes.2.2.1, et.writes.2.2.2.1, et.writes.2.2.2.2,
    state.bytes.1, ?_⟩⟩
  intro i
  have hi : i.val < 32 := by have := i.isLt; have size : input.size = 32 := state.bytes.1; omega
  have frame : AgreesExcept [.mem (stackPtr u + 4) 4, .mem (stackPtr u + 64) 8,
      .mem (stackPtr u + 56) 8, .mem (stackPtr u + 48) 8, .mem (stackPtr u + 40) 8,
      .reg 7, .reg 2, .reg 6, .reg 1, .reg 8, .rip] u t := by
    apply ((fv.trans ew.agrees).trans et.agrees).mono
    simp [zeroEffect, argumentEffect, Effect.components, spV]
  change t.external[BitVec.ofNat 64 ((stackPtr s - 80).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, frame.byte]
  · have h := state.bytes.2 i
    change u.external[BitVec.ofNat 64 ((stackPtr s - 80).toNat + i.val)]? = _ at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  · intro c hc hv
    have base : stackPtr s - 80 = stackPtr u + 72 := (Program.ScalarFrame.scalar_stack_address (frameOffset := 152) state.rsp (by decide) (offset := 72) (by decide)).symm
    rw [base] at hv
    have no {off len : Nat} (bound : off + len ≤ 72)
        (cover : (Component.mem (stackPtr u + BitVec.ofNat 64 off) len).Covers
          (stackPtr u + 72 + BitVec.ofNat 64 i.val)) : False := by
      obtain ⟨j, hj, he⟩ := cover
      exact (RangeApart.offsets (stackPtr u) (a := off) (b := 72) (len := len) (count := 32)
        (by omega) (by decide) (.inl bound)) j hj i.val hi he.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no (off := 4) (len := 4) (by decide) hv
    · exact no (off := 64) (len := 8) (by decide) hv
    · exact no (off := 56) (len := 8) (by decide) hv
    · exact no (off := 48) (len := 8) (by decide) hv
    · exact no (off := 40) (len := 8) (by decide) hv
    all_goals exact hv.elim

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
