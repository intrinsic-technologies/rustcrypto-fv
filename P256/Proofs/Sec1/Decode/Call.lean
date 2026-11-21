import P256.Proofs.Sec1.Decode.Frame
import P256.Proofs.Sec1.EncodedPoint
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.ScalarFrame.CallStep

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure AffineCallReady [Bindings] (initial s : RamState) (bytes : ByteArray) : Prop
    extends Frame initial s where
  rip : s.RIP = 0x10e62d
  source : s.regValue .rsi = stackPtr initial - 156
  destination : s.regValue .rdi = stackPtr initial - 312
  encoded : EncodedPointAt s (stackPtr initial - 156) bytes

def affineLayout : StackCallLayout 3680 65 80 3360 :=
  ⟨320, 156, 312, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem affine_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) (state : AffineCallReady s t bytes) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ ↦ 0x1100d0) 0x10e632 t).Holds t v ∧ AffineDecodePre v boundary bytes := by
  obtain ⟨v, run, ready, loaded, effect, _⟩ := call_rel32_exists pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated 312 0xe62d 0x1a9e state.rsp state.rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x100d0 (by decide))
  change (callEffect (fun _ ↦ 0x1100d0) 0x10e632 t).Holds t v at effect
  have source : v.regValue .rsi = stackPtr s - 156 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.source
  have destination : v.regValue .rdi = stackPtr s - 312 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have sp : stackPtr v = stackPtr s - 320 := by
    have h : stackPtr v = stackPtr t - 8 := effect.writes.1
    rw [h, state.rsp, BitVec.sub_sub]
    rfl
  have ret : InProgram (returnBoundary v).rip := by
    change InProgram (stackTop v)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0xe632 (by decide)
  refine ⟨v, run, ready, effect,
    CalleePre.of_stack pre.toCalleePre affineLayout
      (bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees)
      (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
      (effect.agrees.directionFlagClear (by simp) state.directionFlag) loaded
      (fun a ha ↦ effect.agrees.grow a (state.allocated a ha)) effect.rip sp source destination ret,
    ?_⟩
  rw [source]
  refine ⟨state.encoded.1, ?_⟩
  intro i hi
  exact (ScalarFrame.call_byte (frameOffset := 312) (by decide) state.rsp effect
    (offset := 156) (len := 65) (by decide) (by decide) hi).trans (state.encoded.2 i hi)

theorem affine_result [Bindings] {s t v u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre s boundary bytes) (state : AffineCallReady s t bytes)
    (effect : (callEffect (fun _ ↦ 0x1100d0) 0x10e632 t).Holds t v)
    (result : CalleeResult v u boundary 80 3360)
    (affine : AffineResultAt u (v.regValue .rdi) (P256.Spec.Points.decodePoint bytes)) :
    Frame s u ∧ u.RIP = 0x10e632 ∧
      AffineResultAt u (stackPtr s - 312) (P256.Spec.Points.decodePoint bytes) := by
  have sp : stackPtr v = stackPtr s - 320 := by
    have h : stackPtr v = stackPtr t - 8 := effect.writes.1
    rw [h, state.rsp, BitVec.sub_sub]
    rfl
  have destination : v.regValue .rdi = stackPtr s - 312 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have callMemory : MemoryWriteFrame t v
      #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨ScalarFrame.Work.region s 3680 32, by simp, ?_⟩
      have address : pushAddr t = stackPtr s - 320 := by
        rw [pushAddr, state.rsp, BitVec.sub_sub]
        rfl
      rw [address] at ha
      exact ScalarFrame.Work.contains pre.toCalleePre (offset := 320) (len := 8)
        (by decide) (by decide) ha
    · exact ha.elim
  have resultMemory : MemoryWriteFrame v u
      #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32] := by
    have h := result.stack_frame (savedBytes := 32) pre.stack sp destination
      (by decide) (by decide) (by decide) (by decide)
    intro a ha
    apply h a
    intro region member
    exact ha region (by simpa using Or.inr member)
  have memory := memoryWriteFrame_trans callMemory resultMemory
  have total := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre.toCalleePre memory)
  refine ⟨⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha ↦ result.allocated a (effect.agrees.grow a (state.allocated a ha)), total,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, result.rip.trans (callEffect_stack effect).1,
    by simpa only [destination] using affine⟩
  · change stackPtr u = stackPtr s - 312
    have rsp : stackPtr u = stackPtr v + 8 := result.rsp
    rw [rsp, (callEffect_stack effect).2, state.rsp]
  · intro slot member
    have bound : slot.2 ≤ 32 := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.Work.read pre.toCalleePre (by decide) memory bound (by omega)).trans
      (state.saved slot member)
  · have h := ScalarFrame.Work.read pre.toCalleePre (by decide) memory
      (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (result.calleeSaved .rbp (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans (state.registers .rbp (by simp)))
    · exact (result.calleeSaved .r13 (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 13) (by simp)).trans (state.registers .r13 (by simp)))
  · exact result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans state.mxcsr)
  · exact result.fp87.trans ((effect.agrees.fcw (by simp)).trans state.fp87)

end P256.Proofs.Sec1.Decode
