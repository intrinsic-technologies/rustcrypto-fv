import P256.Proofs.Verifying.Message.Convert.Head
import P256.Proofs.Verifying.Message.Convert.Pre
import P256.Proofs.Verifying.Message.Convert.Write
import P256.Proofs.Verifying.Message.Convert.CopyY
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure YCopied [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (y : Nat) : Prop extends Context initial s boundary message where
  rip : s.RIP = 0x10d988
  source : s.regValue .rdx = initial.regValue .rsi
  yPointer : s.regValue .rbx = frameBase initial + 32
  y : MontgomeryAt s (frameBase initial + 32) y

theorem copy_y_output {s t : RamState} {value : Nat}
    (result : (Copy32.effect 0x10d988 CopyY.source CopyY.destination s).Holds s t)
    (input : MontgomeryAt s (CopyY.source s) value)
    (allocated : MemReadable t (CopyY.destination s) 32) :
    MontgomeryAt t (CopyY.destination s) value := by
  apply montgomeryAt_of_memLoad_limbs input.1 allocated.mem
  intro j hj
  apply Eq.trans _ (input.memLoad_limb j hj)
  have values := result.writes
  simp only [Copy32.effect, Write.AllHold, Operand.read] at values
  obtain ⟨_, _, h0, h8, h16, h24⟩ := values
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h8
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h16
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h24

theorem copy_y [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y r scalarS : Nat} (pre : Pre initial boundary message)
    (input : InputAt initial (.affine x y) r scalarS)
    (state : Head initial s boundary message) : ∃ t, YCopied initial t boundary message y := by
  have hp := key_copy_pre pre state.toFrameState (offset := 32) (sourceOffset := 32)
    (by decide) (by decide) state.rip (show CopyY.destination s = stackPtr s + BitVec.ofNat 64 32 from rfl)
    (show CopyY.source s = initial.regValue .rsi + BitVec.ofNat 64 32 by
      change s.regValue .rdx + 32 = _
      rw [state.source]
      rfl)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := CopyY.copy boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd964 CopyY.bytes
      (by decide) (by decide +kernel)) hp
  have agrees := Copy32.frame effect
  have context := state.toContext.after_write pre run ready agrees
    (offset := 32) (len := 32) (by decide) (by decide)
    (by
      intro c hc a ha
      simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals first | exact ha.elim | exact ha)
    (by simp [Copy32.components]) (by simp [Copy32.components])
    (by simp [Copy32.components]) (by simp [Copy32.components])
  have readable : MemReadable t (CopyY.destination s) 32 :=
    readable_of_grow
      (stack_readable (frameOffset := 1176) pre.toCalleePre state.toFrameState (by decide) (by decide))
      agrees.grow
  have key := (input_preserved pre input state.stackFrame).1
  have payload : MontgomeryAt s (CopyY.source s) y := by
    change MontgomeryAt s (s.regValue .rdx + 32) y
    rw [state.source]
    exact key.2.1
  have value := copy_y_output effect payload readable
  have stack : stackPtr s = frameBase initial := state.rsp
  refine ⟨t, context, effect.rip, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 2) (by simp [Copy32.components])).trans state.source
  · exact (agrees.read (n := 64) (r := 3) (by simp [Copy32.components])).trans state.yPointer
  · change MontgomeryAt t (stackPtr s + 32) y at value
    rwa [stack] at value

end P256.Proofs.Verifying.Message.Convert
