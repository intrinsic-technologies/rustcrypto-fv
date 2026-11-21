import P256.Proofs.Verifying.Message.Convert.Y
import P256.Proofs.Verifying.Message.Convert.CopyXPayload
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure XYCopied [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (x y : Nat) : Prop extends Context initial s boundary message where
  rip : s.RIP = 0x10d9aa
  source : s.regValue .rdx = initial.regValue .rsi
  yPointer : s.regValue .rbx = frameBase initial + 32
  x : MontgomeryAt s (frameBase initial + 0) x
  y : MontgomeryAt s (frameBase initial + 32) y

theorem copy_x [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y r scalarS : Nat} (pre : Pre initial boundary message)
    (input : InputAt initial (.affine x y) r scalarS)
    (state : YCopied initial s boundary message y) : ∃ t, XYCopied initial t boundary message x y := by
  have hp := key_copy_pre pre state.toFrameState (offset := 0) (sourceOffset := 0)
    (by decide) (by decide) state.rip (show CopyX.destination s = stackPtr s + BitVec.ofNat 64 0 from rfl)
    (show CopyX.source s = initial.regValue .rsi + BitVec.ofNat 64 0 by
      change s.regValue .rdx = _
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using state.source)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := CopyX.copy boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd988 CopyX.bytes
      (by decide) (by decide +kernel)) hp
  have agrees := CopyX.frame effect
  have covers : ∀ c ∈ CopyX.components (CopyX.destination s), ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 0) 32).Covers a := by
    intro c hc a ha
    simp only [CopyX.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals first | exact ha.elim | exact ha
  have context := state.toContext.after_write pre run ready agrees
    (offset := 0) (len := 32) (by decide) (by decide) covers
    (by simp [CopyX.components]) (by simp [CopyX.components])
    (by simp [CopyX.components]) (by simp [CopyX.components])
  have readable : MemReadable t (CopyX.destination s) 32 :=
    readable_of_grow
      (stack_readable (frameOffset := 1176) pre.toCalleePre state.toFrameState (by decide) (by decide))
      agrees.grow
  have key := (input_preserved pre input state.stackFrame).1
  have payload : MontgomeryAt s (CopyX.source s) x := by
    change MontgomeryAt s (s.regValue .rdx) x
    rw [state.source]
    exact key.1
  have value := CopyX.output effect payload readable
  have stack : stackPtr s = frameBase initial := state.rsp
  refine ⟨t, context, effect.rip, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 2) (by simp [CopyX.components])).trans state.source
  · exact (agrees.read (n := 64) (r := 3) (by simp [CopyX.components])).trans state.yPointer
  · change MontgomeryAt t (stackPtr s + 0) x at value
    rwa [stack] at value
  · exact state.y.of_bytes_eq (preserved_bytes pre state.toFrameState agrees
      (offset := 0) (len := 32) (readOffset := 32) (readLen := 32)
      (by decide) (by decide) (by decide) covers)

end P256.Proofs.Verifying.Message.Convert
