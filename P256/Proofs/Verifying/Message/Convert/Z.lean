import P256.Proofs.Verifying.Message.Convert.X
import P256.Proofs.Verifying.Message.Convert.OnePayload

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Coordinates [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (x y : Nat) : Prop extends Context initial s boundary message where
  rip : s.RIP = 0x10d9df
  source : s.regValue .rdx = initial.regValue .rsi
  yPointer : s.regValue .rbx = frameBase initial + 32
  zPointer : s.regValue .r14 = frameBase initial + 64
  x : MontgomeryAt s (frameBase initial + 0) x
  y : MontgomeryAt s (frameBase initial + 32) y
  z : MontgomeryAt s (frameBase initial + 64) 1

theorem copy_z [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} (pre : Pre initial boundary message)
    (state : XYCopied initial s boundary message x y) :
    ∃ t, Coordinates initial t boundary message x y := by
  have hp := one_copy_pre pre state.toFrameState (offset := 64) (by decide) state.rip
    (show One.destination s = stackPtr s + BitVec.ofNat 64 64 from rfl)
    (show One.source s = 0x202580 from rfl)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := One.copy boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xd9aa One.bytes
      (by decide) (by decide +kernel)) hp
  have agrees := One.frame effect
  have covers : ∀ c ∈ One.components (One.destination s), ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 64) 32).Covers a := by
    intro c hc a ha
    simp only [One.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals first | exact ha.elim | exact ha
  have context := state.toContext.after_write pre run ready agrees
    (offset := 64) (len := 32) (by decide) (by decide) covers
    (by simp [One.components]) (by simp [One.components])
    (by simp [One.components]) (by simp [One.components])
  have readable : MemReadable t (One.destination s) 32 :=
    readable_of_grow
      (stack_readable (frameOffset := 1176) pre.toCalleePre state.toFrameState (by decide) (by decide))
      agrees.grow
  have value := One.output effect (Ecdh.Initial.Prefix.one_at state.loaded) readable
  have stack : stackPtr s = frameBase initial := state.rsp
  refine ⟨t, context, effect.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 2) (by simp [One.components])).trans state.source
  · exact (agrees.read (n := 64) (r := 3) (by simp [One.components])).trans state.yPointer
  · have value : t.regValue .r14 = stackPtr s + 64 := effect.writes.1
    rw [value, stack]
  · exact state.x.of_bytes_eq (preserved_bytes pre state.toFrameState agrees
      (offset := 64) (len := 32) (readOffset := 0) (readLen := 32)
      (by decide) (by decide) (by decide) covers)
  · exact state.y.of_bytes_eq (preserved_bytes pre state.toFrameState agrees
      (offset := 64) (len := 32) (readOffset := 32) (readLen := 32)
      (by decide) (by decide) (by decide) covers)
  · change MontgomeryAt t (stackPtr s + 64) 1 at value
    rwa [stack] at value

end P256.Proofs.Verifying.Message.Convert
