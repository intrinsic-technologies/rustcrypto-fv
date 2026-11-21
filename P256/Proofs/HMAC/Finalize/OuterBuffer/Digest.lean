import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Digest.Frame
import P256.Proofs.HMAC.Finalize.Padding.Memory

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

structure Serialized [Bindings] (initial s : RamState) (key input : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  outer : Sha256StateAt s (stackPtr initial - 152#64) (keyPad key 0x5c)
  digest : (MemoryRegion.mk (stackPtr initial - 320#64).toNat 32).HasBytes s.external
    (P256.Spec.Operations.hash (keyPad key 0x36 ++ input))

theorem serialize [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HmacFinalizePre initial boundary key input)
    (state : Compressed initial s (keyPad key 0x36 ++ input))
    (outer : Sha256StateAt s (stackPtr initial - 152#64) (keyPad key 0x5c))
    (rip : s.RIP = paddingEnd false) :
    ∃ fuel t, Advances boundary fuel s t ∧ Serialized initial t key input ∧
      t.RIP = 0x101182 := by
  have dstAddress : stackPtr s + 8 = stackPtr initial - 320#64 :=
    stack_address state.rsp (by decide : 8 ≤ 328)
  have hp := Digest.pre pre.toHashCalleePre state.toFrameState rip
  obtain ⟨fuel, t, run, ready, _, effect⟩ :=
    Digest.run boundary pre.outerBoundary s (readyToStep state.machine state.bindingsSupported)
      (Digest.code state.loaded) hp
  have agrees := Digest.serializeEffect_agrees effect
  have memory : MemoryWriteFrame s t #v[scratchRegion initial] := by
    apply agrees.memoryWriteFrame
    intro c hc a covered
    simp only [Digest.components, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    change (Component.mem (stackPtr s + 8) 32).Covers a at covered
    rw [dstAddress] at covered
    exact ⟨_, by simp,
      Padding.scratch_contains pre.toHashCalleePre (by decide) (by decide) covered⟩
  have address : stackPtr s + 136 = stackPtr initial - 192#64 :=
    stack_address state.rsp (by decide : 136 ≤ 328)
  have digest := Digest.output hp (address.symm ▸ state.hash) effect
  rw [serializeHash_inner_tail key input pre.inputSize,
    dstAddress] at digest
  refine ⟨fuel, t, run, ⟨Digest.frame pre.toHashCalleePre state.toFrameState ready effect,
    ?_, outer_state_of_scratch_frame pre.toHashCalleePre outer memory, digest⟩, effect.rip⟩
  exact (agrees.read (n := 64) (r := 3) (by simp [Digest.components])).trans state.outputPointer

end P256.Proofs.HMAC.Finalize.OuterBuffer
