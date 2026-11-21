import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.OuterBuffer.State

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

def appendComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 6, .reg 7, .reg 15, .flags,
    .mem (stackPtr s + 176) 32, .mem (stackPtr s + 239) 1, .rip]

structure Appended [Bindings] (initial s : RamState) (key input : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  outer : Sha256StateAt s (stackPtr initial - 152#64)
    (keyPad key 0x5c ++ P256.Spec.Operations.hash (keyPad key 0x36 ++ input))

theorem append_state [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Serialized initial s key input) (ready : ReadyToStep t)
    (agrees : AgreesExcept (appendComponents s) s t)
    (words : ∀ j < 4,
      memLoad t.external (stackPtr s + 176 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (stackPtr s + 8 + BitVec.ofNat 64 (8*j)) 64)
    (position : memLoad t.external (stackPtr s + 239) 8 = 32) :
    Appended initial t key input := by
  have frame := state.toFrameState.after_effect (stackPre pre) (by decide) ready agrees (by
    intro c hc a covered
    simp only [appendComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨workRegion initial 672, by simp,
      local_work_contains pre state.rsp (by decide) covered⟩) (by simp [appendComponents])
  have srcAddress : stackPtr s + 8 = stackPtr initial - 320#64 :=
    stack_address state.rsp (by decide : 8 ≤ 328)
  have dstAddress : stackPtr s + 176 = stackPtr initial - 152#64 :=
    stack_address state.rsp (by decide : 176 ≤ 328)
  have copied := Key.Output.bytes_of_words
    (ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (offset := 8) (len := 32) (by decide))
    (Program.readable_of_grow
      (ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (offset := 176) (len := 32) (by decide))
      agrees.grow) words
  have buffer := hasBytes_copy state.digest (by simpa only [srcAddress, dstAddress] using copied)
  have positionByte : t.external[stackPtr s + 239]? = some 32 := by
    have allocated := Program.readable_of_grow
      (ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (offset := 239) (len := 1) (by decide))
      agrees.grow
    change MemReadable t (stackPtr s + 239) 1 at allocated
    have bytes := Bytes.of_memLoad (n := 8) allocated.mem
    rw [position] at bytes
    have byte := bytes 0 (by decide)
    change t.external[stackPtr s + 239 + 0#64]? = some 32 at byte
    simpa only [BitVec.add_zero] using byte
  have stateOuter := state_append_digest state.outer (hash_size _) buffer ?_ ?_
  · exact ⟨frame,
      (agrees.read (n := 64) (r := 3) (by simp [appendComponents])).trans state.outputPointer,
      stateOuter⟩
  · rw [← dstAddress, BitVec.add_assoc]
    exact positionByte
  · intro i hi
    rw [← dstAddress]
    apply agrees.byte
    intro c hc covered
    simp only [appendComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    · obtain ⟨j, hj, eq⟩ := covered
      apply RangeApart.offsets (stackPtr s) (a := 176) (b := 240) (len := 32) (count := 40)
        (by decide) (by decide) (by decide) j hj i hi
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using eq.symm
    · obtain ⟨j, hj, eq⟩ := covered
      apply RangeApart.offsets (stackPtr s) (a := 239) (b := 240) (len := 1) (count := 40)
        (by decide) (by decide) (by decide) j hj i hi
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using eq.symm

end P256.Proofs.HMAC.Finalize.OuterBuffer
