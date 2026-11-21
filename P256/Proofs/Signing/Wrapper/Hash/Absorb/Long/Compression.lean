import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Prepared
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Input
import P256.Proofs.SHA256.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Compressed [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Frame initial start t where
  rip : t.RIP = 0x102830
  source : t.regValue .r15 = start.regValue .rsi + BitVec.ofNat 64 (64 * (message.size / 64))
  length : t.regValue .r12 = BitVec.ofNat 64 (message.size % 64)
  hash : SHA256.HashStateAt t (frameBase initial + 240)
    (SHA256.compressBlocks SHA256.initialHash message)
  count : loadBytes t.external (frameBase initial + 272) 8 =
    .ok (BitVec.ofNat 64 (message.size / 64))

theorem compress [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Prepared initial start s message) :
    ∃ t, Compressed initial start t message := by
  obtain ⟨call, _, frame, effect⟩ := state.toFrame.call_rel32 pre.context
    0x282b 0x13160 state.rip (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x15990 (by decide))
  have source : call.regValue .rsi = memLoad initial.external (initial.regValue .rdi + 8) 64 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans (state.inputPointer.trans pre.pointer)
  have di : call.regValue .rdi = s.regValue .rdi :=
    effect.agrees.read (n := 64) (r := 7) (by simp)
  have destination : call.regValue .rdi = stackPtr initial - 280 := by
    rw [di, state.outputPointer]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have copied {offset len : Nat} (bound : offset ≤ 520) (span : len ≤ offset + 8)
      {i : Nat} (hi : i < len) :=
    ScalarFrame.call_byte (frameOffset := 520) (by decide) state.rsp
      effect bound span hi
  have ⟨inputBounded, inputApart, inputBytes⟩ := message_slice pre frame
    (offset := 0) (count := 64 * (message.size / 64)) (by omega)
  simp only [BitVec.add_zero, Nat.zero_add] at inputBounded inputApart inputBytes
  have cp : SHA256.CompressionPre call (returnBoundary initial) SHA256.initialHash
      (SHA256.fullBlocks message) (message.size / 64) := by
    refine ⟨CalleePre.of_disjoint_input_and_stack
      ⟨528,280,by decide,by decide,by decide,by decide⟩ (stack pre.context)
      (stack_avoids pre.context) frame.bindingsSupported frame.machine frame.directionFlag frame.loaded
      effect.rip frame.rsp ?_ ?_ ?_ destination frame.allocated (outside pre.context) ?_, ?_, ?_, ?_⟩
    · simpa only [registerRegion, source] using inputBounded
    · simpa only [registerRegion, source] using hasBytes_allocated inputBytes
    · simpa only [registerRegion, source] using inputApart
    · change InProgram (stackTop call)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0x2830 (by decide)
    · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.countRegister
    · simpa only [registerRegion, source, SHA256.fullBlocks] using inputBytes
    · rw [destination]
      have hash : SHA256.HashStateAt s (stackPtr initial - 280) SHA256.initialHash := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.hash
      exact hash.copy (fun i hi => copied (offset := 280) (len := 32) (by decide) (by decide) hi)
  obtain ⟨t, result⟩ := SHA256.compression_correct cp
  have finalFrame := frame.after_callee pre.context result.toCalleeResult destination
    (by decide) (by decide) (by decide) (by decide)
  have kept {offset len : Nat} (bound : offset ≤ 520) (span : len ≤ offset + 8)
      (apart : offset + 32 ≤ 280 ∨ 280 + len ≤ offset) {i : Nat} (hi : i < len) :
      t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
    (result.toCalleeResult.stack_byte (stack pre.context) frame.rsp destination
      (by decide) (by decide) bound span apart hi).trans (copied bound span hi)
  have saved (r : Syntax.Reg) (member : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = s.regValue r := by
    apply (result.calleeSaved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  refine ⟨t, finalFrame, result.rip.trans (callEffect_stack effect).1,
    (saved .r15 (by simp)).trans state.source,
    (saved .r12 (by simp)).trans state.length, ?_, ?_⟩
  · have h := result.hashWords
    rw [di, state.outputPointer,
      SHA256.compressBlocks_fullBlocks] at h
    exact h
  · apply loadBytes_ok_copy _ state.count
    intro i hi
    have h := kept (offset := 248) (len := 8) (by decide) (by decide) (by decide) hi
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using h

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long
