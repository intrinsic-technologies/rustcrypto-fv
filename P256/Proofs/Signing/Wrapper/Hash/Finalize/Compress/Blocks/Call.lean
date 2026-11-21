import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.Memory
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.FieldCall.Result
import P256.Proofs.Program.CalleeStack
import P256.Proofs.SHA256.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 800000 in
theorem call [Bindings] (last : Bool) {initial start s : RamState}
    {secret message chunk : ByteArray} {hash : Array UInt32}
    (pre : HashEntry initial start secret message) (state : HashAt initial start s hash)
    (rip : s.RIP = if last then 0x1029a4 else 0x1028f9)
    (output : s.regValue .rdi = frameBase initial + 128)
    (source : s.regValue .rsi = frameBase initial) (count : s.regValue .rdx = 1)
    (bytes : (MemoryRegion.mk (frameBase initial).toNat 64).HasBytes s.external chunk) :
    ∃ t, HashAt initial start t
      (SHA256.Reference.compress hash (Standards.NIST.SHA2.bytesToBits chunk)) ∧
      t.RIP = s.RIP + 5 ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.regValue r = s.regValue r) := by
  let pc : Nat := if last then 0x29a4 else 0x28f9
  let disp : BitVec 32 := if last then 0x12fe7 else 0x13092
  obtain ⟨u, _, frame, effect⟩ := state.toFrame.call_rel32 pre.context pc disp
    (by cases last <;> exact rip)
    (by cases last <;> decide) (by cases last <;> decide +kernel)
    (by cases last <;> exact inProgram_of_textOffset 0x15990 (by decide))
  have di : u.regValue .rdi = s.regValue .rdi :=
    effect.agrees.read (n := 64) (r := 7) (by simp)
  have destination : u.regValue .rdi = stackPtr initial - 392 := by
    rw [di, output]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have si : u.regValue .rsi = stackPtr initial - 520 := by
    have same : u.regValue .rsi = s.regValue .rsi :=
      effect.agrees.read (n := 64) (r := 6) (by simp)
    rw [same, source]
    rfl
  have copied {offset len : Nat} (bound : offset ≤ 520) (span : len ≤ offset + 8)
      {i : Nat} (hi : i < len) :=
    ScalarFrame.call_byte (frameOffset := 520) (by decide) state.rsp
      effect bound span hi
  let layout : StackCallLayout 5112 64 32 336 :=
    ⟨528,520,392,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have cp : SHA256.CompressionPre u (returnBoundary initial) hash chunk 1 := by
    refine ⟨CalleePre.of_stack_region (stack pre.context) (stack_avoids pre.context) (outside pre.context) layout frame.bindingsSupported frame.machine
      frame.directionFlag frame.loaded frame.allocated ?_ frame.rsp si destination ?_, ?_, ?_, ?_⟩
    · cases last <;> exact effect.rip
    · change InProgram (stackTop u)
      rw [(callEffect_stack effect).1]
      cases last
      · exact inProgram_of_textOffset 0x28fe (by decide)
      · exact inProgram_of_textOffset 0x29a9 (by decide)
    · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans count
    · change (MemoryRegion.mk (u.regValue .rsi).toNat 64).HasBytes u.external chunk
      rw [si]
      apply hasBytes_copy (a := stackPtr initial - 520) (b := stackPtr initial - 520) ?_
        (fun i hi => copied (offset := 520) (len := 64) (by decide) (by decide) hi)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using bytes
    · rw [destination]
      have hashAt : SHA256.HashStateAt s (stackPtr initial - 392) hash := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.hashWords
      exact hashAt.copy (fun i hi => copied (offset := 392) (len := 32) (by decide) (by decide) hi)
  obtain ⟨t, result⟩ := SHA256.compression_correct cp
  have finalFrame := frame.after_callee pre.context result.toCalleeResult destination
    (by decide) (by decide) (by decide) (by decide)
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
  have live : Live initial start t := ⟨finalFrame⟩
  refine ⟨t, ⟨live, ?_, (saved .r15 (by simp)).trans state.hashPointer⟩, ?_, saved⟩
  · have h := result.hashWords
    rw [di, output, SHA256.compressBlocks_single hash chunk bytes.1] at h
    exact h
  · have ret : (returnBoundary u).rip =
        Extracted.textAddress + BitVec.ofNat 64 pc + (5 : BitVec 64) :=
      (callEffect_stack effect).1
    rw [result.rip, ret, rip]
    cases last <;> rfl

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks
