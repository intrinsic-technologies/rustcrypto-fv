import Hkdf.Proofs.NewExpand.Expand.Positive.Copy
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Footprint
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StartInfo

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

private theorem finishDigest [Bindings] {entry s u t : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (head : LoopState entry s boundary key info length n) (more : 32*n < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry u boundary length)
    (result : Finalize.Result entry u t boundary length key
      ((blocks .sha256 key info n).2 ++ info ++ ⟨#[UInt8.ofNat (n+1)]⟩))
    (slots : ∀ i ∈ ([232,240,248,416,424,440] : List (BitVec 64)), slot u i = slot s i)
    (copy : u.regValue .r12 = 0x10dd60) (counter : slot u 256 = BitVec.ofNat 64 n)
    (remaining : slot u 8 = BitVec.ofNat 64 (length - 32*(n+1)))
    (dest : slot u 432 = entry.regValue .rcx + BitVec.ofNat 64 (32*n))
    (size : slot u 264 = BitVec.ofNat 64 (min (length - 32*n) 32))
    (frame : MemoryWriteFrame s u #v[Stack.region entry 2264]) :
    ∃ final, LoopState entry final boundary key info length (n+1) := by
  have bounds := Info.workBounds pre.call.stack saved
  have stackFrame := stackFrameOfLocal pre.call.stack saved result.frameLocal (by
    intro region member
    simp only [Finalize.writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> dsimp <;> omega)
  apply copyAndFinishRound pre head result.toSavedFrame result.rip more bound
  · intro i member
    apply Eq.trans _ (slots i member)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact result.slot_eq pre.call.stack saved.sp _ (by decide) (by decide) (by decide)
  · exact result.r12Reg.trans copy
  · rw [result.counter, counter, BitVec.ofNat_add]
    rfl
  · exact (result.slot_eq pre.call.stack saved.sp 8 (by decide) (by decide) (by decide)).trans remaining
  · rw [result.nextPtr, dest, size, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  · exact result.r14Reg.trans dest
  · exact result.r13Reg
  · exact result.chunk.trans size
  · rw [blocks_succ]
    exact result.digest
  · exact head.outputOfStack pre more bound (memoryWriteFrame_trans frame stackFrame)

variable [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
  {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}

theorem iterate (pre : ExpandPre entry boundary key info ptr length)
    (state : LoopState entry s boundary key info length n)
    (more : 32 * n < length) (bound : length ≤ 8160) :
    ∃ t, LoopState entry t boundary key info length (n + 1) := by
  obtain ⟨a, savedA, pcA, hmacA, copyA, destA, remainingA, sizeA, slotsA, frameA⟩ :=
    startInfo pre state more bound
  have small : (blocks .sha256 key info n).2.size < 64 := by
    cases n with
    | zero => exact (by decide : 0 < 64)
    | succ n => rw [blocks_sha256_previous_size key info (Nat.zero_lt_succ _)]; decide
  obtain ⟨_, b, _, savedB, pcB, hmacB, copyB, destB, writesB⟩ :=
    Info.absorb pre (by omega) bound savedA pcA
      ((slotsA 248 (by decide)).trans state.count)
      ((slotsA 232 (by decide)).trans state.descriptors)
      ((slotsA 440 (by decide)).trans state.tableEnd) copyA hmacA small
  obtain ⟨frameB, slotsB⟩ := infoFrame pre.call.stack savedA savedB writesB
  have countB := (slotsB 256 (by decide)).trans ((slotsA 256 (by decide)).trans state.counter)
  have chunkB := (slotsB 264 (by decide)).trans sizeA
  have remB := (slotsB 8 (by decide)).trans remainingA
  have hmacB' : HmacAt b (Counter.base entry + 272) key ((blocks .sha256 key info n).2 ++ info) := by
    rwa [← (show stackPtr b = Counter.base entry from savedB.sp)]
  obtain ⟨c, cs⟩ := Counter.append pre (by omega) bound savedB pcB countB (by omega)
    (copyB.trans copyA) hmacB'
  obtain ⟨frameC, slotsC⟩ := counterFrame pre.call.stack savedB cs.toSavedFrame cs.frameLocal
  have hmacC := cs.hmac
  rw [← (show stackPtr c = Counter.base entry from cs.sp)] at hmacC
  obtain ⟨t, post⟩ := Finalize.run pre cs.toSavedFrame (by omega) bound cs.pc hmacC
  apply finishDigest pre state more bound cs.toSavedFrame post
  · intro i member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (slotsC _ (by decide)).trans ((slotsB _ (by decide)).trans (slotsA _ (by decide)))
  · exact cs.memcpy
  · exact (slotsC 256 (by decide)).trans countB
  · change slot b 8 = BitVec.ofNat 64 (length - 32*n) at remB
    change slot b 264 = BitVec.ofNat 64 (min (length - 32*n) 32) at chunkB
    rw [cs.remaining, remB, chunkB, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 1
    omega
  · exact (slotsC 432 (by decide)).trans (destB.trans destA)
  · exact (slotsC 264 (by decide)).trans chunkB
  · exact memoryWriteFrame_trans frameA (memoryWriteFrame_trans frameB frameC)

end Hkdf.Proofs.NewExpand.Expand
