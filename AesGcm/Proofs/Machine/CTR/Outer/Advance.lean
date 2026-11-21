import AesGcm.Proofs.Machine.CTR.Outer.BatchBytes
import AesGcm.Proofs.Machine.CTR.Outer.Frame

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open Standards.NIST.GCM AesGcm.Spec.GCM

theorem OuterInvariant.advance_batch
    {u : Bool} {code : CodeMap} {fr : Activation} {key : Vector UInt8 (AES16.variant u).keyBytes}
    {input : ByteArray} {batches c blockCount : Nat} {schedule counter source destination : BitVec 64}
    {loc next : LIR.lifted.Location}
    (h : OuterInvariant u code fr key input batches c schedule counter source destination loc)
    (hsize : input.size = 16 * blockCount) (hbatches : batches = blockCount / 4)
    (label : next.label = (if c + 1 < batches then
      (if u then .l108e98 else .l107a08) else (if u then .l109509 else .l10805f)))
    (typed : GPRsTyped next.arguments)
    (writes : RamWriteFrame loc.store next.store
      (batchWriteRegions (outerStackPointer fr u) counter destination c))
    (dst : next.arguments[2]'(by change 2 < 53; decide) = ⟨64, destination⟩)
    (rsp : next.arguments[4]'(by change 4 < 53; decide) = ⟨64, outerStackPointer fr u⟩)
    (ctr : next.arguments[9]'(by change 9 < 53; decide) = ⟨64, counter⟩)
    (regs : ∀ r : Fin Reg.count, r.val ∈ [22, 39, 50, 51] → next.arguments[r] = loc.arguments[r])
    (count : memLoad next.store (outerStackPointer fr u + 224) 64 = BitVec.ofNat 64 (c+1))
    (value : memLoad next.store (counter + 16) 32 = memLoad loc.store (counter + 16) 32 + 4)
    (chunk : let output := byteArrayOfBits (GCTR (forwardCipher (AES16.variant u) key)
      (bitsOfBytes (initialCounterBlock fr.original counter)) (bitsOfByteArray input))
      (span (destination + BitVec.ofNat 64 (64 * c)) 64).HasBytes next.store
        (output.extract (64 * c) (64 * (c + 1)))) :
    (c + 1 < batches ∧ OuterInvariant u code fr key input batches (c+1) schedule counter source destination next) ∨
    (c + 1 = batches ∧ OuterExit u code fr key input blockCount schedule counter source destination next) := by
  let sp := outerStackPointer fr u
  have bound := h.count_lt
  have either : next.label = (if u then .l108e98 else .l107a08) ∨
      next.label = (if u then .l109509 else .l10805f) := by split at label <;> simp [label]
  obtain ⟨frame, outer, sched, dstSlot⟩ := h.batch_frame hsize hbatches either writes dst rsp ctr regs
  have wide : RamWriteFrame loc.store next.store
      [fr.region, span (counter + 16) 4, span (destination + BitVec.ofNat 64 (64 * c)) 64] := by
    apply (RamWriteFrame.refl _ _).trans writes
    obtain ⟨low, high, top, _⟩ := h.batch_stack_bounds
    change fr.low.toNat + 296 ≤ sp.toNat at low
    change sp.toNat + 1800 ≤ fr.rsp.toNat at high
    have sub : (sp - 296).toNat = sp.toNat - 296 := BitVec.toNat_sub_of_le (by exact (show 296 ≤ sp.toNat by omega))
    have add (k : Nat) (hk : k ≤ 320) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    intro r hr
    change r ∈ [span (sp - 296) 512, span (sp + 224) 8, span (sp + 256) 64,
      span (counter + 16) 4, span (destination + BitVec.ofNat 64 (64 * c)) 64] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [Activation.region, span] <;> omega
    · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [Activation.region, span] <;> rw [show (sp + 224).toNat = sp.toNat + 224 from add 224 (by decide)] <;> omega
    · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [Activation.region, span] <;> rw [show (sp + 256).toNat = sp.toNat + 256 from add 256 (by decide)] <;> omega
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨suffix, prefixBytes, written⟩ := h.batch_bytes (by omega) wide chunk
  have state : OuterState u code fr key input blockCount schedule counter source destination next :=
    ⟨frame, outer, written, typed, sched, h.schedule_read.of_frame writes⟩
  have counterNext : memLoad next.store (counter + 16) 32 =
      memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 (4 * (c+1)) := by
    rw [value, h.counter_value, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  by_cases cont : c + 1 < batches
  · simp only [cont, ↓reduceIte] at label
    rw [show blockCount = input.size / 16 by omega] at state
    exact Or.inl ⟨cont, state, label, cont, dstSlot, count, counterNext, suffix, prefixBytes⟩
  · simp only [cont, ↓reduceIte] at label
    have done : c+1 = batches := by omega
    have pos : 64 * (c+1) = input.size - input.size % 64 := by omega
    rw [pos] at suffix prefixBytes
    rw [show input.size - (input.size - input.size % 64) = input.size % 64 by omega] at suffix
    rw [done, hbatches] at counterNext
    exact Or.inr ⟨done, state, label, counterNext, suffix, prefixBytes⟩

end AesGcm.Proofs.Machine.CTR
