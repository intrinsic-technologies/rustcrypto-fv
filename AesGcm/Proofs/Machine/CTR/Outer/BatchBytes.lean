import AesGcm.Proofs.Machine.CTR.Outer.Invariant
import AesGcm.Proofs.Machine.Runtime.MemorySlices

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open Standards.NIST.GCM AesGcm.Spec.GCM

theorem OuterInvariant.batch_bytes
    {u : Bool} {code : CodeMap} {fr : Activation}
    {key : Vector UInt8 (AES16.variant u).keyBytes} {input : ByteArray}
    {batches c : Nat} {schedule counter source destination : BitVec 64}
    {loc : LIR.lifted.Location} {after : Ram}
    (inv : OuterInvariant u code fr key input batches c schedule counter source destination loc)
    (bound : 64 * (c + 1) ≤ input.size)
    (frame : RamWriteFrame loc.store after
      [fr.region, span (counter + 16) 4, span (destination + BitVec.ofNat 64 (64 * c)) 64])
    (chunk : let output := byteArrayOfBits (GCTR (forwardCipher (AES16.variant u) key)
      (bitsOfBytes (initialCounterBlock fr.original counter)) (bitsOfByteArray input))
     (span (destination + BitVec.ofNat 64 (64 * c)) 64).HasBytes after
       (output.extract (64 * c) (64 * (c + 1)))) :
    let output := byteArrayOfBits (GCTR (forwardCipher (AES16.variant u) key)
      (bitsOfBytes (initialCounterBlock fr.original counter)) (bitsOfByteArray input))
    (span (source + BitVec.ofNat 64 (64 * (c + 1))) (input.size - 64 * (c + 1))).HasBytes
      after (input.extract (64 * (c + 1)) input.size) ∧
    (span destination (64 * (c + 1))).HasBytes after (output.extract 0 (64 * (c + 1))) ∧
    RamWriteFrame fr.original after [fr.region, span (counter + 16) 4, span destination input.size] := by
  let pos := 64 * c
  let limit := 64 * (c + 1)
  let schedSize := 16 * ((AES16.variant u).Nr + 1)
  let output := byteArrayOfBits (GCTR (forwardCipher (AES16.variant u) key)
    (bitsOfBytes (initialCounterBlock fr.original counter)) (bitsOfByteArray input))
  have outSize : output.size = input.size := byteArrayOfBits_size _
  have sourceLow := inv.toOuterState.source_read.low
  have destLow := inv.toOuterState.destination_write.readable.low
  have counterLow := inv.toOuterState.counter_write.readable.low
  have pos_limit : pos + 64 = limit := by dsimp only [pos, limit]; omega
  have fit : limit ≤ input.size := bound
  have ptr {base : BitVec 64} {off : Nat} (h : base.toNat + off < 2^64) :
      (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt h]
  have srcPos := ptr (base := source) (off := pos) (by omega)
  have srcLimit := ptr (base := source) (off := limit) (by omega)
  have dstPos := ptr (base := destination) (off := pos) (by omega)
  have ctrOff : (counter + 16).toNat = counter.toNat + 16 := by bv_omega
  have stackSep : ∀ r ∈ [span fr.rdi 8, span fr.rsi 32, span schedule schedSize,
      span counter 20, span source input.size, span destination input.size],
      (callStack fr).Disjoint r :=
    atomsAll_mem (atom := .fact _) inv.outer (by simp [outerAtoms, schedSize])
  have ctrSep : ∀ r ∈ [span fr.rdi 8, span fr.rsi 32, span schedule schedSize,
      span source input.size, span destination input.size], (span counter 20).Disjoint r :=
    atomsAll_mem (atom := .fact _) inv.outer (by simp [outerAtoms, schedSize])
  have buffers : source = destination ∨
      (span source input.size).Disjoint (span destination input.size) :=
    atomsAll_mem (atom := .fact _) inv.outer (by simp [outerAtoms])
  let batch := span (destination + BitVec.ofNat 64 pos) 64
  have batchIn {a : Nat} (h : batch.Contains a) : (span destination input.size).Contains a := by
    change (destination + BitVec.ofNat 64 pos).toNat ≤ a ∧ a < (destination + BitVec.ofNat 64 pos).toNat + 64 at h
    change destination.toNat ≤ a ∧ a < destination.toNat + input.size
    omega
  have outsidePart {base : BitVec 64} {size : Nat} {part : MemoryRegion}
      (hs : (callStack fr).Disjoint (span base size)) (hc : (span counter 20).Disjoint (span base size))
      (sub : ∀ a, part.Contains a → (span base size).Contains a) (hd : part.Disjoint batch) :
      ∀ r ∈ [fr.region, span (counter + 16) 4, batch], part.Disjoint r := by
    intro r hr a ha hb
    rcases List.mem_cons.mp hr with rfl | hr
    · exact span_disjoint_activationRegion hs a (sub a ha) hb
    rcases List.mem_cons.mp hr with rfl | hr
    · apply hc a _ (sub a ha)
      change (counter + 16).toNat ≤ a ∧ a < (counter + 16).toNat + 4 at hb
      change counter.toNat ≤ a ∧ a < counter.toNat + 20
      omega
    · exact hd a ha (List.mem_singleton.mp hr ▸ hb)
  let unread := span (source + BitVec.ofNat 64 limit) (input.size - limit)
  have unreadIn (a : Nat) (h : unread.Contains a) : (span source input.size).Contains a := by
    change (source + BitVec.ofNat 64 limit).toNat ≤ a ∧ a < (source + BitVec.ofNat 64 limit).toNat + (input.size - limit) at h
    change source.toNat ≤ a ∧ a < source.toNat + input.size
    omega
  have unreadApart : unread.Disjoint batch := by
    intro a hu hb
    rcases buffers with he | hd
    · change (source + BitVec.ofNat 64 limit).toNat ≤ a ∧ _ at hu
      change _ ∧ a < (destination + BitVec.ofNat 64 pos).toNat + 64 at hb
      rw [srcLimit, he] at hu
      omega
    · exact hd a (unreadIn a hu) (batchIn hb)
  have suffixSize : (input.extract pos input.size).size = input.size - pos := by simp
  have suffix := inv.source_bytes
  change (span (source + BitVec.ofNat 64 pos) (input.size - pos)).HasBytes _ _ at suffix
  rw [← suffixSize] at suffix
  have tail := hasBytes_extract suffix 64 (input.size - pos) (by omega)
    (by rw [suffixSize]; omega) (by omega)
  have tailEq : source + BitVec.ofNat 64 pos + 64 = source + BitVec.ofNat 64 limit := by
    rw [← pos_limit, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  change (span (source + BitVec.ofNat 64 pos + 64) ((input.size - pos) - 64)).HasBytes _
    ((input.extract pos input.size).extract 64 (input.size - pos)) at tail
  rw [tailEq, ByteArray.extract_extract, pos_limit, Nat.add_sub_of_le (by omega),
    Nat.min_self, show input.size - pos - 64 = input.size - limit by omega] at tail
  have headSize : (output.extract 0 pos).size = pos := by
    simp only [ByteArray.size_extract, Nat.sub_zero, outSize, Nat.min_eq_left (show pos ≤ input.size by omega)]
  have chunkSize : (output.extract pos limit).size = 64 := by
    simp only [ByteArray.size_extract, outSize, Nat.min_eq_left fit]
    omega
  have prevBytes := inv.prefix_bytes
  change (span destination pos).HasBytes _ (output.extract 0 pos) at prevBytes
  have prefAfter := hasBytes_of_frame frame prevBytes (by change destination.toNat + pos ≤ 2^64; omega)
    (outsidePart (base := destination) (size := input.size) (stackSep _ (by simp)) (ctrSep _ (by simp))
      (fun a ha => by
        change destination.toNat ≤ a ∧ a < destination.toNat + pos at ha
        change destination.toNat ≤ a ∧ a < destination.toNat + input.size
        omega)
      (fun a ha hb => by
        change _ ∧ a < destination.toNat + pos at ha
        change (destination + BitVec.ofNat 64 pos).toNat ≤ a ∧ _ at hb
        omega))
  refine ⟨hasBytes_of_frame frame tail (by change (source + BitVec.ofNat 64 limit).toNat + (input.size - limit) ≤ 2^64; omega)
    (outsidePart (stackSep _ (by simp)) (ctrSep _ (by simp)) unreadIn unreadApart), ?_, ?_⟩
  · have combined := hasBytes_append (by simpa only [headSize] using prefAfter)
      (by simpa only [headSize, chunkSize] using chunk)
      (by rw [headSize]; omega) (front := output.extract 0 pos) (tail := output.extract pos limit)
    simpa only [headSize, chunkSize, pos_limit, ByteArray.extract_append_extract,
      Nat.zero_min, Nat.max_eq_right (show pos ≤ limit by omega)] using combined
  · apply inv.written.trans frame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · rcases List.mem_singleton.mp hr with rfl
      refine ⟨span destination input.size, by simp, ?_, ?_⟩
      · change destination.toNat ≤ (destination + BitVec.ofNat 64 pos).toNat; omega
      · change (destination + BitVec.ofNat 64 pos).toNat + 64 ≤ destination.toNat + input.size; omega

end AesGcm.Proofs.Machine.CTR
