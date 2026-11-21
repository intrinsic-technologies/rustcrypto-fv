import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Call
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Selection
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem core_inputs_of_validCall {initial : RamState} {key : Vector UInt8 16}
    {nonce : Vector UInt8 12} {aad bytes : ByteArray} {capacity : Nat} {ret cap : BitVec 64} {mem : Ram}
    (hc : ValidCall initial key nonce aad bytes capacity)
    (hf : RamWriteFrame initial.external mem [(entryActivation initial ret).region])
    (hcap : cap = memLoad initial.external ((entryActivation initial ret).rsp + 8) 64) :
    let fr := entryActivation initial ret
    let p := selectedPointer fr.r9 cap fr.r8
    cap.toNat = capacity ∧ (selectedLength fr.r9 cap).toNat = bytes.size ∧
    (p = fr.r8 ∨ bytes.size = 0) ∧ fr.rcx.toNat = aad.size ∧
    Readable mem fr.rsi 12 ∧ (span fr.rsi 12).HasBytes mem ⟨nonce.toArray⟩ ∧
    Readable mem fr.rdx aad.size ∧ (span fr.rdx aad.size).HasBytes mem aad ∧
    Readable mem p bytes.size ∧ (span p bytes.size).HasBytes mem bytes ∧
    (0 < bytes.size → Writable Extracted.programImage mem p bytes.size) ∧
    (∀ r ∈ [span fr.rsi 12, span fr.rdx aad.size, span p bytes.size], (callStack fr).Disjoint r) ∧
    (∀ r ∈ [span fr.rsi 12, span fr.rdx aad.size], (span p bytes.size).Disjoint r) ∧
    (∀ s ∈ ([0x201208,0x201210,0x201228,0x201230] : List (BitVec 64)),
      (span p bytes.size).Disjoint (span s 8)) := by
  let fr := entryActivation initial ret
  let buffer := span fr.r8 capacity
  have hbuffer : ValidOutput buffer initial.external :=
    hc.elim (fun h => h.outputInMemory.1) (fun h => h.2.outputInMemory)
  have hsep : MemorySeparation initial
      [keyRegion initial 16, span fr.rsi 12, span fr.rdx aad.size] [buffer]
      aes128gcmEncryptInPlace.minStackBytes 16 :=
    hc.elim (fun h => h.separation) (fun h => h.2.separation)
  have hnonce : ValidInput (span fr.rsi 12) initial.external ⟨nonce.toArray⟩ :=
    hc.elim (fun h => h.nonceInMemory) (fun h => h.2.nonceInMemory)
  have haad : ValidInput (span fr.rdx aad.size) initial.external aad :=
    hc.elim (fun h => h.associatedDataInMemory) (fun h => h.2.associatedDataInMemory)
  have hrcx : fr.rcx.toNat = aad.size := hc.elim
    (fun h => h.associatedDataLengthArgumentMatchesData)
    (fun h => h.2.associatedDataLengthArgumentMatchesData)
  have harg : ValidStackArgument initial capacity :=
    hc.elim (fun h => h.capacityArgumentOnStack) (fun h => h.2.capacityArgumentOnStack)
  have hload := memLoad_of_word64At harg.2
  change memLoad initial.external (BitVec.ofNat 64 (fr.rsp.toNat + 8)) 64 = _ at hload
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hload
  have hcapEq : cap = BitVec.ofNat 64 capacity := hcap.trans hload
  have hcapNat : cap.toNat = capacity := by
    have hb : fr.r8.toNat + capacity < 2 ^ 32 := hbuffer.2.1
    rw [hcapEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have stackEq : callStack fr = Stack.region initial aes128gcmEncryptInPlace.minStackBytes 8 := by
    simp only [callStack, Stack.region, fr, entryActivation, Activation.ofEntry_low_toNat]
    rfl
  have stackWithin {x : Nat} (hx : (callStack fr).Contains x) :
      (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16).Contains x := by
    rw [stackEq] at hx
    simp only [Stack.region, MemoryRegion.Contains] at hx ⊢
    omega
  have stackApart {r : MemoryRegion}
      (hr : r ∈ [keyRegion initial 16, span fr.rsi 12, span fr.rdx aad.size] ++ [buffer]) :
      (callStack fr).Disjoint r :=
    fun x hx hy => hsep.1 r hr x hy (stackWithin hx)
  have nonceApart : (callStack fr).Disjoint (span fr.rsi 12) := stackApart (by simp)
  have aadApart : (callStack fr).Disjoint (span fr.rdx aad.size) := stackApart (by simp)
  have stackInputs {r : MemoryRegion} (rApart : (callStack fr).Disjoint r) :
      ∀ s ∈ [span fr.rsi 12, span fr.rdx aad.size, r], (callStack fr).Disjoint s := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact nonceApart
    · exact aadApart
    · exact rApart
  have bufferApart : (callStack fr).Disjoint buffer := stackApart (by simp)
  have preserveInput {p : BitVec 64} {n : Nat} {input : ByteArray}
      (hbound : (span p n).Bounded) (hb : (span p n).HasBytes initial.external input)
      (hapart : (callStack fr).Disjoint (span p n)) :
      Readable mem p n ∧ (span p n).HasBytes mem input := by
    have hsize : input.size = n := hb.1
    have hr := Readable.of_hasBytes hb hbound
    rw [hsize] at hr
    simp only [span, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr
    have hlow := hr.low
    refine ⟨hr.of_frame hf, hasBytes_of_frame hf hb (by change p.toNat + n ≤ 2 ^ 64; omega) ?_⟩
    intro r hmem x hx hy
    obtain rfl := List.mem_singleton.mp hmem
    rw [stackEq] at hapart
    exact hapart x (Activation.ofEntry_region_within x hy) hx
  obtain ⟨nr, nb⟩ := preserveInput hnonce.2.1 hnonce.2.2 nonceApart
  obtain ⟨ar, ab⟩ := preserveInput haad.2.1 haad.2.2 aadApart
  change cap.toNat = capacity ∧ _
  rcases hc with hc | ⟨hempty, hc⟩
  · have hlen : fr.r9.toNat = bytes.size := hc.lengthArgumentMatchesBuffer
    have hfits : (entryActivation initial ret).r9.toNat ≤ cap.toNat := by
      change fr.r9.toNat ≤ cap.toNat
      rw [hlen, hcapNat]
      exact hc.outputInMemory.2.1
    have prefixWithin {x : Nat} (hx : (span fr.r8 bytes.size).Contains x) : buffer.Contains x := by
      have hsize := hc.outputInMemory.2.1
      simp only [MemoryRegion.Contains, buffer, span] at hx ⊢
      omega
    have prefixApart : (callStack fr).Disjoint (span fr.r8 bytes.size) :=
      fun x hx hy => bufferApart x hx (prefixWithin hy)
    have prefixBound : (span fr.r8 bytes.size).Bounded := by
      have hbound : fr.r8.toNat + capacity < 2 ^ 32 := hbuffer.2.1
      have hsize := hc.outputInMemory.2.1
      change fr.r8.toNat + bytes.size < 2 ^ 32
      omega
    obtain ⟨br, bb⟩ := preserveInput prefixBound hc.outputInMemory.2.2 prefixApart
    have avoidBuffer : buffer.Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat) :=
      hsep.2.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [selectedLength, selectedPointer, hfits, ↓reduceIte]
    refine ⟨hcapNat, hlen, Or.inl True.intro, hrcx, nr, nb, ar, ab, br, bb, ?_, stackInputs prefixApart, ?_, ?_⟩
    · intro hpos
      have hw : Writable Extracted.programImage initial.external fr.r8 bytes.size :=
        Writable.of_avoids hbuffer.2.1 hbuffer.2.2 avoidBuffer
          (fun x hx => Or.inl ⟨x.2, hx⟩) (fun _ h => Or.inr (not_pageTableEntriesApart_frames h))
          (Nat.le_refl _) (Nat.add_le_add_left hc.outputInMemory.2.1 _) hpos
      exact hw.of_frame hf
    · intro r hr x hx
      exact hsep.2.1 _ List.mem_cons_self r (List.mem_cons_of_mem _ hr) x (prefixWithin hx)
    · intro slot hs x hx hy
      have slotBounds : FrameInfo.slotsLow entryCallSlots ≤ slot.toNat ∧
          slot.toNat + 8 ≤ FrameInfo.slotsHigh entryCallSlots := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl <;> decide
      have inside := prefixWithin hx
      have addr : (BitVec.ofNat 64 x).toNat = x := by
        have hbound : fr.r8.toNat + capacity < 2 ^ 32 := hbuffer.2.1
        simp only [MemoryRegion.Contains, buffer, span] at inside
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine avoidBuffer (BitVec.ofNat 64 x) (by rwa [addr]) (Or.inl ?_)
      simp only [MemoryRegion.Contains, span] at hy
      apply root_callSlots_span (m := LIR.Aes128gcmEncryptInPlace.frameInfo) rfl
      · rw [addr]
        exact Nat.le_trans slotBounds.1 hy.1
      · rw [addr]
        exact Nat.lt_of_lt_of_le hy.2 slotBounds.2
  · subst bytes
    have htooLong : ¬ (entryActivation initial ret).r9.toNat ≤ cap.toNat := by
      rw [hcapNat]
      exact Nat.not_le_of_lt hc.lengthArgumentExceedsCapacity
    have emptySpan {x : Nat} (hx : (span 1 0).Contains x) : False := by
      simp only [MemoryRegion.Contains, span, Nat.add_zero] at hx
      omega
    simp only [selectedLength, selectedPointer, htooLong, ↓reduceIte]
    refine ⟨hcapNat, rfl, Or.inr rfl, hrcx, nr, nb, ar, ab, ?_, ?_, ?_, stackInputs (fun _ _ hx => emptySpan hx), ?_, ?_⟩
    · exact ⟨by decide, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
    · exact ⟨rfl, fun i => (Nat.not_lt_zero _ i.isLt).elim⟩
    · intro hp
      exact (Nat.lt_irrefl _ hp).elim
    · exact fun _ _ _ hx => (emptySpan hx).elim
    · exact fun _ _ _ hx => (emptySpan hx).elim

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
