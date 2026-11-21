import AesGcm.Proofs.Machine.LIR.Aes256gcmDecryptInPlace.Frame
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256

open AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem buffer_inputs_of_validCall {initial : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {aad sealed : ByteArray} {ret : BitVec 64} {mem : Ram}
    (hCall : InPlace.ValidCall aes256gcmDecryptInPlace initial key nonce aad sealed
      sealed.size sealed.size)
    (hf : RamWriteFrame initial.external mem
      [(Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret).region]) :
    let fr := Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret
    Readable mem fr.rsi 12 ∧ (span fr.rsi 12).HasBytes mem ⟨nonce.toArray⟩ ∧
    Readable mem fr.rdx aad.size ∧ (span fr.rdx aad.size).HasBytes mem aad ∧
    Readable mem fr.r8 sealed.size ∧ (span fr.r8 sealed.size).HasBytes mem sealed ∧
    (0 < sealed.size - 16 → Writable Extracted.programImage mem fr.r8 (sealed.size - 16)) ∧
    (∀ r ∈ [span fr.rsi 12, span fr.rdx aad.size, span fr.r8 sealed.size],
      (callStack fr).Disjoint r) ∧
    (∀ r ∈ [span fr.rsi 12, span fr.rdx aad.size],
      (span fr.r8 (sealed.size - 16)).Disjoint r) ∧
    (∀ slot ∈ ([0x201208, 0x201210, 0x201228, 0x201230] : List (BitVec 64)),
      (span fr.r8 (sealed.size - 16)).Disjoint (span slot 8)) := by
  let fr := Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret
  change RamWriteFrame initial.external mem [fr.region] at hf
  have stackEq : callStack fr =
      Stack.region initial aes256gcmDecryptInPlace.minStackBytes 8 := by
    simp only [callStack, Stack.region, fr, Activation.ofEntry_low_toNat]
    rfl
  have stackApart : ∀ r ∈ [span fr.rsi 12, span fr.rdx aad.size, span fr.r8 sealed.size],
      (callStack fr).Disjoint r := by
    intro r hr x hx hy
    rw [stackEq] at hx
    exact hCall.separation.1 r (List.mem_cons_of_mem _ hr) x hy hx
  have preserveInput {p : BitVec 64} {n : Nat} {bytes : ByteArray}
      (hbound : (span p n).Bounded) (hb : (span p n).HasBytes initial.external bytes)
      (hsep : (callStack fr).Disjoint (span p n)) :
      Readable mem p n ∧ (span p n).HasBytes mem bytes := by
    have hsize : bytes.size = n := hb.1
    have hr := Readable.of_hasBytes hb hbound
    rw [hsize] at hr
    simp only [span, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr
    have hlow : p.toNat + n ≤ 2 ^ 64 := by have := hr.low; omega
    refine ⟨hr.of_frame hf, hasBytes_of_frame hf hb hlow ?_⟩
    intro r hmem x hx hy
    obtain rfl := List.mem_singleton.mp hmem
    rw [stackEq] at hsep
    exact hsep x (Activation.ofEntry_region_within x hy) hx
  obtain ⟨nr, nb⟩ := preserveInput (p := fr.rsi) hCall.nonceInMemory.2.1 hCall.nonceInMemory.2.2
    (stackApart _ (by simp))
  obtain ⟨ar, ab⟩ := preserveInput (p := fr.rdx) hCall.associatedDataInMemory.2.1
    hCall.associatedDataInMemory.2.2 (stackApart _ (by simp))
  obtain ⟨sr, sb⟩ := preserveInput (p := fr.r8) hCall.outputInMemory.1.2.1 hCall.outputInMemory.2.2
    (stackApart _ (by simp))
  have avoidBuffer : (span fr.r8 sealed.size).Avoids
      (fun address => InProgram address ∨ pageTables.Contains address.toNat) :=
    hCall.separation.2.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have prefixWithin (x : Nat) (hx : (span fr.r8 (sealed.size - 16)).Contains x) :
      (span fr.r8 sealed.size).Contains x := by
    simp only [MemoryRegion.Contains, span] at hx ⊢
    omega
  refine ⟨nr, nb, ar, ab, sr, sb, ?_, stackApart, ?_, ?_⟩
  · intro hp
    have hw : Writable Extracted.programImage initial.external fr.r8 (sealed.size - 16) :=
      Writable.of_avoids hCall.outputInMemory.1.2.1 hCall.outputInMemory.1.2.2 avoidBuffer
        (fun x hx => Or.inl ⟨x.2, hx⟩) (fun _ h => Or.inr (not_pageTableEntriesApart_frames h))
        (Nat.le_refl _) (Nat.add_le_add_left (Nat.sub_le _ _) _) hp
    exact hw.of_frame hf
  · intro r hr x hx
    exact hCall.separation.2.1 _ List.mem_cons_self r (List.mem_cons_of_mem _ hr) x (prefixWithin x hx)
  · intro slot hs x hx hy
    have slotBounds : FrameInfo.slotsLow entryCallSlots ≤ slot.toNat ∧
        slot.toNat + 8 ≤ FrameInfo.slotsHigh entryCallSlots := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> decide
    have inside := prefixWithin x hx
    have low := sr.low
    have addr : (BitVec.ofNat 64 x).toNat = x := by
      simp only [MemoryRegion.Contains, span] at inside
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine avoidBuffer (BitVec.ofNat 64 x) (by rwa [addr]) (Or.inl ?_)
    simp only [MemoryRegion.Contains, span] at hy
    apply root_callSlots_span (m := LIR.Aes256gcmDecryptInPlace.frameInfo) rfl
    · rw [addr]
      exact Nat.le_trans slotBounds.1 hy.1
    · rw [addr]
      exact Nat.lt_of_lt_of_le hy.2 slotBounds.2

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256
