import ChaCha20Poly1305.Proofs.Decrypt.PacketOf

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

theorem written (s : RamState) (inputs : List ByteArray) :
    writtenRegions decryptInPlace s inputs =
      [bufferRegion decryptInPlace s, Stack.region s decryptInPlace.minStackBytes] := by
  simp [writtenRegions, Routine.needsOutput, decryptInPlace]

theorem buffer (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    bufferRegion decryptInPlace s = registerRegion s .rcx msg.size := by
  have n : (s.regValue .r9).toNat = msg.size := hc.lengthArgumentsMatchInputs.2.2.2.1
  change registerRegion s .rcx (max ((s.regValue .r9).toNat - 16) (s.regValue .r9).toNat) = _
  rw [Nat.max_eq_right (Nat.sub_le _ _), n]

theorem output (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    outputRegion decryptInPlace s = registerRegion s .rcx (msg.size-16) := by
  have n : (s.regValue .r9).toNat = msg.size := hc.lengthArgumentsMatchInputs.2.2.2.1
  have room : hasRoom decryptInPlace s = true := decide_eq_true (Nat.le_max_left _ _)
  simp only [outputRegion, room, ite_true]
  change registerRegion s .rcx ((s.regValue .r9).toNat - 16) = _
  rw [n]

theorem stackFloor (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    1072 ≤ (stackPtr s).toNat := hc.stackAvailable.2.2.1

theorem stackTop (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    (stackPtr s).toNat + 8 < 2^32 := by
  have h := hc.stackAvailable.1
  change (stackPtr s).toNat-1072+((stackPtr s).toNat+8-((stackPtr s).toNat-1072)) < 2^32 at h
  omega

theorem bufferStackApart (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (pos : 0 < msg.size) :
    (s.regValue .rcx).toNat + msg.size ≤ (stackPtr s).toNat - 1072 ∨
      (stackPtr s).toNat + 8 ≤ (s.regValue .rcx).toNat := by
  have h := hc.separation.1
  rw [written,buffer hc] at h
  have hd := (List.pairwise_cons.mp h).1 _ (.head _)
  have floor := stackFloor hc
  have apart := apart_ends hd pos (by
    change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 1072)
    omega)
  change (s.regValue .rcx).toNat + msg.size ≤ (stackPtr s).toNat-1072 ∨
    (stackPtr s).toNat-1072+((stackPtr s).toNat+8-((stackPtr s).toNat-1072)) ≤ (s.regValue .rcx).toNat at apart
  omega

theorem readStackApart (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    {r : MemoryRegion} (hr : r ∈ readRegions decryptInPlace s [key,nonce,aad,msg])
    (pos : 0 < r.size) :
    r.start + r.size ≤ (stackPtr s).toNat - 1072 ∨ (stackPtr s).toNat + 8 ≤ r.start := by
  have floor := stackFloor hc
  have hd := hc.separation.2.1 _ (by rw [written]; exact .tail _ (.head _)) r hr
  have a := (apart_ends hd (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-1072); omega) pos).symm
  change _ ≤ (stackPtr s).toNat-1072 ∨
    (stackPtr s).toNat-1072+((stackPtr s).toNat+8-((stackPtr s).toNat-1072)) ≤ _ at a
  omega

theorem stackWritable (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    Writable Decrypt.Lifted.fnCode s.external (stackPtr s - 1072) 1080 := by
  have floor := stackFloor hc
  have start : (stackPtr s - 1072).toNat = (stackPtr s).toNat-1072 := by bv_omega
  apply Writable.of_avoids hc.stackAvailable.1 hc.stackAvailable.2.1
    (hc.separation.2.2 _ (by rw [written]; exact .tail _ (.head _)))
    code_forbidden tables_forbidden
  · exact Nat.le_of_eq start.symm
  · change _ ≤ (stackPtr s).toNat-1072+((stackPtr s).toNat+8-((stackPtr s).toNat-1072))
    omega
  · decide

theorem boundaryOutside (hc : ValidCall decryptInPlace s [key,nonce,aad,msg]) :
    ¬ InProgram (returnBoundary s).rip := by
  obtain ⟨ret,slot,_,away⟩ := hc.returnAddress
  change ¬ InProgram (memLoad s.external (s.regValue .rsp) 64)
  rwa [memLoad_returnSlot slot]

theorem slotWritable (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    {d len : Nat} (lo : len ≤ d) (hi : d ≤ 1072)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (u.external[a]?).isSome) :
    MemWritable u (stackPtr s - BitVec.ofNat 64 d) len := by
  have floor := stackFloor hc
  have w := (stackWritable hc).sub (n:=len) (a:=stackPtr s - BitVec.ofNat 64 d)
    (by bv_omega) (by bv_omega)
  exact ⟨w.readable.low,fun i h => grow _ (w.readable.present i h),w.tables⟩

theorem slotOutsideProgram (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    {d len : Nat} (lo : len ≤ d) (hi : d ≤ 1072) {x : BitVec 64}
    (covers : (Component.mem (stackPtr s - BitVec.ofNat 64 d) len).Covers x) :
    ¬ InProgram x := by
  obtain ⟨i,hi',rfl⟩ := covers
  have floor := stackFloor hc
  have top := stackTop hc
  apply fun hp => hc.separation.2.2 _ (by rw [written]; exact .tail _ (.head _)) _ ?_ (.inl hp)
  change (stackPtr s).toNat-1072 ≤ _ ∧ _ < (stackPtr s).toNat-1072 +
    ((stackPtr s).toNat+8-((stackPtr s).toNat-1072))
  constructor <;> bv_omega

theorem slotFits {sp : BitVec 64} {d len cap : Nat} (lo : len ≤ d) (hi : d ≤ cap) {x : BitVec 64}
    (covers : (Component.mem (sp - BitVec.ofNat 64 d) len).Covers x) :
    (Component.mem (sp - BitVec.ofNat 64 cap) cap).Covers x := by
  obtain ⟨i,hi',rfl⟩ := covers
  refine ⟨cap-d+i,by omega,?_⟩
  have eq := congrArg (BitVec.ofNat 64) (Nat.sub_add_cancel hi)
  rw [BitVec.ofNat_add] at eq ⊢
  bv_omega

theorem imageApart {routine : Routine} {ins : List ByteArray} (hc : ValidCall routine s ins)
    {r : MemoryRegion} (hw : r ∈ writtenRegions routine s ins) (pos : 0 < r.size)
    {sec : ImageSection} (hs : sec ∈ Extracted.programSections)
    {lo hi : Nat} (start : sec.address.toNat ≤ lo) (stop : hi ≤ sec.address.toNat + sec.bytes.size)
    (ordered : lo < hi) (bounded : hi ≤ 2^64) :
    r.start + r.size ≤ lo ∨ hi ≤ r.start := by
  apply apart_of_avoids (hc.separation.2.2 _ hw) _ pos ordered bounded
  intro a l h
  obtain ⟨v,hv⟩ := exists_mem_toCodeMap hs (a:=a) (Nat.le_trans start l) (Nat.lt_of_lt_of_le h stop)
  exact .inl ⟨v,fetch_image hv⟩

end ChaCha20Poly1305.Proofs.DecryptInPlace
