import ChaCha20Poly1305.Proofs.Decrypt.InputRanges

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Spec.Program
open Hash Detached

theorem nonceSupply {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (pos : 0<msg.size) {m : Ram}
    (frame : RamWriteFrame s.external m (prefixWrites s msg.size)) :
    let p := s.regValue .rsi
    Readable m p 12 ∧ memLoad m p 64=pair nonce 0 ∧ memLoad m (p+8) 32=(Detached.word nonce 2).toBitVec ∧
      (p.toNat+12≤(s.regValue .rsp).toNat-1136 ∨ (s.regValue .rsp).toNat+8≤p.toNat) := by
  let p := s.regValue .rsi
  have h : ValidInput s (registerRegion s .rsi 12) (nonce : ByteArray) := hc.inputsInMemory.2.1
  have away := readAway hc pos (r:=registerRegion s .rsi 12) (by change 0<12; decide)
    (by simp [readRegions,decrypt,inputRegion])
  have floor : 1136≤(s.regValue .rsp).toNat := hc.stackAvailable.2.2.1
  have low : p.toNat+12<2^32 := h.1
  have rd := Readable.of_hasBytes h.2 h.1
  rw [show (nonce : ByteArray).size=12 from nonce.size_toArray] at rd
  have bytes := bytesOfRegion (p:=p) h.2
  have e0 := pairAt bytes 0 (by decide)
  have e1 := wordAt bytes 2 (by decide)
  change memLoad _ (p+0#64) 64=_ at e0
  rw [BitVec.add_zero] at e0
  have keep (i w : Nat) (n : i+w/8≤12) : memLoad m (p+BitVec.ofNat 64 i) w=memLoad s.external (p+BitVec.ofNat 64 i) w := by
    apply away.load frame floor (Nat.le_of_lt low)
    · change p.toNat≤(p+BitVec.ofNat 64 i).toNat; bv_omega
    · change (p+BitVec.ofNat 64 i).toNat+w/8≤p.toNat+12; bv_omega
  refine ⟨?_,?_,(keep 8 32 (by decide)).trans e1,away.stack⟩
  · apply Readable.of_frame _ frame
    simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using rd
  · have e := keep 0 64 (by decide)
    change memLoad m (p+0#64) 64=memLoad s.external (p+0#64) 64 at e
    rw [BitVec.add_zero] at e; exact e.trans e0

theorem aadSupply {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (pos : 0<msg.size) {m : Ram}
    (frame : RamWriteFrame s.external m (prefixWrites s msg.size)) :
    let p := if aad.size=0 then 0 else s.regValue .rdx
    Readable m p aad.size ∧ memLoad m p (8*aad.size)=Bytes.packed aad ∧
      (p.toNat+aad.size≤(s.regValue .rsp).toNat-1136 ∨ (s.regValue .rsp).toNat+8≤p.toNat) ∧ aad.size<2^32 := by
  have h : ValidInput s (registerRegion s .rdx aad.size) aad := hc.inputsInMemory.2.2.1
  have floor : 1136≤(s.regValue .rsp).toNat := hc.stackAvailable.2.2.1
  have low : (s.regValue .rdx).toNat+aad.size<2^32 := h.1
  by_cases z : aad.size=0
  · simp only [ite_eq_left z]
    refine ⟨⟨by rw [z]; decide,by intro i hi; omega⟩,?_,Or.inl (by rw [z]; simp),by omega⟩
    have one {n : Nat} (a b : BitVec n) (h : n=0) : a=b := by subst n; exact Subsingleton.elim _ _
    exact one _ _ (by omega)
  · simp only [ite_eq_right z]
    have away := readAway hc pos (r:=registerRegion s .rdx aad.size) (show 0<aad.size by omega)
      (by simp [readRegions,decrypt,inputRegion])
    refine ⟨?_,?_,away.stack,by omega⟩
    · apply Readable.of_frame _ frame
      simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Readable.of_hasBytes h.2 h.1
    · apply (away.load frame floor (Nat.le_of_lt low) (Nat.le_refl _) (by change (s.regValue .rdx).toNat+8*aad.size/8≤(s.regValue .rdx).toNat+aad.size; omega)).trans
      simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Bytes.mem_packed h.2

theorem aadLength {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (pos : 0<msg.size) {m : Ram}
    (frame : RamWriteFrame s.external m (prefixWrites s msg.size)) :
    Readable m (s.regValue .rsp+8) 8 ∧ memLoad m (s.regValue .rsp+8) 64=BitVec.ofNat 64 aad.size := by
  have arg : StackArgument s 0 (BitVec.ofNat 64 aad.size) := hc.lengthArgumentsMatchInputs.2.2.1
  have rd := slotRead arg
  have away := readAway hc pos (r:=stackArgumentSlot s 0) (show 0<8 by decide)
    (by simp [readRegions,decrypt,argumentRegions])
  have floor : 1136≤(s.regValue .rsp).toNat := hc.stackAvailable.2.2.1
  have low : (s.regValue .rsp).toNat+8+8<2^32 := arg.1
  have addr : BitVec.ofNat 64 (stackArgumentSlot s 0).start=s.regValue .rsp+8 := by
    change BitVec.ofNat 64 ((s.regValue .rsp).toNat+8)=_; bv_omega
  rw [addr] at rd
  refine ⟨rd.1.of_frame frame,(away.load frame floor (Nat.le_of_lt low) ?_ ?_).trans rd.2⟩
  · change (s.regValue .rsp).toNat+8≤(s.regValue .rsp+8).toNat; bv_omega
  · change (s.regValue .rsp+8).toNat+8≤(s.regValue .rsp).toNat+8+8; bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
