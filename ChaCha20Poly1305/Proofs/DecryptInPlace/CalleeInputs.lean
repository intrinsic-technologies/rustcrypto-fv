import ChaCha20Poly1305.Proofs.DecryptInPlace.Regions

namespace ChaCha20Poly1305.Proofs.DecryptInPlace

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift Prelude
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open ChaCha20Poly1305.Proofs.Decrypt

variable [b : Bindings] {s u : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {aad msg : ByteArray}

omit b in
private theorem readKept (hc : ValidCall decryptInPlace s [key,nonce,aad,msg])
    (fr : RamWriteFrame s.external u.external [scratch s]) {r : MemoryRegion} {bytes : ByteArray}
    (member : r ∈ readRegions decryptInPlace s [key,nonce,aad,msg]) (v : ValidInput s r bytes) :
    r.HasBytes u.external bytes := by
  refine ⟨v.2.1,fun i => ?_⟩
  have size : bytes.size = r.size := v.2.1
  have low : r.start+r.size < 2^32 := v.1
  have apart := readStackApart hc member (by have := i.isLt; omega)
  have ar : (BitVec.ofNat 64 (r.start+i.val)).toNat = r.start+i.val :=
    Nat.mod_eq_of_lt (by have := i.isLt; omega)
  rw [fr.outside _ ⟨by have := i.isLt; omega,?_⟩]
  · exact v.2.2 i
  · intro q hq
    obtain rfl := List.mem_singleton.mp hq
    have floor := stackFloor hc
    change _ ≤ (stackPtr s).toNat-1072 ∨ (stackPtr s).toNat-1072+1072 ≤ _
    have := i.isLt
    omega

set_option allowUnsafeReducibility true in
attribute [local reducible] Decrypt.Lifted.lifted
set_option maxRecDepth 4000 in
set_option maxHeartbeats 500000 in
theorem calleeInputs (hc : ValidCall decryptInPlace s [key, nonce, aad, msg])
    (long : 16 ≤ msg.size) (small : msg.size < 2^32) (atCall : AtDetached s u (inPlacePacket s key nonce aad msg long small)) :
    Atom.All Decrypt.Lifted.fnCode (Decrypt.Lifted.lifted.locationOf .l1001f0 u).arguments u.external
      ((Detached.detachedFn (inPlacePacket s key nonce aad msg long small)).pre (calleeFrame u)) := by

  let p := inPlacePacket s key nonce aad msg long small
  let f := calleeFrame u
  let sp := stackPtr s
  have ag := atCall.track.agrees
  have fr := widenToScratch hc (by decide : 80 ≤ 1072) (callFrame hc atCall)
  have floor := stackFloor hc
  have top := stackTop hc
  change 1072 ≤ sp.toNat at floor
  change sp.toNat+8<2^32 at top
  have subNat (k : Nat) (le : k ≤ 1072) :
      (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by bv_omega
  have fs : f.rsp = sp-80 := atCall.rsp
  have spNat : f.rsp.toNat = sp.toNat-80 := fs ▸ subNat 80 (by decide)
  have fk : f.rdi = sp-32 := atCall.keyPtr
  have fd : f.r8 = sp-56 := atCall.desc
  have fnonce : f.rsi = s.regValue .rsi := ag.agree (.reg 6) (by simp [callChanges]) rfl
  have faad : f.rdx = s.regValue .rdx := ag.agree (.reg 2) (by simp [callChanges]) rfl
  have fl : f.rcx.toNat = aad.size := (congrArg BitVec.toNat atCall.aadLen).trans hc.lengthArgumentsMatchInputs.2.2.1
  have len : p.n.toNat = msg.size-16 := Nat.mod_eq_of_lt (by omega)
  have base : p.buf = s.regValue .rcx := rfl
  have apart := bufferStackApart hc (by omega)
  change (s.regValue .rcx).toNat + msg.size ≤ sp.toNat-1072 ∨ sp.toNat+8 ≤ (s.regValue .rcx).toNat at apart
  have window := (stackWritable hc).of_frame fr
  have nonceV : ValidInput s (registerRegion s .rsi 12) (nonce : ByteArray) := hc.inputsInMemory.2.1
  have nonceIn : registerRegion s .rsi 12 ∈ readRegions decryptInPlace s [key,nonce,aad,msg] := by
    simp [readRegions,decryptInPlace,inputRegion]
  have nonceSep := readStackApart hc nonceIn (by change 0<12; decide)
  change (s.regValue .rsi).toNat+12 ≤ sp.toNat-1072 ∨ sp.toNat+8 ≤ (s.regValue .rsi).toNat at nonceSep
  have nonceB := readKept hc fr nonceIn nonceV
  have nr := Readable.of_hasBytes nonceB nonceV.1
  change Readable u.external (BitVec.ofNat 64 (s.regValue .rsi).toNat) (nonce : ByteArray).size at nr
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,show (nonce : ByteArray).size=12 from nonce.size_toArray] at nr
  have bytes := Detached.bytesOfRegion (p:=s.regValue .rsi) nonceB
  have n0 := Detached.pairAt bytes 0 (by decide)
  have n1 := Detached.wordAt bytes 2 (by decide)
  have aadV : ValidInput s (registerRegion s .rdx aad.size) aad := hc.inputsInMemory.2.2.1
  have aadLow : (s.regValue .rdx).toNat+aad.size < 2^32 := aadV.1
  have aadIn : registerRegion s .rdx aad.size ∈ readRegions decryptInPlace s [key,nonce,aad,msg] := by
    simp [readRegions,decryptInPlace,inputRegion]
  have aadB := readKept hc fr aadIn aadV
  have pa : p.pa = (if aad.size=0 then 0 else s.regValue .rdx) := rfl
  have aadAll : Readable u.external p.pa aad.size ∧ memLoad u.external p.pa (8*aad.size)=Bytes.packed aad ∧
      (p.pa.toNat+aad.size≤sp.toNat-1072 ∨ sp.toNat+8≤p.pa.toNat) := by
    rw [pa]
    by_cases empty : aad.size=0
    · simp only [ite_eq_left empty]
      refine ⟨⟨by rw [empty]; decide,by intro i h; omega⟩,?_,Or.inl (by simp [empty])⟩
      have eq {w : Nat} (x y : BitVec w) (zero : w=0) : x=y := by subst w; exact Subsingleton.elim _ _
      exact eq _ _ (by omega)
    · simp only [ite_eq_right empty]
      refine ⟨?_,?_,readStackApart hc aadIn (by change 0<aad.size; omega)⟩
      · simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Readable.of_hasBytes aadB aadV.1
      · simpa only [registerRegion,BitVec.ofNat_toNat,BitVec.setWidth_eq] using Bytes.mem_packed aadB
  have stk : Stack.region s decryptInPlace.minStackBytes ∈ writtenRegions decryptInPlace s [key,nonce,aad,msg] :=
    written s _ ▸ .tail _ (.head _)
  have buf : registerRegion s .rcx msg.size ∈ writtenRegions decryptInPlace s [key,nonce,aad,msg] := by
    rw [written,buffer hc]; exact .head _
  have checkImage (r : MemoryRegion) (hr : r ∈ writtenRegions decryptInPlace s [key,nonce,aad,msg])
      (pos : 0<r.size) : r.start + r.size ≤ 0x100000 ∨ 0x102def ≤ r.start :=
    imageApart hc hr pos (show Decrypt.Lifted.textSection ∈ Extracted.programSections from .head _)
      (by decide) (by decide +kernel) (by decide) (by decide)
  have stCode := checkImage _ stk (by change 0 < sp.toNat+8-(sp.toNat-1072); omega)
  change sp.toNat-1072+(sp.toNat+8-(sp.toNat-1072)) ≤ _ ∨ _ ≤ sp.toNat-1072 at stCode
  have bufCode := checkImage _ buf (by change 0<msg.size; omega)
  change (s.regValue .rcx).toNat+msg.size ≤ _ ∨ _ ≤ (s.regValue .rcx).toNat at bufCode
  have valid := hc.outputInMemory (by simp [Routine.needsOutput,decryptInPlace])
  rw [buffer hc] at valid
  have wr : Writable Decrypt.Lifted.fnCode s.external (s.regValue .rcx) msg.size :=
    Writable.of_avoids valid.1 valid.2 (hc.separation.2.2 _ buf) code_forbidden tables_forbidden
      (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have dstWrite : Writable Decrypt.Lifted.fnCode u.external p.buf p.n.toNat := by
    rw [base,len]
    exact (wr.of_frame fr).sub (Nat.le_refl _) (by omega)
  have ct := (ciphertextParts hc long small fr).1
  have rd (d n : Nat) (hd : d≤1072) (hn : n≤d+8) : Readable u.external (sp-BitVec.ofNat 64 d) n :=
    window.readable.sub (by rw [show (stackPtr s-1072).toNat = sp.toNat-1072 from subNat 1072 (by decide),subNat d hd]; omega)
      (by rw [show (stackPtr s-1072).toNat = sp.toNat-1072 from subNat 1072 (by decide),subNat d hd]; omega)
  have keyAt := atCall.keyWords
  have first := keyAt (0 : Fin 4)
  change memLoad u.external (sp-32+0) 64 = p.x.k[0] at first
  rw [show sp-32+0=sp-32 by bv_omega] at first
  change memLoad u.external (s.regValue .rsi + 0) 64 = p.x.nl at n0
  rw [show s.regValue .rsi + 0 = s.regValue .rsi by bv_omega] at n0
  have ctx : Atom.All Decrypt.Lifted.fnCode (Decrypt.Lifted.lifted.locationOf .l1001f0 u).arguments u.external
      (Detached.inputs p.x f) := by
    simp only [Detached.inputs,Atom.All,Atom.Holds,fk,fnonce]
    refine ⟨?_,?_,?_,?_,?_,n1,trivial⟩
    · exact first
    · exact keyAt 1
    · exact keyAt 2
    · exact keyAt 3
    · exact n0
  change Atom.All _ _ _ ((Detached.srcGeo f ++ Detached.inputs p.x f) ++ Detached.extraIn p f)
  rw [Atom.all_append,Atom.all_append]
  refine ⟨⟨?_,ctx⟩,?_⟩
  · simp only [Detached.srcGeo,Atom.All,Atom.Holds,fk,fs,fnonce]
    refine ⟨rd 32 32 (by decide) (by decide),nr,?_,?_,?_,trivial⟩
    all_goals simp only [show (sp-80).toNat = sp.toNat-80 from subNat 80 (by decide),
      show (sp-32).toNat = sp.toNat-32 from subNat 32 (by decide)] <;> omega
  · simp only [Detached.extraIn,Detached.vec,List.cons_append,List.nil_append,Atom.All,Atom.Holds]
    have desc1 : f.r8+8 = sp-48 := by rw [fd]; bv_omega
    have desc2 : f.r8+16 = sp-40 := by rw [fd]; bv_omega
    have slot : f.rsp+8 = sp-72 := by rw [fs]; bv_omega
    rw [desc1,desc2,slot,fd]
    refine ⟨rd 56 24 (by decide) (by decide),rd 72 8 (by decide) (by decide),aadAll.1,dstWrite,
      ?_,?_,?_,?_,?_,?_,fl,?_,?_,atCall.tagLo,atCall.tagHi,aadAll.2.1,ct,
      atCall.src,atCall.dst,atCall.len,trivial⟩
    · rw [spNat]; omega
    · rw [spNat, show (sp-56).toNat = sp.toNat-56 from subNat 56 (by decide)]; omega
    · have sep := aadAll.2.2; rw [spNat,show p.aad = aad from rfl]; omega
    · rw [base,len,spNat]; omega
    · rw [base,len,show (sp-56).toNat = sp.toNat-56 from subNat 56 (by decide)]; omega
    · rw [base,len]; omega
    · rw [fl]; omega
    · intro pos
      change 0 < aad.size at pos
      rw [faad,pa,ite_eq_right (Nat.ne_of_gt pos)]

end ChaCha20Poly1305.Proofs.DecryptInPlace
