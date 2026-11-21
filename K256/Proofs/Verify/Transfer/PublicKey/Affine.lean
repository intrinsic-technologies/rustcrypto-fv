import K256.Proofs.Verify.Transfer.PublicKey.Affine.Child

namespace K256.Proofs.Verify.Transfer.PublicKey

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR Standards.SECG.ECC

open K256.Proofs.Sec1.Affine K256.Proofs.Ecdh.Decode.Affine

theorem affine {fr : Activation} {b m bytes} (e : Ecdh.Decode.Affine.Entry fr b m bytes)
    (size : bytes.size = 65) (head : bytes.data[0]? = some 4) {p : Curve.Point}
    (decoded : K256.Spec.Secp256k1.decodePublicKey bytes = some p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480,b,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ out.values[4] = ⟨64,fr.rsp+8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = b[i]) ∧
      RamWriteFrame m out.store (Ecdh.Decode.Affine.writes fr) ∧ memLoad out.store (fr.rdi+88) 8 = 1 ∧
      Ecdh.Decode.AffinePointAt out.store fr.rdi p ∧ Ecdh.Decode.Affine.CallerWidths out.values := by
  obtain ⟨base,entry,ax,_,dx,atoms,saved,preserved⟩ := e.start
  have accepted : 2 ≤ (4 : UInt8).toBitVec.toNat ∧ (4 : UInt8).toBitVec.toNat < 6 := by decide
  simp only [head,Option.getD_some] at ax
  rw [head,Option.getD_some,ite_eq_left accepted] at entry
  have frame := atoms
  simp only [Fn121480.frameAt,Fn121480.frameAtG2,Atom.All,Atom.Holds] at frame
  obtain ⟨bsp,bdf,bbx,b13,bmx,bft,bfc,_,_,_,_,_,_,_,_,write,room,_,_⟩ := frame
  change fr.low.toNat + 1192 ≤ fr.rsp.toNat at room
  have scratch : Writable Extracted.programImage (saveRegisters b m) (fr.rsp-136-9) 9 := by
    rw [show fr.rsp-136-9 = fr.rsp-145 by bv_omega]
    exact write.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨child,n,route,crsp,cdi,csi,c14,cdx,keep,slot,pushed⟩ :=
    reachCoordinateCall Common.fnCode_subset_programImage (tag := 4) (by decide) ax dx bsp scratch
  let cf := uncompressedFrame fr n
  have fixed_ : CoordinateRegisters cf child := by
    refine ⟨crsp,cdi,csi,cdx,(keep 22 (by decide)).trans bdf,?_⟩
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (keep 3 (by decide)).trans bbx
    · exact (keep 5 (by decide)).trans ((preserved 5 (by decide)).trans (e.saved 5 (by decide)))
    · exact (keep 12 (by decide)).trans ((preserved 12 (by decide)).trans (e.saved 12 (by decide)))
    · exact (keep 13 (by decide)).trans b13
    · exact c14
    · exact (keep 15 (by decide)).trans ((preserved 15 (by decide)).trans (e.saved 15 (by decide)))
    · exact (keep 39 (by decide)).trans bmx
    · exact (keep 50 (by decide)).trans bft
    · exact (keep 51 (by decide)).trans bfc
  have prefixWrites := prefixFrame (by omega : 145 ≤ fr.rsp.toNat) saved pushed
  obtain ⟨o,nested,returned,rsp,regs,writesChild,ok,point⟩ := uncompressedChild e fixed_ slot prefixWrites size head decoded
  have middle := coordinateFrames (by omega : 1192 ≤ fr.rsp.toNat) pushed writesChild
  have after := frameAfterCoordinates atoms (fun i hi => (regs i hi).trans
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))) rsp middle
  have gate : (Sec1.Wrapper.callFrame .l121502 0x121502).Accepts (dialect Extracted.programImage) o.tag = true := by
    rw [returned]
    rfl
  have atCopy : Sec1.Parser.Reaches Extracted.programImage .l1214a0 base (saveRegisters b m) .l121502 o.values o.store := route.trans (ParseSignature.exec_reaches_resume nested (Sec1.Wrapper.callFrame .l121502 0x121502) [] gate)
  have win := (e.output.of_frame saved).of_frame middle
  obtain ⟨out,tail,tagOut,done_,_,written,flag,_⟩ := finishCoordinates Common.fnCode_subset_programImage
    fr o.values o.store after win (.inr e.dstAbove)
  obtain ⟨spOut,kept⟩ := e.returnedRegisters done_
  have mid := (e.afterSaves saved).trans middle (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.add_le_add_left (by decide : 1145 ≤ 1192) _⟩)
  exact ⟨out,Program.Exec.of_sem (((Sec1.Parser.reaches_jump entry).trans atCopy).exec tail.sem),
    tagOut,spOut,kept,withOutput mid written,flag.trans ok,finishPointAt after win tail ok point⟩

end K256.Proofs.Verify.Transfer.PublicKey
