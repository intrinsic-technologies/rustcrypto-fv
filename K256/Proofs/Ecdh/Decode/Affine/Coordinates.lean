import K256.Proofs.Ecdh.Decode.Affine.Child
import K256.Proofs.Ecdh.Decode.Affine.Entry
import K256.Proofs.Ecdh.Decode.Affine.Frame
import K256.Proofs.Ecdh.Decode.Affine.Selection

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Affine Standards.SECG.ECC

theorem coordinateExecution {fr : Activation} {args m bytes} (e : Entry fr args m bytes)
    {tag : UInt8} {p : Curve.Point} (header : bytes.data[0]? = some tag)
    (valid : tag = 2 ∨ tag = 3 ∨ tag = 5) (size : bytes.size = 33)
    (decoded : Sec1.decompress (if tag = 5 then 2 else tag)
      (Encoding.octetsToNat (bytes.extract 1 33)) = some p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480,args,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ out.values[4] = ⟨64,fr.rsp+8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame m out.store (writes fr) ∧ memLoad out.store (fr.rdi+88) 8 = 1 ∧
      AffinePointAt out.store fr.rdi p ∧ CallerWidths out.values := by
  obtain ⟨base,entry,ax,_,dx,atoms,saved,preserved⟩ := e.start
  have accepted : 2 ≤ tag.toBitVec.toNat ∧ tag.toBitVec.toNat < 6 := by
    rcases valid with rfl | rfl | rfl <;> decide
  have alternatives : tag.toBitVec = 2 ∨ tag.toBitVec = 3 ∨ tag.toBitVec = 4 ∨ tag.toBitVec = 5 := by
    rcases valid with rfl | rfl | rfl <;> decide
  have compressed : (tag.toBitVec != 4) = true := by rcases valid with rfl | rfl | rfl <;> decide
  simp only [header,Option.getD_some] at ax
  rw [header,Option.getD_some,ite_eq_left accepted] at entry
  have frame := atoms
  simp only [Fn121480.frameAt,Fn121480.frameAtG2,Atom.All,Atom.Holds] at frame
  obtain ⟨bsp,bdf,bbx,b13,bmx,bft,bfc,_,_,_,_,_,_,_,_,write,room,_,_⟩ := frame
  change fr.low.toNat + 1192 ≤ fr.rsp.toNat at room
  have scratch : Writable Extracted.programImage (saveRegisters args m) (fr.rsp-136-9) 9 := by
    rw [show fr.rsp-136-9 = fr.rsp-145 by bv_omega]
    exact write.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨child,n,route,crsp,cdi,csi,c14,cdx,keep,slot,pushed⟩ :=
    reachCoordinateCall Common.fnCode_subset_programImage alternatives ax dx bsp scratch
  simp only [compressed,ite_true] at route cdx slot
  rw [ite_eq_left compressed] at route
  let cf := childFrame fr n tag.toBitVec
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
  obtain ⟨o,nested,returned,rsp,regs,writesChild,ok,point⟩ := childExecution e fixed_ slot prefixWrites valid size decoded
  have middle := coordinateFrames (by omega : 1192 ≤ fr.rsp.toNat) pushed writesChild
  have after := frameAfterCoordinates atoms (fun i hi => (regs i hi).trans
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))) rsp middle
  have gate : (Sec1.Wrapper.callFrame .l1214ce 0x1214ce).Accepts (dialect Extracted.programImage) o.tag = true := by
    rw [returned]
    rfl
  have back := route.trans (ParseSignature.exec_reaches_resume nested (Sec1.Wrapper.callFrame .l1214ce 0x1214ce) [] gate)
  have atCopy := back.trans (Sec1.Parser.reaches_jump (resumeCompressed o.values o.store))
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

end K256.Proofs.Ecdh.Decode.Affine
