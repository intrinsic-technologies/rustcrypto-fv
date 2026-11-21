import K256.Proofs.Sec1.Affine.IdentityCall
import K256.Proofs.Sec1.Affine.Routines
import K256.Proofs.Sec1.Affine.Routes.CoordinateCall

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

theorem decodeCoordinateCall {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m)
    {tag : BitVec 8} (inputTag : (bytes.data[0]?.getD 0).toBitVec = tag)
    (tagValid : tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5) (size : bytes.size ≤ 65)
    (routine : CoordinateRoutine s bytes tag) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480,args,m⟩,[]⟩ out ∧
      ReturnAt (s.regValue .rsp-600) bytes args m out := by
  let fr := activation s
  let sp := fr.rsp-136
  let code := Extracted.programImage
  let compressed := tag != 4
  let ret : BitVec 64 := if compressed then 0x1214ce else 0x121502
  let resume := if compressed then Label.l1214ce else .l121502
  obtain ⟨base, entry, ax, _, dx, atoms, saved, preserved⟩ := e.start call
  rw [inputTag] at entry ax
  have accepted : 2 ≤ tag.toNat ∧ tag.toNat < 6 := by rcases tagValid with h | h | h | h <;> rw [h] <;> decide
  rw [ite_eq_left accepted] at entry
  have frame := atoms
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at frame
  obtain ⟨bsp,bdf,bbx,b13,bmx,bft,bfc,_,_,_,_,_,_,_,_,write,room,_,_⟩ := frame
  change fr.low.toNat + 1192 ≤ fr.rsp.toNat at room
  have scratch : Writable code (saveRegisters args m) (sp-9) 9 := by
    rw [show sp - 9 = fr.rsp-145 by dsimp only [sp]; bv_omega]
    exact write.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨child, entered, route, crsp, cdi, csi, c14, cdx, keep, slot, pushed⟩ :=
    reachCoordinateCall Common.fnCode_subset_programImage tagValid ax dx bsp scratch
  have cm := coordinateMemory_of_packing call e size (prefixFrame (by omega : 145 ≤ fr.rsp.toNat) saved pushed)
  let cf := childActivation s entered tag
  have initial := (e.registers call).2
  have fixed_ : CoordinateRegisters cf child := by
    refine ⟨crsp,cdi,csi,cdx,(keep 22 (by decide)).trans bdf,?_⟩
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (keep 3 (by decide)).trans bbx
    · exact (keep 5 (by decide)).trans ((preserved 5 (by decide)).trans (initial 5 (by decide)))
    · exact (keep 12 (by decide)).trans ((preserved 12 (by decide)).trans (initial 12 (by decide)))
    · exact (keep 13 (by decide)).trans b13
    · exact c14
    · exact (keep 15 (by decide)).trans ((preserved 15 (by decide)).trans (initial 15 (by decide)))
    · exact (keep 39 (by decide)).trans bmx
    · exact (keep 50 (by decide)).trans bft
    · exact (keep 51 (by decide)).trans bfc
  obtain ⟨o, nested, returned, rsp, regs, writes, point⟩ := routine child entered cm fixed_ slot
  have middle := coordinateFrames (by omega : 1192 ≤ fr.rsp.toNat) pushed writes
  have after := frameAfterCoordinates atoms (fun i hi => (regs i hi).trans
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))) rsp middle
  have gate : (Wrapper.callFrame resume ret).Accepts (dialect code) o.tag = true := by
    rw [returned]
    change decide (_ = _) = true
    exact decide_eq_true rfl
  have back : (program.sem (dialect code)).Reaches
      ⟨⟨.l1214a0,base,saveRegisters args m⟩,[]⟩ ⟨⟨resume,o.values,o.store⟩,[]⟩ :=
    route.trans (ParseSignature.exec_reaches_resume nested (Wrapper.callFrame resume ret) [] gate)
  have atCopy : Parser.Reaches code .l1214a0 base (saveRegisters args m) .l121502 o.values o.store := by
    by_cases h : compressed = true
    · have h' : resume = .l1214ce := ite_eq_left h
      rw [h'] at back
      exact back.trans (Parser.reaches_jump (resumeCompressed o.values o.store))
    · have h' : resume = .l121502 := ite_eq_right h
      rwa [h'] at back
  have win := activationOutputWritable call (e.savedFrame call saved)
  have above := activationOutputAbove call
  obtain ⟨out, tail, tagOut, done_, _, written, validity, copy⟩ :=
    finishCoordinates Common.fnCode_subset_programImage fr o.values o.store after (win.of_frame middle) (.inr above)
  obtain ⟨spOut, kept⟩ := e.returnedRegisters call done_
  have saved' := (RamWriteFrame.refl m (Parser.affineWrites (s.regValue .rsp-600))).trans saved (savedWithin call)
  have mid := saved'.trans middle (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have baseEq : fr.rsp - 1192 = s.regValue .rsp-600-1200 := by change _ - 8 - 1192 = _; bv_omega
    refine ⟨_,List.mem_cons_self,?_,?_⟩ <;> dsimp only [Parser.affineWrites] <;> rw [baseEq] <;> omega)
  have all := mid.trans written (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩)
  refine ⟨out,Program.Exec.of_sem (((Parser.reaches_jump entry).trans atCopy).exec tail.sem),
    tagOut,spOut,kept,all,?_⟩
  have nz : bytes.data[0]?.getD 0 ≠ 0 := by
    intro h
    rw [h] at inputTag
    rcases tagValid with h | h | h | h <;> rw [h] at inputTag <;> contradiction
  rw [ite_eq_right nz]
  have result := finishResult validity copy point
  change ResultAt out.store fr.rdi (K256.Spec.Secp256k1.decodePublicKey bytes) at result
  unfold ResultAt at result
  change (match K256.Spec.Secp256k1.decodePublicKey bytes with
    | none => memLoad out.store (s.regValue .rsp-600+248) 8 = 0
    | some p => memLoad out.store (s.regValue .rsp-600+248) 8 = 1 ∧ Parser.PublicKeyAt out.store fr.rdi p)
  rwa [show fr.rdi+88 = s.regValue .rsp-600+248 by dsimp only [fr,activation]; bv_omega] at result

end K256.Proofs.Sec1.Affine
