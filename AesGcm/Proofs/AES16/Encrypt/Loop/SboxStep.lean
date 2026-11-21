import AesGcm.Proofs.AES16.Encrypt.Loop.Progress
import AesGcm.Proofs.AES16.Encrypt.Loop.Key3

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option maxHeartbeats 600000 in
theorem sbox_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (fr : Activation)
    (loc : LIR.lifted.Location) (planes : Planes16)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hwork : WorkingState code use256 key fr loc)
    (hlabel : loc.label = (if use256 then .l106aa9 else .l105236))
    (hbuffer : loc.arguments[14]'(by change 14 < 53; decide) = ⟨64,buffer use256 fr⟩)
    (hWords : WordsAt loc.store (buffer use256 fr) 16 (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧
      next.label = (if use256 then .l106ab8 else .l105243) ∧
      WordsAt next.store (buffer use256 fr) 16 (Vector.ofFn (subBytes planes)) ∧
      next.arguments[12]'(by change 12 < 53; decide) = loc.arguments[12]'(by change 12 < 53; decide) ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64,buffer use256 fr⟩ := by
  dsimp only [LIR.lifted] at *
  have hbefore : frameAt use256 loc.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr := by
    rw [hlabel]; cases use256 <;> rfl
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨h4,_,_,hroom,halign,_⟩ := frame_facts use256 code fr loc.arguments loc.store hcanonical
  have hR : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - (if use256 then 120 else 104) := by rw [h4]; rfl
  have hCp : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 - 8 = callPointer use256 fr := by
    rw [hR]; exact (stack_addresses use256 fr).1
  have hStack : Writable code loc.store ((loc.arguments[4]'(by change 4 < 53; decide)).get 64 - 8) (if use256 then 32 else 24) := by
    rw [hCp]
    change Writable code loc.store (fr.rsp - BitVec.ofNat 64 (if use256 then 128 else 112)) _
    apply hwork.writable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide
  have hBuf : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 + (if use256 then 8 else 0) =
      buffer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).2.1
  obtain ⟨ca,cont,hCall,hCaLabel,hCont,hCa4,hCa7,hCa6,hCaPres,hCaTyped,hCaWords,hCaRet,hCaWrite⟩ :=
    key1_sbox_call_runBlock use256 code hcode loc.arguments loc.store planes hwork.typed hStack
      (by rw [hBuf]; exact hWords)
  rw [hCont] at hCall
  have hCallActual : LIR.program.runBlock (dialect code) loc = .call ca
      {target := (if use256 then .l106ab8 else .l105243), kept := #v[], arity := rfl,
        guard := some ⟨64,if use256 then 0x106ab8 else 0x105243⟩} := by
    rcases loc with ⟨lab,args,mem⟩
    change lab = _ at hlabel
    subst lab
    exact hCall
  rw [hCp] at hCa4 hCaRet hCaWrite
  rw [hBuf] at hCa7 hCaWords
  have hNative := native_of_span hCaWrite (Nat.le_refl _)
    (show (callPointer use256 fr).toNat + 8 ≤
      (callPointer use256 fr).toNat + (if use256 then 56 else 48) by cases use256 <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega)
  obtain ⟨next,hreach,hw,hl,hm,hs,hr⟩ := call_advance use256 0 code hcode
    key fr loc ca (if use256 then .l106ab8 else .l105243)
    (if use256 then 0x106ab8 else 0x105243)
    hwork hbefore (by cases use256 <;> rfl) hsep hCallActual hCaLabel hCaTyped hCa4 hCa7
    (by intro _; exact hCa6)
    (by intro r hr; exact hCaPres r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega))
    hCaRet (by cases use256 <;> decide) hNative planes hCaWords
  refine ⟨next,hreach,hw,hl,?_,(hr 12 (by decide)).trans (hCaPres 12 (by decide)),
    (hr 14 (by decide)).trans ((hCaPres 14 (by decide)).trans hbuffer)⟩
  exact hm

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
