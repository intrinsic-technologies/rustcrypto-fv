import AesGcm.Proofs.AES16.Encrypt.Loop.Progress
import AesGcm.Proofs.AES16.Encrypt.Loop.Algebra
import AesGcm.Proofs.AES16.Encrypt.Inline2

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option maxHeartbeats 600000 in
theorem inline2_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (j : Nat) (hNr : 4*j+2 < (variant use256).Nr)
    (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hwork : WorkingState code use256 key fr loc)
    (hlabel : loc.label = (if use256 then .l106ab8 else .l105243))
    (hindex : loc.arguments[12]'(by change 12 < 53; decide) =
      ⟨64,BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))⟩)
    (hWords : WordsAt loc.store (buffer use256 fr) 16
      (Vector.ofFn (subBytes (roundState (variant use256) key input (4*j+1))))) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧
      next.label = (if use256 then .l106ce3 else .l10546a) ∧
      WordsAt next.store (buffer use256 fr) 16
        (Vector.ofFn (subBytes (roundState (variant use256) key input (4*j+2)))) ∧
      next.arguments[12]'(by change 12 < 53; decide) = loc.arguments[12]'(by change 12 < 53; decide) ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64,buffer use256 fr⟩ := by
  dsimp only [LIR.lifted] at *
  have hbefore : frameAt use256 loc.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr := by
    rw [hlabel]; cases use256 <;> rfl
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨h4,h3,hslot,hroom,halign,_⟩ := frame_facts use256 code fr loc.arguments loc.store hcanonical
  have hR : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 =
      fr.rsp-(if use256 then 120 else 104) := by rw [h4]; rfl
  have hBuf : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 + (if use256 then 8 else 0) =
      buffer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).2.1
  have hCp : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 - 8 =
      callPointer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).1
  have hSlot : memLoad loc.store
      ((loc.arguments[4]'(by change 4 < 53; decide)).get 64+(if use256 then 48 else 40)) 64 = fr.rsi := by
    rw [hR,(stack_addresses use256 fr).2.2]
    exact hslot
  let r : Fin ((variant use256).Nr+1) := ⟨4*j+2,by omega⟩
  have hKeyAddr : fr.rsi + ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1) +
      (if use256 then 18 else 32) = fr.rsi+BitVec.ofNat 64 (16*r.val) := by
    rw [hindex]
    change fr.rsi+((BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))) <<< 1)+
      (if use256 then 18 else 32) = _
    cases use256
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 0 32 2 0 rfl
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 7 18 2 0 rfl
  have hKeyRead : Readable loc.store
      (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 18 else 32)) 16 := by
    rw [hKeyAddr]
    exact roundKey_read hwork.readable r
  have hKeys : WordsAt loc.store
      (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 18 else 32)) 16
      (Vector.ofFn (expectedKey (variant use256) key r)) := by
    rw [hKeyAddr]
    exact hwork.schedule.words r
  have hStack : Writable code loc.store ((loc.arguments[4]'(by change 4 < 53; decide)).get 64-8)
      (if use256 then 64 else 56) := by
    rw [hCp]
    change Writable code loc.store (fr.rsp-BitVec.ofNat 64 (if use256 then 128 else 112)) _
    apply hwork.writable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide
  obtain ⟨hSpLow,hCallNat,hBufNat,_,_,hCallLow,_,_,_,_⟩ :=
    call_geometry use256 code loc.store fr 0 (by decide) hwork.writable hroom halign
  have hRspNat : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat =
      (callPointer use256 fr).toNat+8 := by
    rw [hR,hCallNat]
    rw [window_eq] at hroom
    cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals bv_omega
  have hEnd : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat+
      (if use256 then 48 else 40) =
      (callPointer use256 fr).toNat+(if use256 then 56 else 48) := by
    rw [hRspNat]
    cases use256 <;> rfl
  have hApart : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat+
        (if use256 then 48 else 40) ≤
        (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 18 else 32)).toNat ∨
      (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 18 else 32)).toNat+16 ≤
        ((loc.arguments[4]'(by change 4 < 53; decide)).get 64-8).toNat := by
    rw [hEnd,hKeyAddr,hCp]
    apply key_apart hwork.readable hsep (by omega) r _ _ (by simpa only [Nat.add_zero] using hCallLow)
    rw [hCallNat]
    rw [window_eq] at hroom
    cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals omega
  obtain ⟨ca,cont,hCall,hCaLabel,hCont,hCa4,hCa7,hCa6,hCa3,hCa12,hCa14,
      hCa22,hCa39,hCa50,hCa51,hCaTyped,hCaWords,hCaRet,hCaWrite⟩ :=
    inline_mixColumns2 use256 code hcode loc.arguments loc.store
      (subBytes (roundState (variant use256) key input (4*j+1)))
      (expectedKey (variant use256) key r) fr.rsi hwork.typed hStack hSlot hKeyRead hApart
      (by rw [hBuf]; exact hWords) hKeys
  rw [hCont] at hCall
  have hCallActual : LIR.program.runBlock (dialect code) loc = .call ca
      {target := (if use256 then .l106ce3 else .l10546a), kept := #v[], arity := rfl,
        guard := some ⟨64,if use256 then 0x106ce3 else 0x10546a⟩} := by
    rcases loc with ⟨lab,args,mem⟩
    change lab = _ at hlabel
    subst lab
    exact hCall
  rw [hBuf] at hCaWords hCa7 hCa14
  rw [hCp] at hCa4 hCaRet hCaWrite
  have hRound : xorPlanes
      (mixColumns2 (subBytes (roundState (variant use256) key input (4*j+1))))
      (expectedKey (variant use256) key r) = roundState (variant use256) key input (4*j+2) := by
    simpa only [roundMix,Nat.reduceAdd,Nat.reduceMod] using
      roundState_add (variant use256) key input j 1 hNr
  rw [hRound] at hCaWords
  have hNative := native_of_span hCaWrite (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨next,hreach,hw,hl,hm,hs,hr⟩ := call_advance use256 0 code hcode key fr loc ca
    (if use256 then .l106ce3 else .l10546a) (if use256 then 0x106ce3 else 0x10546a)
    hwork hbefore (by cases use256 <;> rfl) hsep hCallActual hCaLabel hCaTyped hCa4 hCa7
    (by intro _; exact hCa6)
    (by
      rintro ⟨rr,hrr⟩ hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl
      · exact hCa3.trans h3.symm
      · exact hCa22
      · exact hCa39
      · exact hCa50
      · exact hCa51)
    hCaRet (by cases use256 <;> decide) hNative
    (roundState (variant use256) key input (4*j+2)) hCaWords
  exact ⟨next,hreach,hw,hl,hm,(hr 12 (by decide)).trans hCa12,(hr 14 (by decide)).trans hCa14⟩

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
