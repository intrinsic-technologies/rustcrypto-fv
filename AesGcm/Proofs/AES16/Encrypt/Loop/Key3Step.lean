import AesGcm.Proofs.AES16.Encrypt.Loop.Progress
import AesGcm.Proofs.AES16.Encrypt.Loop.Algebra
import AesGcm.Proofs.AES16.Encrypt.Loop.Key3

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option maxHeartbeats 600000 in
theorem key3_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (j : Nat) (hNr : 4*j+3 < (variant use256).Nr)
    (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hwork : WorkingState code use256 key fr loc)
    (hlabel : loc.label = (if use256 then .l106ceb else .l105472))
    (hindex : loc.arguments[12]'(by change 12 < 53; decide) =
      ⟨64,BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))⟩)
    (hWords : WordsAt loc.store (buffer use256 fr) 16
      (Vector.ofFn (mixColumns3 (subBytes (roundState (variant use256) key input (4*j+2))))))
    (hbuffer : loc.arguments[14]'(by change 14 < 53; decide) = ⟨64,buffer use256 fr⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧
      next.label = (if use256 then .l106d50 else .l1054d6) ∧
      WordsAt next.store (buffer use256 fr) 16
        (Vector.ofFn (subBytes (roundState (variant use256) key input (4*j+3)))) ∧
      next.arguments[12]'(by change 12 < 53; decide) = loc.arguments[12]'(by change 12 < 53; decide) ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64,buffer use256 fr⟩ := by
  dsimp only [LIR.lifted] at *
  have hbefore : frameAt use256 loc.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr := by
    rw [hlabel]; cases use256 <;> rfl
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨h4,h3,hslot,hroom,halign,_⟩ := frame_facts use256 code fr loc.arguments loc.store hcanonical
  have hBase : (loc.arguments[3]'(by change 3 < 53; decide)).get 64 = fr.rsi := by
    rw [h3]; rfl
  have hR : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 =
      fr.rsp-(if use256 then 120 else 104) := by rw [h4]; rfl
  have hBuf : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 + (if use256 then 8 else 0) =
      buffer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).2.1
  have hCp : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 - 8 =
      callPointer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).1
  let r : Fin ((variant use256).Nr+1) := ⟨4*j+3,by omega⟩
  have hKeyAddr : fr.rsi + ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1) +
      (if use256 then 34 else 48) = fr.rsi+BitVec.ofNat 64 (16*r.val) := by
    rw [hindex]
    change fr.rsi+((BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))) <<< 1)+
      (if use256 then 34 else 48) = _
    cases use256
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 0 48 3 0 rfl
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 7 34 3 0 rfl
  have hKeyRead : Readable loc.store
      (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 34 else 48)) 16 := by
    rw [hKeyAddr]
    exact roundKey_read hwork.readable r
  have hKeys : WordsAt loc.store
      (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 34 else 48)) 16
      (Vector.ofFn (expectedKey (variant use256) key r)) := by
    rw [hKeyAddr]
    exact hwork.schedule.words r
  have hStack : Writable code loc.store ((loc.arguments[4]'(by change 4 < 53; decide)).get 64-8)
      (if use256 then 32 else 24) := by
    rw [hCp]
    change Writable code loc.store (fr.rsp-BitVec.ofNat 64 (if use256 then 128 else 112)) _
    apply hwork.writable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide
  obtain ⟨hSpLow,hCallNat,hBufNat,_,_,hCallLow,_,_,_,_⟩ :=
    call_geometry use256 code loc.store fr 0 (by decide) hwork.writable hroom halign
  have hApart : (callPointer use256 fr).toNat+(if use256 then 32 else 24) ≤
        (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 34 else 48)).toNat ∨
      (fr.rsi+((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 34 else 48)).toNat+16 ≤
        (callPointer use256 fr).toNat := by
    rw [hKeyAddr]
    apply key_apart hwork.readable hsep (by omega) r _ _ (by simpa only [Nat.add_zero] using hCallLow)
    rw [hCallNat]
    rw [window_eq] at hroom
    cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals omega
  obtain ⟨ca,cont,hCall,hCaLabel,hCont,hCa4,hCa7,hCa6,hCaPres,hCaTyped,
      hCaWords,hCaRet,hCaWrite⟩ := key3_runBlock use256 code hcode loc.arguments loc.store
      (mixColumns3 (subBytes (roundState (variant use256) key input (4*j+2))))
      (expectedKey (variant use256) key r) hwork.typed hStack
      (by simpa only [hBase] using hKeyRead)
      (by rw [hCp]; simpa only [hBase] using hApart)
      (by rw [hbuffer,hBuf]; rfl)
      (by rw [hBuf]; exact hWords)
      (by simpa only [hBase] using hKeys)
  rw [hCont] at hCall
  have hCallActual : LIR.program.runBlock (dialect code) loc = .call ca
      {target := (if use256 then .l106d50 else .l1054d6), kept := #v[], arity := rfl,
        guard := some ⟨64,if use256 then 0x106d50 else 0x1054d6⟩} := by
    rcases loc with ⟨lab,args,mem⟩
    change lab = _ at hlabel
    subst lab
    exact hCall
  rw [hBuf] at hCaWords hCa7
  rw [hCp] at hCa4 hCaRet hCaWrite
  have hRound : xorPlanes
      (mixColumns3 (subBytes (roundState (variant use256) key input (4*j+2))))
      (expectedKey (variant use256) key r) = roundState (variant use256) key input (4*j+3) := by
    simpa only [roundMix,Nat.reduceAdd,Nat.reduceMod] using
      roundState_add (variant use256) key input j 2 hNr
  rw [hRound] at hCaWords
  have hNative := native_of_span hCaWrite (Nat.le_refl _)
    (show (callPointer use256 fr).toNat+(if use256 then 32 else 24) ≤
      (callPointer use256 fr).toNat+(if use256 then 56 else 48) by
      cases use256 <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega)
  obtain ⟨next,hreach,hw,hl,hm,hs,hr⟩ := call_advance use256 0 code hcode key fr loc ca
    (if use256 then .l106d50 else .l1054d6) (if use256 then 0x106d50 else 0x1054d6)
    hwork hbefore (by cases use256 <;> rfl) hsep hCallActual hCaLabel hCaTyped hCa4 hCa7
    (by intro _; exact hCa6)
    (by
      intro rr hin
      exact hCaPres rr (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢
        omega))
    hCaRet (by cases use256 <;> decide) hNative
    (roundState (variant use256) key input (4*j+3)) hCaWords
  exact ⟨next,hreach,hw,hl,hm,(hr 12 (by decide)).trans (hCaPres 12 (by decide)),
    (hr 14 (by decide)).trans ((hCaPres 14 (by decide)).trans hbuffer)⟩

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
