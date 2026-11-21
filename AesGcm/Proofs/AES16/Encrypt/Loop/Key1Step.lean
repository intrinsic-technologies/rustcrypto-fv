import AesGcm.Proofs.AES16.Encrypt.Loop.Progress
import AesGcm.Proofs.AES16.Encrypt.Loop.Algebra
import AesGcm.Proofs.AES16.Encrypt.Loop.Key1

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option maxHeartbeats 600000 in
theorem key1_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (j : Nat) (hNr : 4*j+1 < (variant use256).Nr)
    (hbound : j ≤ (if use256 then 3 else 2)) (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hwork : WorkingState code use256 key fr loc)
    (hlabel : loc.label = (if use256 then .l106a19 else .l1051a8))
    (hindex : loc.arguments[12]'(by change 12 < 53; decide) =
      ⟨64,BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))⟩)
    (hWords : WordsAt loc.store (buffer use256 fr) 16
      (Vector.ofFn (mixColumns1 (subBytes (roundState (variant use256) key input (4*j)))))) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧
      next.label = (if j = (if use256 then 3 else 2) then (if use256 then .l106ebc else .l105636)
        else (if use256 then .l106aa9 else .l105236)) ∧
      WordsAt next.store (buffer use256 fr) 16
        (Vector.ofFn (roundState (variant use256) key input (4*j+1))) ∧
      (∀ p : Fin 8, ((next.arguments[(planeReg p).val]'(planeReg p).isLt).get 64).setWidth 16 =
        roundState (variant use256) key input (4*j+1) p) ∧
      next.arguments[12]'(by change 12 < 53; decide) = loc.arguments[12]'(by change 12 < 53; decide) ∧
      next.arguments[14]'(by change 14 < 53; decide) = loc.arguments[14]'(by change 14 < 53; decide) := by
  dsimp only [LIR.lifted] at *
  have hbefore : frameAt use256 loc.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr := by
    rw [hlabel]; cases use256 <;> rfl
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨h4,h3,_,hroom,halign,_⟩ := frame_facts use256 code fr loc.arguments loc.store hcanonical
  have hBase : (loc.arguments[3]'(by change 3 < 53; decide)).get 64 = fr.rsi := by rw [h3]; rfl
  have hR : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 =
      fr.rsp-(if use256 then 120 else 104) := by rw [h4]; rfl
  have hBuf : (loc.arguments[4]'(by change 4 < 53; decide)).get 64+(if use256 then 8 else 0) =
      buffer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).2.1
  let r : Fin ((variant use256).Nr+1) := ⟨4*j+1,by omega⟩
  have hKeyAddr : (loc.arguments[3]'(by change 3 < 53; decide)).get 64+
      ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 2 else 16) =
      fr.rsi+BitVec.ofNat 64 (16*r.val) := by
    rw [hBase,hindex]
    change fr.rsi+((BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))) <<< 1)+
      (if use256 then 2 else 16) = _
    cases use256
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 0 16 1 0 rfl
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 7 2 1 0 rfl
  have hKeyRead : Readable loc.store
      ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
        ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 2 else 16)) 16 := by
    rw [hKeyAddr]
    exact roundKey_read hwork.readable r
  have hKeys : WordsAt loc.store
      ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
        ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 2 else 16)) 16
      (Vector.ofFn (expectedKey (variant use256) key r)) := by
    rw [hKeyAddr]
    exact hwork.schedule.words r
  have hStack : Writable code loc.store ((loc.arguments[4]'(by change 4 < 53; decide)).get 64)
      (if use256 then 24 else 16) := by
    rw [hR]
    apply hwork.writable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide
  obtain ⟨hSpLow,hCallNat,hBufNat,_,_,_,_,_,_,_⟩ :=
    call_geometry use256 code loc.store fr 0 (by decide) hwork.writable hroom halign
  have hRspNat : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat =
      fr.rsp.toNat-(if use256 then 120 else 104) := by
    rw [hR]
    rw [window_eq] at hroom
    cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals bv_omega
  have hApart : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat+
        (if use256 then 24 else 16) ≤
        ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
          ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 2 else 16)).toNat ∨
      ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
        ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 2 else 16)).toNat+16 ≤
        ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat := by
    rw [hKeyAddr]
    apply key_apart hwork.readable hsep (by omega) r _ _
    all_goals rw [hRspNat]
    all_goals rw [window_eq] at hroom
    all_goals cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals omega
  obtain ⟨next,hRun,hLabel,hPres,hTyped,hNextWords,hRegs,hWrite⟩ := key1_runBlock use256 code hcode
    loc.arguments loc.store (mixColumns1 (subBytes (roundState (variant use256) key input (4*j))))
    (expectedKey (variant use256) key r) hwork.typed hStack hKeyRead hApart
    (by rw [hBuf]; exact hWords) hKeys
  have hRunActual : LIR.program.runBlock (dialect code) loc = .jump next := by
    rcases loc with ⟨lab,args,mem⟩
    change lab = _ at hlabel
    subst lab
    exact hRun
  rw [hBuf] at hNextWords hWrite
  have hIndexStop : (loc.arguments[12]'(by change 12 < 53; decide)).get 64 =
      (if use256 then 103 else 64) ↔ j = (if use256 then 3 else 2) := by
    rw [hindex]
    cases use256
    · exact index_eq_of_bound j 2 0 hbound (by decide)
    · exact index_eq_of_bound j 3 7 hbound (by decide)
  simp only [hIndexStop] at hLabel
  have hRound : xorPlanes
      (mixColumns1 (subBytes (roundState (variant use256) key input (4*j))))
      (expectedKey (variant use256) key r) = roundState (variant use256) key input (4*j+1) := by
    simpa only [roundMix,Nat.reduceAdd,Nat.reduceMod,Nat.add_zero] using
      roundState_add (variant use256) key input j 0 hNr
  rw [hRound] at hNextWords hRegs
  have hNative : RamWriteFrame loc.store next.store (nativeRegions use256 fr) := by
    apply native_of_span hWrite
    all_goals rw [hBufNat,hCallNat]
    all_goals rw [window_eq] at hroom
    all_goals cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals omega
  obtain ⟨hReach,hWorkNext⟩ := jump_advance use256 code key fr loc next hwork hbefore
    (by
      by_cases hx : j = (if use256 then 3 else 2)
      · have hl : next.label = (if use256 then .l106ebc else .l105636) := by
          simpa only [hx,ite_true] using hLabel
        rw [hl]
        cases use256 <;> rfl
      · have hl : next.label = (if use256 then .l106aa9 else .l105236) := by
          simpa only [hx,ite_false] using hLabel
        rw [hl]
        cases use256 <;> rfl) hsep hRunActual hTyped hNative
    (by
      intro rr hin
      exact hPres rr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢; omega))
  exact ⟨next,hReach,hWorkNext,hLabel,hNextWords,hRegs,hPres 12 (by decide),hPres 14 (by decide)⟩

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
