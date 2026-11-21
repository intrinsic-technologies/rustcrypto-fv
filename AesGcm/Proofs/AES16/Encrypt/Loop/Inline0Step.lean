import AesGcm.Proofs.AES16.Encrypt.Loop.Progress
import AesGcm.Proofs.AES16.Encrypt.Loop.Algebra
import AesGcm.Proofs.AES16.Encrypt.Inline0

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option maxHeartbeats 800000 in
theorem inline0_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (j : Nat) (hNr : 4*j+4 < (variant use256).Nr)
    (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hwork : WorkingState code use256 key fr loc)
    (hlabel : loc.label = (if use256 then .l106d50 else .l1054d6))
    (hindex : loc.arguments[12]'(by change 12 < 53; decide) =
      ⟨64,BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))⟩)
    (hWords : WordsAt loc.store (buffer use256 fr) 16
      (Vector.ofFn (subBytes (roundState (variant use256) key input (4*j+3))))) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧
      ∃ hnext : 4*(j+1) < (variant use256).Nr+1,
        LoopState use256 key input fr (j+1) hnext next := by
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
  have hBuf : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 + (if use256 then 8 else 0) =
      buffer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).2.1
  let r : Fin ((variant use256).Nr+1) := ⟨4*j+4,by omega⟩
  have hKeyAddr : (loc.arguments[3]'(by change 3 < 53; decide)).get 64 +
      ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 50 else 64) =
      fr.rsi+BitVec.ofNat 64 (16*r.val) := by
    rw [hBase,hindex]
    change fr.rsi+((BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))) <<< 1)+
      (if use256 then 50 else 64) = _
    cases use256
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 0 64 4 0 rfl
    · simpa only [r,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        using key_address fr.rsi j 7 50 4 0 rfl
  have hKeyRead : Readable loc.store
      ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
        ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 50 else 64)) 16 := by
    rw [hKeyAddr]
    exact roundKey_read hwork.readable r
  have hKeys : WordsAt loc.store
      ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
        ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 50 else 64)) 16
      (Vector.ofFn (expectedKey (variant use256) key r)) := by
    rw [hKeyAddr]
    exact hwork.schedule.words r
  have hStack : Writable code loc.store ((loc.arguments[4]'(by change 4 < 53; decide)).get 64)
      (if use256 then 64 else 40) := by
    rw [hR]
    apply hwork.writable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide
  obtain ⟨hSpLow,hCallNat,_,_,_,_,_,_,_,_⟩ :=
    call_geometry use256 code loc.store fr 0 (by decide) hwork.writable hroom halign
  have hRspNat : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat =
      fr.rsp.toNat-(if use256 then 120 else 104) := by
    rw [hR]
    rw [window_eq] at hroom
    cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals bv_omega
  have hApart : ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat+
        (if use256 then 64 else 40) ≤
        ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
          ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 50 else 64)).toNat ∨
      ((loc.arguments[3]'(by change 3 < 53; decide)).get 64+
        ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1)+(if use256 then 50 else 64)).toNat+16 ≤
        ((loc.arguments[4]'(by change 4 < 53; decide)).get 64).toNat := by
    rw [hKeyAddr]
    apply key_apart hwork.readable hsep (by omega) r _ _
    all_goals rw [hRspNat]
    all_goals rw [window_eq] at hroom
    all_goals cases use256
    all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
    all_goals omega
  obtain ⟨next,hRun,hLabel,hNext4,hNext3,hNext12,hTail,hNext22,hNext39,hNext50,hNext51,
      hTyped,hNextWords,hWrite⟩ := inline_mixColumns0 use256 code hcode loc.arguments loc.store
    (subBytes (roundState (variant use256) key input (4*j+3)))
    (expectedKey (variant use256) key r) hwork.typed hStack hKeyRead hApart
    (by rw [hBuf]; exact hWords) hKeys
  have hRunActual : LIR.program.runBlock (dialect code) loc = .jump next := by
    rcases loc with ⟨lab,args,mem⟩
    change lab = _ at hlabel
    subst lab
    exact hRun
  rw [hBuf] at hNextWords
  have hNative : RamWriteFrame loc.store next.store (nativeRegions use256 fr) := by
    apply (RamWriteFrame.refl loc.store (nativeRegions use256 fr)).trans hWrite
    intro reg hreg
    cases use256
    · simp only [Bool.false_eq_true,↓reduceIte,List.mem_singleton] at hreg
      subst reg
      refine ⟨span (callPointer false fr) 48,List.mem_cons_self,?_,?_⟩
      all_goals simp only [span]
      all_goals rw [hRspNat,hCallNat]
      all_goals rw [window_eq] at hroom
      all_goals simp only [Bool.false_eq_true,↓reduceIte] at hroom ⊢
      all_goals omega
    · simp only [↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hreg
      rcases hreg with rfl | rfl
      · refine ⟨span (callPointer true fr) 56,List.mem_cons_self,?_,?_⟩
        all_goals simp only [span]
        all_goals rw [hRspNat,hCallNat]
        all_goals rw [window_eq] at hroom
        all_goals simp only [↓reduceIte] at hroom ⊢
        all_goals omega
      · have hspill : (loc.arguments[4]'(by change 4 < 53; decide)).get 64+60 = fr.rsp-60 := by
          rw [hR]
          change fr.rsp-120+60 = fr.rsp-60
          bv_omega
        rw [hspill]
        exact ⟨span (fr.rsp-60) 4,List.mem_cons_of_mem _ List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  obtain ⟨hReach,hWorkNext⟩ := jump_advance use256 code key fr loc next hwork hbefore
    (by rw [hLabel]; rfl) hsep hRunActual hTyped hNative
    (by
      rintro ⟨rr,hrr⟩ hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hNext3
      · exact hNext4
      · exact hNext22
      · exact hNext39
      · exact hNext50
      · exact hNext51)
  have hnext : 4*(j+1) < (variant use256).Nr+1 := by omega
  have hCount : 4*j+4 = 4*(j+1) := by omega
  have hRound : xorPlanes
      (mixColumns0 (subBytes (roundState (variant use256) key input (4*j+3))))
      (expectedKey (variant use256) key r) = roundState (variant use256) key input (4*(j+1)) := by
    simpa only [roundMix,Nat.reduceAdd,Nat.reduceMod,r,hCount] using
      roundState_add (variant use256) key input j 3 hNr
  have hDelayed : delayedPlanes (roundState (variant use256) key input (4*(j+1)))
      (expectedKey (variant use256) key ⟨4*(j+1),hnext⟩) =
      (fun p : Fin 8 ↦ if p.val=7 then
        mixColumns0 (subBytes (roundState (variant use256) key input (4*j+3))) p else
        mixColumns0 (subBytes (roundState (variant use256) key input (4*j+3))) p ^^^
          expectedKey (variant use256) key r p) := by
    rw [← hRound]
    have hr : r = ⟨4*(j+1),hnext⟩ := Fin.ext hCount
    rw [hr]
    exact delay_xor _ _
  refine ⟨next,hReach,hWorkNext,hnext,hLabel,?_,?_,?_⟩
  · rw [hNext12,hindex]
    change (⟨64,BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))+32⟩ : Value) = _
    rw [index_succ]
  · rw [hDelayed]
    exact hNextWords
  · rw [hDelayed]
    change ((next.arguments[0]'(by change 0 < 53; decide)).get 64).setWidth 16 =
      mixColumns0 (subBytes (roundState (variant use256) key input (4*j+3))) 7
    exact hTail

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
