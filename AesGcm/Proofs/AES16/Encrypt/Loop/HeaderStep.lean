import AesGcm.Proofs.AES16.Encrypt.Loop.Progress
import AesGcm.Proofs.AES16.Encrypt.Loop.Header
import AesGcm.Proofs.AES16.Encrypt.Loop.Algebra

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option maxHeartbeats 600000 in
theorem header_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (j : Nat) (hj : 4*j < (variant use256).Nr+1)
    (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16*((variant use256).Nr+1))))
    (hwork : WorkingState code use256 key fr loc)
    (hloop : LoopState use256 key input fr j hj loc) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc,[]⟩ ⟨next,[]⟩ ∧
      WorkingState code use256 key fr next ∧
      next.label = (if use256 then .l106a11 else .l1051a0) ∧
      WordsAt next.store (buffer use256 fr) 16
        (Vector.ofFn (subBytes (roundState (variant use256) key input (4*j)))) ∧
      next.arguments[12]'(by change 12 < 53; decide) = loc.arguments[12]'(by change 12 < 53; decide) ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64,buffer use256 fr⟩ := by
  dsimp only [LIR.lifted] at *
  have hbefore : frameAt use256 loc.label fr =
      frameAt use256 (if use256 then .l1069f0 else .l105180) fr := by rw [hloop.label]; rfl
  have hcanonical := hwork.frame
  rw [hbefore] at hcanonical
  obtain ⟨h4,h3,hslot,hroom,halign,_⟩ := frame_facts use256 code fr loc.arguments loc.store hcanonical
  have hR : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 =
      fr.rsp - (if use256 then 120 else 104) := by rw [h4]; rfl
  have hBuf : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 + (if use256 then 8 else 0) =
      buffer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).2.1
  have hCp : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 - 8 =
      callPointer use256 fr := by rw [hR]; exact (stack_addresses use256 fr).1
  have hSlot : memLoad loc.store
      ((loc.arguments[4]'(by change 4 < 53; decide)).get 64 + (if use256 then 48 else 40)) 64 = fr.rsi := by
    rw [hR,(stack_addresses use256 fr).2.2]
    exact hslot
  have hKeyAddr : fr.rsi + ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1) + (if use256 then 0 else 14) =
      fr.rsi + BitVec.ofNat 64 (16*(4*j)+14) := by
    rw [hloop.index]
    change fr.rsi + ((BitVec.ofNat 64 (32*j+(if use256 then 7 else 0))) <<< 1) +
      (if use256 then 0 else 14) = _
    cases use256
    · simpa only [Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat] using key_address fr.rsi j 0 14 0 7 rfl
    · simpa only [Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.reduceMul,BitVec.ofNat_eq_ofNat] using key_address fr.rsi j 7 0 0 7 rfl
  have hKeyRead : Readable loc.store
      (fr.rsi + ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1) + (if use256 then 0 else 14)) 2 := by
    rw [hKeyAddr]
    apply hwork.readable.of_offsets rfl (addr_self _)
    simp only [sub_zero_lit,BitVec.toNat_ofNat]
    have hm := Nat.mod_le (16*(4*j)+14) (2^64)
    omega
  have hKey : memLoad loc.store
      (fr.rsi + ((loc.arguments[12]'(by change 12 < 53; decide)).get 64 <<< 1) + (if use256 then 0 else 14)) 16 =
      expectedKey (variant use256) key ⟨4*j,hj⟩ 7 := by
    rw [hKeyAddr]
    exact hwork.schedule ⟨4*j,hj⟩ 7
  have hStack : Writable code loc.store ((loc.arguments[4]'(by change 4 < 53; decide)).get 64-8) (if use256 then 64 else 56) := by
    rw [hCp]
    change Writable code loc.store (fr.rsp - BitVec.ofNat 64 (if use256 then 128 else 112)) _
    apply hwork.writable.of_offsets
      (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide
  obtain ⟨ca,cont,hCall,hCaLabel,hCont,hCa4,hCa7,hCa6,hCa3,hCa12,hCa14,
      hCaPres,hCaTyped,hCaWords,hCaRet,hCaWrite⟩ := header_runBlock use256 code hcode
    loc.arguments loc.store fr.rsi
    (delayedPlanes (roundState (variant use256) key input (4*j))
      (expectedKey (variant use256) key ⟨4*j,hj⟩))
    (expectedKey (variant use256) key ⟨4*j,hj⟩ 7) hwork.typed hStack hSlot hKeyRead hKey hloop.tail
    (by rw [hBuf]; exact hloop.words)
  rw [hCont] at hCall
  have hCallActual : LIR.program.runBlock (dialect code) loc = .call ca
      {target := (if use256 then .l106a11 else .l1051a0), kept := #v[], arity := rfl,
        guard := some ⟨64,if use256 then 0x106a11 else 0x1051a0⟩} := by
    rcases loc with ⟨lab,args,mem⟩
    have hLab := hloop.label
    change lab = (if use256 then .l1069f0 else .l105180) at hLab
    subst lab
    exact hCall
  rw [hBuf,restore_delayed] at hCaWords
  rw [hCp] at hCa4 hCaRet hCaWrite
  rw [hBuf] at hCa7 hCa14
  have hNative : RamWriteFrame loc.store ca.store (nativeRegions use256 fr) := by
    apply native_of_span hCaWrite (Nat.le_refl _)
    have hn : (if use256 then 32 else 24) ≤ (if use256 then 56 else 48) := by
      cases use256 <;> decide
    omega
  obtain ⟨next,hreach,hw,hl,hm,hs,hr⟩ := call_advance use256 0 code hcode key fr loc ca
    (if use256 then .l106a11 else .l1051a0) (if use256 then 0x106a11 else 0x1051a0)
    hwork hbefore (by cases use256 <;> rfl) hsep hCallActual hCaLabel hCaTyped
    hCa4 hCa7 (by intro _; exact hCa6)
    (by
      rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl
      · exact hCa3.trans h3.symm
      · exact hCaPres 22 (by decide)
      · exact hCaPres 39 (by decide)
      · exact hCaPres 50 (by decide)
      · exact hCaPres 51 (by decide))
    hCaRet (by cases use256 <;> decide) hNative
    (roundState (variant use256) key input (4*j)) hCaWords
  exact ⟨next,hreach,hw,hl,hm,(hr 12 (by decide)).trans hCa12,
    (hr 14 (by decide)).trans hCa14⟩

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
