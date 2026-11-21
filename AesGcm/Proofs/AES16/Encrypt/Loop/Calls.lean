import AesGcm.Proofs.AES16.Encrypt.Loop.Frame
import AesGcm.Proofs.AES16.Sbox
import AesGcm.Proofs.AES16.MixColumnsAlgebra
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

def helperLabel (kind : Fin 3) : LIR.Label :=
  if kind = 0 then .l100b10 else if kind = 1 then .l100000 else .l100580

def helperFrame (kind : Fin 3) : FrameInfo :=
  if kind = 0 then LIR.Fn100b10.frameInfo
  else if kind = 1 then LIR.Fn100000.frameInfo else LIR.Fn100580.frameInfo

def helperTransform (kind : Fin 3) : Planes16 → Planes16 :=
  if kind = 0 then subBytes else if kind = 1 then mixColumns1 else mixColumns3

theorem helper_contract (kind : Fin 3) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (planes : Planes16) :
    CallContract LIR.lifted code (helperLabel kind) (helperFrame kind)
      (fun fr ↦ [span fr.rdi 16])
      (fun fr mem ↦ WordsAt mem fr.rdi 16 (Vector.ofFn planes) ∧ (kind = 0 → fr.rsi = 8) ∧
        Writable code mem fr.rdi 16 ∧ (callStack fr).Disjoint (span fr.rdi 16))
      (fun fr mem ↦ WordsAt mem fr.rdi 16 (Vector.ofFn (helperTransform kind planes))) := by
  intro fr loc hl hs hf ht hp
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · obtain ⟨out, he, htag, hd, hty, hw, hpost⟩ :=
      subBytes_callContract code hcode fr loc hl hs hf ht ⟨hp.2.1 rfl,hp.2.2⟩
    refine ⟨out,he,htag,hd,hty,hw,?_⟩
    have hplanes : (fun p : Fin 8 ↦
        memLoad fr.original (fr.rdi + BitVec.ofNat 64 (2 * p.val)) 16) = planes := by
      funext p
      simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn, hs] using hp.1 p.val p.isLt
    simpa only [helperTransform, Fin.reduceEq, ↓reduceIte, hplanes] using hpost
  · obtain ⟨out, he, htag, hd, hty, hw, hpost⟩ :=
      mixColumns1_call code hcode planes fr loc hl hs hf ht ⟨hp.1,hp.2.2⟩
    refine ⟨out,he,htag,hd,hty,hw,?_⟩
    simpa only [helperTransform, Fin.reduceEq, ↓reduceIte, projectPlanes_mixColumns1, projectPlanes_widenPlanes] using hpost
  · obtain ⟨out, he, htag, hd, hty, hw, hpost⟩ :=
      mixColumns3_call code hcode planes fr loc hl hs hf ht ⟨hp.1,hp.2.2⟩
    refine ⟨out,he,htag,hd,hty,hw,?_⟩
    simpa only [helperTransform, Fin.reduceEq, ↓reduceIte, projectPlanes_mixColumns3, projectPlanes_widenPlanes] using hpost

theorem helper_window (kind : Fin 3) : (helperFrame kind).window ≤ 240 := by
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> decide

theorem helper_done (kind : Fin 3) (fr : Activation) :
    (helperFrame kind).doneAtoms fr = LIR.Fn100b10.frameInfo.doneAtoms fr := by
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> rfl

set_option hygiene false in
local macro "execute_helper_proof" u:term "," depth:num "," cp:num "," buf:num ","
    keyslot:num "," win:num "," ro:num : tactic => `(tactic| (
  change before[4] = ⟨64, fr.rsp - $depth⟩ ∧ before[22] = ⟨1, 0⟩ ∧
    before[3] = ⟨64, fr.rsi⟩ ∧ before[39] = ⟨32, fr.mxcsr⟩ ∧
    before[50] = ⟨16, fr.ftw⟩ ∧ before[51] = ⟨16, fr.fcw⟩ ∧
    memLoad mem (fr.rsp - $keyslot) 64 = fr.rsi ∧
    memLoad mem (fr.rsp - 56) 64 = fr.rdi ∧
    memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧
    memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
    memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧
    memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
    memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧
    memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
    Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code mem (fr.rsp - $win) $win ∧
    fr.low.toNat + $win ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
    Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
    Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
    ($ro ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) ∧ True at hframe
  have hframeCopy : Atom.All code before mem
      (frameAt $u (if $u then .l1069f0 else .l105180) fr) := hframe
  rcases hframe with ⟨h4,h22,h3,h39,h50,h51,hkey,hout,hbx,h12,h13,h14,h15,h5,
    hread,hret,hretlow,hstack,hroom,halign,hroread0,hro0,hroread1,hro1,hroapart,-⟩
  change args[4] = ⟨64, fr.rsp - $cp⟩ at hsp
  change args[7] = ⟨64, fr.rsp - $buf⟩ at hbuffer
  have hp := precise_room $u fr hroom
  have hpr : (preciseActivation $u fr).low.toNat + (frameInfo $u).window ≤
      (preciseActivation $u fr).rsp.toNat := Nat.le_of_eq hp
  obtain ⟨hSpLow,hCallSp,hBuf,hReadCall,hWriteCall,hRoom,hAlign,hApart,hWithin,hSlots⟩ :=
    call_geometry $u code mem (preciseActivation $u fr) (helperFrame kind).window
      (helper_window kind) hstack hpr halign
  have hCallSlots : Atom.All code args mem
      ((helperFrame kind).callSlotAtoms (helperFrame kind).callSlots
        (activationOfValues mem args ret (preciseActivation $u fr).low)) := by
    have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · change Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
        Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
        (0x201238 + 240 ≤ ((args[4]).get 64).toNat ∨
          ((args[4]).get 64).toNat ≤ 0x201210) ∧ True
      refine ⟨hroread0,hro0,hroread1,hro1,?_,trivial⟩
      rw [hsp]
      change 0x201238 + 240 ≤ (fr.rsp - $cp).toNat ∨
        (fr.rsp - $cp).toNat ≤ 0x201210
      change (fr.rsp - $cp).toNat = fr.rsp.toNat - $cp at hCallSp
      omega
    · trivial
    · trivial
  have ha39 : args[39] = ⟨32, fr.mxcsr⟩ := (hpres 39 (by decide)).trans h39
  have ha50 : args[50] = ⟨16, fr.ftw⟩ := (hpres 50 (by decide)).trans h50
  have ha51 : args[51] = ⟨16, fr.fcw⟩ := (hpres 51 (by decide)).trans h51
  obtain ⟨out,he,htag,hdone,htyped,hwrite,hwords⟩ := callContract_exec_values
    LIR.lifted code (helperLabel kind) (helperFrame kind) _ _ _
    (helper_contract kind code hcode planes) mem args ret (preciseActivation $u fr).low
    hTypes (by rw [ha39]; rfl) (by rw [ha50]; rfl) (by rw [ha51]; rfl)
    ((hpres 22 (by decide)).trans h22)
    (by rw [hsp]; exact hReadCall) (by rw [hsp]; exact hRet) hRetLow
    (by intro _; rw [hsp]; exact hWriteCall)
    (by rw [hsp]; exact hRoom) (by rw [hsp]; exact hAlign) hCallSlots
    (by
      dsimp only [activationOfValues]
      rw [hbuffer,hsp]
      simp (config := { bitVecOfNat := false }) only [Value.get, BitVec.setWidth_eq]
      refine ⟨hWords,?_,hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide),hApart⟩
      intro hk
      rw [hlen hk]
      rfl)
  rw [helper_done] at hdone
  change out.values[4] = ⟨64, args[4].get 64 + 8⟩ ∧ out.values[22] = ⟨1,0⟩ ∧
    out.values[3] = ⟨64,args[3].get 64⟩ ∧ out.values[5] = ⟨64,args[5].get 64⟩ ∧
    out.values[12] = ⟨64,args[12].get 64⟩ ∧ out.values[13] = ⟨64,args[13].get 64⟩ ∧
    out.values[14] = ⟨64,args[14].get 64⟩ ∧ out.values[15] = ⟨64,args[15].get 64⟩ ∧
    out.values[39] = ⟨32,args[39].get 32⟩ ∧ out.values[50] = ⟨16,args[50].get 16⟩ ∧
    out.values[51] = ⟨16,args[51].get 16⟩ ∧ True at hdone
  rcases hdone with ⟨ho4,ho22,ho3,ho5,ho12,ho13,ho14,ho15,ho39,ho50,ho51,-⟩
  have hoSp : out.values[4] = before[4] := by
    rw [ho4,hsp,h4]
    congr 1
    change fr.rsp - $cp + 8 = fr.rsp - $depth
    bv_omega
  have hSame : ∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15,39,50,51] →
      out.values[r] = args[r] := by
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ho3.trans (hTypes.value 3).symm
    · exact ho5.trans (hTypes.value 5).symm
    · exact ho12.trans (hTypes.value 12).symm
    · exact ho13.trans (hTypes.value 13).symm
    · exact ho14.trans (hTypes.value 14).symm
    · exact ho15.trans (hTypes.value 15).symm
    · change out.values[39] = args[39]
      rw [ho39,ha39]
      rfl
    · change out.values[50] = args[50]
      rw [ho50,ha50]
      rfl
    · change out.values[51] = args[51]
      rw [ho51,ha51]
      rfl
  change RamWriteFrame mem out.store
    [(activationOfValues mem args ret (preciseActivation $u fr).low).region,
      span (activationOfValues mem args ret (preciseActivation $u fr).low).rdi 16] at hwrite
  dsimp only [activationOfValues,Activation.region] at hwrite
  rw [hsp,hbuffer] at hwrite
  change RamWriteFrame mem out.store
    [callRegion $u (preciseActivation $u fr), span (buffer $u fr) 16] at hwrite
  have hSub : RegionsWithin
      [callRegion $u (preciseActivation $u fr),span (buffer $u fr) 16]
      [(preciseActivation $u fr).region] := by
    intro r hr
    apply hWithin r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    exact hr.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  have hWhole : RamWriteFrame mem out.store [fr.region] :=
    (RamWriteFrame.refl mem [fr.region]).trans hwrite (by
      intro r hr
      obtain ⟨rr,hrr,hlo,hhi⟩ := hSub r hr
      obtain ⟨rrr,hrrr,hlo',hhi'⟩ := precise_within $u fr hroom rr hrr
      exact ⟨rrr,hrrr,Nat.le_trans hlo' hlo,Nat.le_trans hhi hhi'⟩)
  have hSlotsTwo (k : Nat) (hk : k ≤ 72) : Outside
      [callRegion $u (preciseActivation $u fr),span (buffer $u fr) 16]
      (fr.rsp - BitVec.ofNat 64 k) 8 := by
    have h := hSlots k hk
    refine ⟨h.1,?_⟩
    intro r hr
    apply h.2 r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    exact hr.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  have hRoTwo (a : BitVec 64) (hlo : 0x201210 ≤ a.toNat)
      (hhi : a.toNat + 8 ≤ 0x201238) : Outside
      [callRegion $u (preciseActivation $u fr),span (buffer $u fr) 16] a 8 := by
    have h := call_slot_outside $u code mem fr hstack hroom halign hroapart a hlo hhi
    refine ⟨h.1,?_⟩
    intro r hr
    apply h.2 r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    exact hr.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  have hFrameOut := frame_preserve $u code fr before out.values mem out.store _
    hframeCopy (by
      rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hSame 3 (by decide)).trans (hpres 3 (by decide))
      · exact hoSp
      · exact ho22.trans h22.symm
      · exact (hSame 39 (by decide)).trans (hpres 39 (by decide))
      · exact (hSame 50 (by decide)).trans (hpres 50 (by decide))
      · exact (hSame 51 (by decide)).trans (hpres 51 (by decide))) hwrite
    (by intro k hk; apply hSlotsTwo; simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hk; omega)
    ⟨hRoTwo _ (by decide) (by decide),hRoTwo _ (by decide) (by decide)⟩
  dsimp only [activationOfValues] at hwords
  rw [hbuffer] at hwords
  exact ⟨out,he,htag,htyped,hWhole,hFrameOut,hwords,hoSp,hSame⟩
  ))

set_option maxHeartbeats 1000000 in
theorem execute_helper (use256 : Bool) (kind : Fin 3) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation)
    (before args : Values Value Reg.count) (mem : Ram) (planes : Planes16) (ret : BitVec 64)
    (hframe : Atom.All code before mem
      (frameAt use256 (if use256 then .l1069f0 else .l105180) fr))
    (hTypes : GPRsTyped args)
    (hsp : args[4] = ⟨64,callPointer use256 fr⟩)
    (hbuffer : args[7] = ⟨64,buffer use256 fr⟩) (hlen : kind = 0 → args[6] = ⟨64,8⟩)
    (hpres : ∀ r : Fin Reg.count, r.val ∈ [3,22,39,50,51] → args[r] = before[r])
    (hRet : memLoad mem (callPointer use256 fr) 64 = ret) (hRetLow : ret.toNat < 2^32)
    (hWords : WordsAt mem (buffer use256 fr) 16 (Vector.ofFn planes)) :
    ∃ out : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨⟨helperLabel kind,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ GPRsTyped out.values ∧
      RamWriteFrame mem out.store [fr.region] ∧
      Atom.All code out.values out.store
        (frameAt use256 (if use256 then .l1069f0 else .l105180) fr) ∧
      WordsAt out.store (buffer use256 fr) 16 (Vector.ofFn (helperTransform kind planes)) ∧
      out.values[4] = before[4] ∧
      (∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15,39,50,51] → out.values[r] = args[r]) := by
  cases use256
  · execute_helper_proof false, 104,112,104,64,352,0x201398
  · execute_helper_proof true, 120,128,112,72,368,0x2013a8

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
