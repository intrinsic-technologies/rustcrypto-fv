import AesGcm.Proofs.AES16.Encrypt.Calls

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option hygiene false in
local macro "preserve_loop_frame" depth:num "," keyslot:num "," win:num "," ro:num : tactic => `(tactic| (
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
  change after[4] = ⟨64, fr.rsp - $depth⟩ ∧ after[22] = ⟨1, 0⟩ ∧
    after[3] = ⟨64, fr.rsi⟩ ∧ after[39] = ⟨32, fr.mxcsr⟩ ∧
    after[50] = ⟨16, fr.ftw⟩ ∧ after[51] = ⟨16, fr.fcw⟩ ∧
    memLoad mem' (fr.rsp - $keyslot) 64 = fr.rsi ∧
    memLoad mem' (fr.rsp - 56) 64 = fr.rdi ∧
    memLoad mem' (fr.rsp - 48) 64 = fr.rbx ∧
    memLoad mem' (fr.rsp - 40) 64 = fr.r12 ∧
    memLoad mem' (fr.rsp - 32) 64 = fr.r13 ∧
    memLoad mem' (fr.rsp - 24) 64 = fr.r14 ∧
    memLoad mem' (fr.rsp - 16) 64 = fr.r15 ∧
    memLoad mem' (fr.rsp - 8) 64 = fr.rbp ∧
    Readable mem' fr.rsp 8 ∧ memLoad mem' fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code mem' (fr.rsp - $win) $win ∧
    fr.low.toNat + $win ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
    Readable mem' 0x201210 8 ∧ memLoad mem' 0x201210 64 = 0x103880 ∧
    Readable mem' 0x201230 8 ∧ memLoad mem' 0x201230 64 = 0x101230 ∧
    ($ro ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) ∧ True
  rcases hframe with ⟨h4,h22,h3,h39,h50,h51,hkey,hout,hbx,h12,h13,h14,h15,h5,
    hread,hret,hretlow,hstack,hroom,halign,hroread0,hro0,hroread1,hro1,hroapart,-⟩
  refine ⟨(hregs 4 (by decide)).trans h4, (hregs 22 (by decide)).trans h22,
    (hregs 3 (by decide)).trans h3, (hregs 39 (by decide)).trans h39,
    (hregs 50 (by decide)).trans h50, (hregs 51 (by decide)).trans h51,
    (hstep.memLoad_eq (hslots $keyslot (by decide))).trans hkey,
    (hstep.memLoad_eq (hslots 56 (by decide))).trans hout,
    (hstep.memLoad_eq (hslots 48 (by decide))).trans hbx,
    (hstep.memLoad_eq (hslots 40 (by decide))).trans h12,
    (hstep.memLoad_eq (hslots 32 (by decide))).trans h13,
    (hstep.memLoad_eq (hslots 24 (by decide))).trans h14,
    (hstep.memLoad_eq (hslots 16 (by decide))).trans h15,
    (hstep.memLoad_eq (hslots 8 (by decide))).trans h5,
    hread.of_frame hstep, ?_, hretlow, hstack.of_frame hstep, hroom, halign,
    hroread0.of_frame hstep, (hstep.memLoad_eq hro.1).trans hro0,
    hroread1.of_frame hstep, (hstep.memLoad_eq hro.2).trans hro1, hroapart, trivial⟩
  have hz := hslots 0 (by decide)
  change Outside regions (fr.rsp - 0) 8 at hz
  simp only [sub_zero_lit] at hz
  exact (hstep.memLoad_eq hz).trans hret
  ))

theorem frame_preserve (use256 : Bool) (code : CodeMap) (fr : Activation)
    (before after : Values Value Reg.count) (mem mem' : Ram) (regions : List MemoryRegion)
    (hframe : Atom.All code before mem (frameAt use256
      (if use256 then .l1069f0 else .l105180) fr))
    (hregs : ∀ r : Fin Reg.count, r.val ∈ [3,4,22,39,50,51] → after[r] = before[r])
    (hstep : RamWriteFrame mem mem' regions)
    (hslots : ∀ k : Nat, k ∈ [0,8,16,24,32,40,48,56,(if use256 then 72 else 64)] → Outside regions (fr.rsp - BitVec.ofNat 64 k) 8)
    (hro : Outside regions 0x201210 8 ∧ Outside regions 0x201230 8) :
    Atom.All code after mem' (frameAt use256
      (if use256 then .l1069f0 else .l105180) fr) := by
  cases use256
  · preserve_loop_frame 104, 64, 352, 0x201398
  · preserve_loop_frame 120, 72, 368, 0x2013a8

def nativeRegions (use256 : Bool) (fr : Activation) : List MemoryRegion :=
  span (callPointer use256 fr) (if use256 then 56 else 48) ::
    (if use256 then [span (fr.rsp - 60) 4] else [])

theorem native_geometry (use256 : Bool) (fr : Activation)
    (hroom : fr.low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat)
    (hsp : fr.rsp.toNat ≤ 2^32)
    (hro : 0x201238 + (frameInfo use256).window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) :
    RegionsWithin (nativeRegions use256 fr) [fr.region] ∧
    (∀ k : Nat, k ∈ [0,8,16,24,32,40,48,56,(if use256 then 72 else 64)] →
      Outside (nativeRegions use256 fr) (fr.rsp - BitVec.ofNat 64 k) 8) ∧
    (Outside (nativeRegions use256 fr) 0x201210 8 ∧
      Outside (nativeRegions use256 fr) 0x201230 8) := by
  have hs (k : Nat) (hk : k ≤ (frameInfo use256).window) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hw : (frameInfo use256).window < 2^64 := by
      rw [window_eq]; cases use256 <;> decide
    have hkle : BitVec.ofNat 64 k ≤ fr.rsp := by
      change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega
    rw [BitVec.toNat_sub_of_le hkle,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hs112 := hs 112 (by rw [window_eq]; cases use256 <;> decide)
  have hs128 := hs 128 (by rw [window_eq]; cases use256 <;> decide)
  have hs60 := hs 60 (by rw [window_eq]; cases use256 <;> decide)
  change (fr.rsp - 60).toNat = fr.rsp.toNat - 60 at hs60
  have hc0 : (0x201210 : BitVec 64).toNat = 0x201210 := by decide +kernel
  have hc1 : (0x201230 : BitVec 64).toNat = 0x201230 := by decide +kernel
  have hwithin : RegionsWithin (nativeRegions use256 fr) [fr.region] := by
    intro r hr
    refine ⟨fr.region,by simp only [List.mem_singleton],?_,?_⟩
    all_goals
      cases use256
      all_goals simp only [nativeRegions,callPointer,span,Activation.region,
        Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      all_goals rcases hr with rfl | rfl
      all_goals first | contradiction | (simp only [hs112,hs128,hs60]; rw [window_eq] at hroom; simp only [Bool.false_eq_true,↓reduceIte] at hroom; omega)
  refine ⟨hwithin,?_,?_,?_⟩
  · intro k hk
    have hk72 : k ≤ 72 := by
      cases use256
      all_goals simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hk
      all_goals omega
    have hslot := hs k (by rw [window_eq]; split <;> omega)
    refine ⟨by rw [hslot]; omega,?_⟩
    intro r hr
    cases use256
    all_goals simp only [nativeRegions,callPointer,span,Bool.false_eq_true,↓reduceIte,
      List.mem_cons,List.not_mem_nil,or_false] at hr hk ⊢
    all_goals rcases hr with rfl | rfl
    all_goals first | contradiction | (simp only [hs112,hs128,hs60,hslot]; rw [window_eq] at hroom; simp only [Bool.false_eq_true,↓reduceIte] at hroom; omega)
  all_goals
    refine ⟨by decide,?_⟩
    intro r hr
    cases use256
    all_goals simp only [nativeRegions,callPointer,span,Bool.false_eq_true,↓reduceIte,
      List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    all_goals rcases hr with rfl | rfl
    all_goals first | contradiction | (simp only [hs112,hs128,hs60,hc0,hc1]; rw [window_eq] at hro hroom; simp only [Bool.false_eq_true,↓reduceIte] at hro hroom; omega)

theorem frame_facts (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (h : Atom.All code args mem (frameAt use256
      (if use256 then .l1069f0 else .l105180) fr)) :
    args[4] = ⟨64,fr.rsp - (if use256 then 120 else 104)⟩ ∧
    args[3] = ⟨64,fr.rsi⟩ ∧
    memLoad mem (fr.rsp - (if use256 then 72 else 64)) 64 = fr.rsi ∧
    fr.low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat ∧
    fr.rsp.toNat % 16 = 8 ∧
    (0x201238 + (frameInfo use256).window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) := by
  cases use256
  · exact ⟨h.1,h.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  · exact ⟨h.1,h.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem native_frame (use256 : Bool) (code : CodeMap) (fr : Activation)
    (before after : Values Value Reg.count) (mem mem' : Ram)
    (h : Atom.All code before mem (frameAt use256
      (if use256 then .l1069f0 else .l105180) fr))
    (hstep : RamWriteFrame mem mem' (nativeRegions use256 fr))
    (hregs : ∀ r : Fin Reg.count, r.val ∈ [3,4,22,39,50,51] → after[r] = before[r]) :
    Atom.All code after mem' (frameAt use256
      (if use256 then .l1069f0 else .l105180) fr) ∧
    RamWriteFrame mem mem' [fr.region] := by
  obtain ⟨_,_,_,hroom,halign,hro⟩ := frame_facts use256 code fr before mem h
  have hstack : Writable code mem (fr.rsp - BitVec.ofNat 64 (frameInfo use256).window)
      (frameInfo use256).window := by
    cases use256 <;> exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hsp,_,_,_,_,_,_,_,_,_⟩ := call_geometry use256 code mem fr 0 (by decide)
    hstack hroom halign
  obtain ⟨hwithin,hslots,hrooutside⟩ := native_geometry use256 fr hroom hsp hro
  exact ⟨frame_preserve use256 code fr before after mem mem' _ h hregs hstep hslots hrooutside,
    (RamWriteFrame.refl mem [fr.region]).trans hstep hwithin⟩

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
