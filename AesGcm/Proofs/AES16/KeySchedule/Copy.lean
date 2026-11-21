import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Fn103f30.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

attribute [local irreducible] memStore memLoad

private theorem toNat_wordAddress (base index : BitVec 64) (k : Nat)
    (h : base.toNat + 2 * (index.toNat + k) < 2 ^ 64) :
    (base + (index <<< 1) + BitVec.ofNat 64 (2 * k)).toNat =
      base.toNat + 2 * (index.toNat + k) := by
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := index.toNat * 2 ^ 1) (by omega),
    Nat.mod_eq_of_lt (a := base.toNat + index.toNat * 2 ^ 1) (by omega),
    Nat.mod_eq_of_lt (a := 2 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem wordAddress_eq (base index : BitVec 64) (k : Nat)
    (h : base.toNat + 2 * (index.toNat + k) < 2 ^ 64) :
    base + (index <<< 1) + BitVec.ofNat 64 (2 * k) =
      base + BitVec.ofNat 64 (2 * (index.toNat + k)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_wordAddress base index k h]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 2 * (index.toNat + k)) (by omega), Nat.mod_eq_of_lt h]

private theorem copy_storeOk_offset {code : CodeMap} {mem : Ram} {addr p : BitVec 64}
    {n off len : Nat} {bytes : List UInt8} (h : Writable code mem addr n)
    (hc : ∀ x ∈ codeRange p bytes, x ∈ code) (hoff : off + len ≤ bytes.length) :
    StoreOk code mem addr n (p + BitVec.ofNat 64 off) len := by
  exact storeOk_of_writable h (RangeApart.right_sub (storeOk_of_codeRange h hc).apart hoff)

set_option maxHeartbeats 2000000 in
theorem copy_callContract (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l103f30 LIR.Fn103f30.frameInfo
      (fun fr ↦ [span (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + 8))) 16])
      (fun fr mem ↦ Writable code mem fr.rdi (2 * fr.rsi.toNat) ∧
        fr.rsi.toNat ≤ 120 ∧ fr.rdx.toNat + 16 ≤ fr.rsi.toNat ∧
        (callStack fr).Disjoint (span fr.rdi (2 * fr.rsi.toNat)))
      (fun fr mem ↦ ∀ p : Fin 8,
        memLoad mem (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + 8 + p.val))) 16 =
          memLoad fr.original (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + p.val))) 16) := by
  unfold CallContract
  dsimp only [LIR.lifted]
  intro fr loc hl hm hats hTypes hpre
  rcases loc with ⟨lab, args, mem⟩
  dsimp only at hl hm hats hpre ⊢
  subst lab mem
  change Atom.All code args fr.original
    [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
      .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9,
      .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
      .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
      .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2^32),
      .writable (fr.rsp - 144) 144, .fact (fr.low.toNat + 144 ≤ fr.rsp.toNat),
      .fact (fr.rsp.toNat % 16 = 8),
      .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
      .mem 0x201230 64 0x101230,
      .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)] at hats
  simp only [Atom.All, Atom.Holds] at hats
  rcases hats with ⟨hsp, hdf, hc, hd, hb, hp, hs, hi, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hr, hret, hrlow, hw, hsl, halign, _⟩
  rcases hpre with ⟨hbuf, hn, hoff, hapart⟩
  have hgrsp : (args[4]).get 64 = fr.rsp := by
    change args[4] = ⟨64, fr.rsp⟩ at hsp
    rw [hsp]
    rfl
  have hgrdx : (args[2]).get 64 = fr.rdx := by
    change args[2] = ⟨64, fr.rdx⟩ at hd
    rw [hd]
    rfl
  have hgrsi : (args[6]).get 64 = fr.rsi := by
    change args[6] = ⟨64, fr.rsi⟩ at hs
    rw [hs]
    rfl
  have hgrdi : (args[7]).get 64 = fr.rdi := by
    change args[7] = ⟨64, fr.rdi⟩ at hi
    rw [hi]
    rfl
  have hbl := hbuf.readable.low
  let a (k : Nat) := fr.rdi + (fr.rdx <<< 1) + BitVec.ofNat 64 (2 * k)
  have ha (k : Nat) (hk : k ≤ 16) :
      (a k).toNat = fr.rdi.toNat + 2 * (fr.rdx.toNat + k) :=
    toNat_wordAddress fr.rdi fr.rdx k (by omega)
  have haddr (k : Nat) (hk : k ≤ 16) :
      a k = fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + k)) :=
    wordAddress_eq fr.rdi fr.rdx k (by omega)
  have hread (m : Ram) (hf : RamWriteFrame fr.original m
      [fr.region, span (a 8) 16]) (k : Nat) (hk : k < 16) :
      LoadOk m (a k) 2 := by
    apply LoadOk.of_region (hbuf.readable.of_frame hf)
    · rw [ha k (by omega)]; omega
    · rw [ha k (by omega)]; omega
  have hbranch (k : Nat) (hk : k ≤ 15) :
      (!(cmpSpec (fr.rdx + BitVec.ofNat 64 k) fr.rsi).CF) = false := by
    have hlt : (fr.rdx + BitVec.ofNat 64 k).toNat < fr.rsi.toNat := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [cmpSpec, subSpec, hlt, decide_true, Bool.not_true]
  have hspnat : (fr.rsp - 8).toNat = fr.rsp.toNat - 8 := by bv_omega
  have hstack : Writable code fr.original (fr.rsp - 8) 8 := by
    apply hw.sub
    · bv_omega
    · bv_omega
  have hsep : fr.rsp.toNat + 8 ≤ fr.rdi.toNat ∨
      fr.rdi.toNat + 2 * fr.rsi.toNat ≤ fr.low.toNat := by
    by_cases h1 : fr.rsp.toNat + 8 ≤ fr.rdi.toNat
    · exact Or.inl h1
    by_cases h2 : fr.rdi.toNat + 2 * fr.rsi.toNat ≤ fr.low.toNat
    · exact Or.inr h2
    exfalso
    have hn1 : fr.rdi.toNat < fr.rsp.toNat + 8 := by omega
    have hn2 : fr.low.toNat < fr.rdi.toNat + 2 * fr.rsi.toNat := by omega
    apply hapart (max fr.low.toNat fr.rdi.toNat)
    · simp only [callStack, MemoryRegion.Contains]
      omega
    · simp only [span, MemoryRegion.Contains]
      omega
  have hin (k : Nat) (hk : k < 8) :
      InRegions [fr.region, span (a 8) 16] (a (8+k)) 2 := by
    refine ⟨span (a 8) 16, by simp, ?_⟩
    simp only [InRegion, span, ha 8 (by omega), ha (8+k) (by omega)]
    omega
  have hslot : InRegions [fr.region, span (a 8) 16] (fr.rsp - 8) 8 := by
    refine ⟨fr.region, by simp, ?_⟩
    simp only [InRegion, Activation.region, hspnat]
    have := hr.low
    omega
  have hwrite (m : Ram) (hf : RamWriteFrame fr.original m
      [fr.region, span (a 8) 16]) (k : Nat) (hk : k < 16) :
      Writable code m (a k) 2 := by
    apply (hbuf.of_frame hf).sub
    · rw [ha k (by omega)]; omega
    · rw [ha k (by omega)]; omega
  have hsource (m : Ram) (hf : RamWriteFrame fr.original m
      [fr.region, span (a 8) 16]) (k : Nat) (hk : k < 8) :
      memLoad m (a k) 16 = memLoad fr.original (a k) 16 := by
    apply hf.memLoad_eq
    refine ⟨?_, ?_⟩
    · rw [ha k (by omega)]; omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Activation.region]
        rw [ha k (by omega)]
        omega
      · simp only [span]
        rw [ha k (by omega), ha 8 (by omega)]
        omega
  obtain ⟨m0, hm0⟩ :
      ∃ m0 : Ram, memStore fr.original (fr.rsp - BitVec.ofNat 64 8) ((args[0]).get 64) = m0 :=
    ⟨memStore fr.original (fr.rsp - BitVec.ofNat 64 8) ((args[0]).get 64), rfl⟩
  have hf0 := (RamWriteFrame.refl fr.original [fr.region, span (a 8) 16]).memStore
    ((args[0]).get 64) hslot
  simp only [BitVec.ofNat_eq_ofNat] at hf0
  rw [hm0] at hf0
  have hg0 := copy_storeOk_offset
    (p := 0x103f30) (bytes := LIR.bytes_l103f30) (off := 0) (len := 1)
    hstack (fun x hx => hcode x (LIR.code_l103f30 x hx)) (by decide)
  simp only [BitVec.add_zero] at hg0
  obtain ⟨m1, hm1⟩ :
      ∃ m1 : Ram, memStore m0 (a 15) (memLoad fr.original (a 7) 16) = m1 :=
    ⟨memStore m0 (a 15) (memLoad fr.original (a 7) 16), rfl⟩
  have hf1 := hf0.memStore (memLoad fr.original (a 7) 16) (hin 7 (by decide))
  simp only [Nat.reduceAdd] at hf1
  rw [hm1] at hf1
  have hl1 := hread m0 hf0 7 (by decide)
  have hv1 := hsource m0 hf0 7 (by decide)
  have hg1 := copy_storeOk_offset
    (p := 0x103f4b) (bytes := LIR.bytes_l103f4b) (off := 5) (len := 5)
    (hwrite m0 hf0 15 (by decide))
    (fun x hx => hcode x (LIR.code_l103f4b x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg1
  obtain ⟨m2, hm2⟩ :
      ∃ m2 : Ram, memStore m1 (a 14) (memLoad fr.original (a 6) 16) = m2 :=
    ⟨memStore m1 (a 14) (memLoad fr.original (a 6) 16), rfl⟩
  have hf2 := hf1.memStore (memLoad fr.original (a 6) 16) (hin 6 (by decide))
  simp only [Nat.reduceAdd] at hf2
  rw [hm2] at hf2
  have hl2 := hread m1 hf1 6 (by decide)
  have hv2 := hsource m1 hf1 6 (by decide)
  have hg2 := copy_storeOk_offset
    (p := 0x103f62) (bytes := LIR.bytes_l103f62) (off := 5) (len := 5)
    (hwrite m1 hf1 14 (by decide))
    (fun x hx => hcode x (LIR.code_l103f62 x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg2
  obtain ⟨m3, hm3⟩ :
      ∃ m3 : Ram, memStore m2 (a 13) (memLoad fr.original (a 5) 16) = m3 :=
    ⟨memStore m2 (a 13) (memLoad fr.original (a 5) 16), rfl⟩
  have hf3 := hf2.memStore (memLoad fr.original (a 5) 16) (hin 5 (by decide))
  simp only [Nat.reduceAdd] at hf3
  rw [hm3] at hf3
  have hl3 := hread m2 hf2 5 (by decide)
  have hv3 := hsource m2 hf2 5 (by decide)
  have hg3 := copy_storeOk_offset
    (p := 0x103f79) (bytes := LIR.bytes_l103f79) (off := 5) (len := 5)
    (hwrite m2 hf2 13 (by decide))
    (fun x hx => hcode x (LIR.code_l103f79 x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg3
  obtain ⟨m4, hm4⟩ :
      ∃ m4 : Ram, memStore m3 (a 12) (memLoad fr.original (a 4) 16) = m4 :=
    ⟨memStore m3 (a 12) (memLoad fr.original (a 4) 16), rfl⟩
  have hf4 := hf3.memStore (memLoad fr.original (a 4) 16) (hin 4 (by decide))
  simp only [Nat.reduceAdd] at hf4
  rw [hm4] at hf4
  have hl4 := hread m3 hf3 4 (by decide)
  have hv4 := hsource m3 hf3 4 (by decide)
  have hg4 := copy_storeOk_offset
    (p := 0x103f8c) (bytes := LIR.bytes_l103f8c) (off := 5) (len := 5)
    (hwrite m3 hf3 12 (by decide))
    (fun x hx => hcode x (LIR.code_l103f8c x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg4
  obtain ⟨m5, hm5⟩ :
      ∃ m5 : Ram, memStore m4 (a 11) (memLoad fr.original (a 3) 16) = m5 :=
    ⟨memStore m4 (a 11) (memLoad fr.original (a 3) 16), rfl⟩
  have hf5 := hf4.memStore (memLoad fr.original (a 3) 16) (hin 3 (by decide))
  simp only [Nat.reduceAdd] at hf5
  rw [hm5] at hf5
  have hl5 := hread m4 hf4 3 (by decide)
  have hv5 := hsource m4 hf4 3 (by decide)
  have hg5 := copy_storeOk_offset
    (p := 0x103f9f) (bytes := LIR.bytes_l103f9f) (off := 5) (len := 5)
    (hwrite m4 hf4 11 (by decide))
    (fun x hx => hcode x (LIR.code_l103f9f x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg5
  obtain ⟨m6, hm6⟩ :
      ∃ m6 : Ram, memStore m5 (a 10) (memLoad fr.original (a 2) 16) = m6 :=
    ⟨memStore m5 (a 10) (memLoad fr.original (a 2) 16), rfl⟩
  have hf6 := hf5.memStore (memLoad fr.original (a 2) 16) (hin 2 (by decide))
  simp only [Nat.reduceAdd] at hf6
  rw [hm6] at hf6
  have hl6 := hread m5 hf5 2 (by decide)
  have hv6 := hsource m5 hf5 2 (by decide)
  have hg6 := copy_storeOk_offset
    (p := 0x103fb2) (bytes := LIR.bytes_l103fb2) (off := 5) (len := 5)
    (hwrite m5 hf5 10 (by decide))
    (fun x hx => hcode x (LIR.code_l103fb2 x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg6
  obtain ⟨m7, hm7⟩ :
      ∃ m7 : Ram, memStore m6 (a 9) (memLoad fr.original (a 1) 16) = m7 :=
    ⟨memStore m6 (a 9) (memLoad fr.original (a 1) 16), rfl⟩
  have hf7 := hf6.memStore (memLoad fr.original (a 1) 16) (hin 1 (by decide))
  simp only [Nat.reduceAdd] at hf7
  rw [hm7] at hf7
  have hl7 := hread m6 hf6 1 (by decide)
  have hv7 := hsource m6 hf6 1 (by decide)
  have hg7 := copy_storeOk_offset
    (p := 0x103fc5) (bytes := LIR.bytes_l103fc5) (off := 5) (len := 5)
    (hwrite m6 hf6 9 (by decide))
    (fun x hx => hcode x (LIR.code_l103fc5 x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg7
  obtain ⟨m8, hm8⟩ :
      ∃ m8 : Ram, memStore m7 (a 8) (memLoad fr.original (a 0) 16) = m8 :=
    ⟨memStore m7 (a 8) (memLoad fr.original (a 0) 16), rfl⟩
  have hf8 := hf7.memStore (memLoad fr.original (a 0) 16) (hin 0 (by decide))
  simp only [Nat.reduceAdd] at hf8
  rw [hm8] at hf8
  have hl8 := hread m7 hf7 0 (by decide)
  have hv8 := hsource m7 hf7 0 (by decide)
  have hg8 := copy_storeOk_offset
    (p := 0x103fdd) (bytes := LIR.bytes_l103fdd) (off := 4) (len := 5)
    (hwrite m7 hf7 8 (by decide))
    (fun x hx => hcode x (LIR.code_l103fdd x hx)) (by decide)
  simp only [BitVec.reduceAdd] at hg8
  have hpop : LoadOk m8 (fr.rsp-8) 8 :=
    ⟨(hstack.readable.of_frame hf8).low, (hstack.readable.of_frame hf8).present⟩
  have hrl : LoadOk m8 fr.rsp 8 := ⟨(hr.of_frame hf8).low, (hr.of_frame hf8).present⟩
  have hout : Outside [fr.region, span (a 8) 16] fr.rsp 8 := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · simp only [Activation.region]; omega
    · simp only [span, ha 8 (by decide)]; omega
  have hrret : memLoad m8 fr.rsp 64 = fr.ret := (hf8.memLoad_eq hout).trans hret
  have hb1 : (!(cmpSpec (fr.rdx+1) fr.rsi).CF) = false := hbranch 1 (by decide)
  have hb2 : (!(cmpSpec (fr.rdx+2) fr.rsi).CF) = false := hbranch 2 (by decide)
  have hb3 : (!(cmpSpec (fr.rdx+3) fr.rsi).CF) = false := hbranch 3 (by decide)
  have hb4 : (!(cmpSpec (fr.rdx+4) fr.rsi).CF) = false := hbranch 4 (by decide)
  have hb5 : (!(cmpSpec (fr.rdx+5) fr.rsi).CF) = false := hbranch 5 (by decide)
  have hb6 : (!(cmpSpec (fr.rdx+6) fr.rsi).CF) = false := hbranch 6 (by decide)
  have hb7 : (!(cmpSpec (fr.rdx+7) fr.rsi).CF) = false := hbranch 7 (by decide)
  have hb8 : (!(cmpSpec (fr.rdx+8) fr.rsi).CF) = false := hbranch 8 (by decide)
  have hb15 : (!(cmpSpec (fr.rdx+15) fr.rsi).CF) = false := hbranch 15 (by decide)
  have hb0 : (!(cmpSpec fr.rdx fr.rsi).CF) = false := by
    simpa only [BitVec.add_zero] using hbranch 0 (by decide)
  simp only [a, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hg0 hl1 hg1 hv1 hl2 hg2 hv2 hl3 hg3 hv3 hl4 hg4 hv4 hl5 hg5 hv5 hl6 hg6 hv6 hl7 hg7 hv7 hl8 hg8 hv8 hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hpop hrret hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb15
  refine ⟨?out, ?exec, ?tag, ?done, ?typed, ?frame, ?post⟩
  case exec =>
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrsp, hgrdx, hgrsi, BitVec.ofNat_eq_ofNat]
        simp only [hg0, hm0, hb7, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, BitVec.ofNat_eq_ofNat]
        simp only [hb15, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl1, hg1, hv1, hm1, hb6, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl2, hg2, hv2, hm2, hb5, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl3, hg3, hv3, hm3, hb4, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl4, hg4, hv4, hm4, hb3, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl5, hg5, hv5, hm5, hb2, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl6, hg6, hv6, hm6, hb1, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, hgrdi, BitVec.ofNat_eq_ofNat]
        simp only [hl7, hg7, hv7, hm7, hb0, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.next
    · as_aux_lemma =>
        cfg_eval [LIR.program]
        simp only [hgrdx, hgrsi, BitVec.ofNat_eq_ofNat]
        simp only [hb8, Bool.false_eq_true, ↓reduceIte]
        rfl
    apply Program.Exec.done
    as_aux_lemma =>
      cfg_eval [LIR.program]
      simp only [hgrdx, hgrdi, BitVec.ofNat_eq_ofNat]
      simp only [hl8, hg8, hv8, hm8, hpop, hrl, hrret, hrlow, and_self, ↓reduceIte]
      rfl
  case tag => runtime_finish []
  case done =>
    as_aux_lemma =>
      exact ⟨rfl, hdf, hb, hp, h12, h13, h14, h15, h39, h50, h51, trivial⟩
  case typed =>
    as_aux_lemma =>
      intro r
      rcases r with ⟨r, hr⟩
      have hr' : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨
          r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=14 ∨ r=15 := by omega
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · exact hTypes ⟨1, by decide⟩
      · exact hTypes ⟨2, by decide⟩
      · exact hTypes ⟨3, by decide⟩
      · rfl
      · exact hTypes ⟨5, by decide⟩
      · exact hTypes ⟨6, by decide⟩
      · exact hTypes ⟨7, by decide⟩
      · exact hTypes ⟨8, by decide⟩
      · exact hTypes ⟨9, by decide⟩
      · exact hTypes ⟨10, by decide⟩
      · exact hTypes ⟨11, by decide⟩
      · exact hTypes ⟨12, by decide⟩
      · exact hTypes ⟨13, by decide⟩
      · exact hTypes ⟨14, by decide⟩
      · exact hTypes ⟨15, by decide⟩
  case frame =>
    as_aux_lemma =>
      change RamWriteFrame fr.original m8 _
      rw [← haddr 8 (by decide)]
      exact hf8
  case post =>
    intro p
    change memLoad m8 _ 16 = _
    rw [Nat.add_assoc, ← haddr (8+p.val) (by omega), ← haddr p.val (by omega)]
    have hap (i j : Nat) (hi : i < 8) (hj : j < 8) (hne : i ≠ j) :
        RangeApart (a (8+i)) 2 (a (8+j)) 2 := by
      apply RangeApart.of_toNat
      · rw [ha (8+i) (by omega)]; omega
      · rw [ha (8+j) (by omega)]; omega
      · rw [ha (8+i) (by omega), ha (8+j) (by omega)]; omega
    have hloadStore (m : Ram) (i j : Nat) (hi : i < 8) (hj : j < 8) :
        memLoad (memStore m (a (8+i)) (memLoad fr.original (a i) 16))
          (a (8+j)) 16 =
        if i = j then memLoad fr.original (a i) 16 else memLoad m (a (8+j)) 16 := by
      by_cases he : i = j
      · subst j
        simp only [ite_true]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · simp only [ite_eq_right he]
        exact memLoad_memStore_of_rangeApart m _ _ _ 16 (hap i j hi hj he)
    have hm8' : memStore m7 (a 8) (memLoad fr.original (a 0) 16) = m8 := by
      simpa only [a, Nat.reduceMul, BitVec.add_zero] using hm8
    rw [← hm8', hloadStore m7 0 p.val (by decide) p.isLt]
    rw [← hm7, hloadStore m6 1 p.val (by decide) p.isLt]
    rw [← hm6, hloadStore m5 2 p.val (by decide) p.isLt]
    rw [← hm5, hloadStore m4 3 p.val (by decide) p.isLt]
    rw [← hm4, hloadStore m3 4 p.val (by decide) p.isLt]
    rw [← hm3, hloadStore m2 5 p.val (by decide) p.isLt]
    rw [← hm2, hloadStore m1 6 p.val (by decide) p.isLt]
    rw [← hm1, hloadStore m0 7 p.val (by decide) p.isLt]
    rcases p with ⟨p, hp⟩
    have hp' : p=0 ∨ p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=5 ∨ p=6 ∨ p=7 := by omega
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

end AesGcm.Proofs.Machine.AES16.KeySchedule
