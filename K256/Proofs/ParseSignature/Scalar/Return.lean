import K256.Proofs.ParseSignature.Memory
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn107730.Frame

import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.ParseSignature.Scalar

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

set_option maxHeartbeats 800000 in
theorem finish_decode {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram) (valid : Bool)
    (hframe : Atom.All code args mem (Fn107730.frameAt .l107880 fr))
    (hflag : args[0] = ⟨64, if valid then 1 else 0⟩) (herror : args[14] = ⟨64, 1⟩)
    (hw : Writable code mem fr.rdi 40) (hout : Outside [callStack fr] fr.rdi 40)
    (h0 : args[15] = ⟨64, scalarWord fr.original fr.rsi 0⟩)
    (h1 : args[12] = ⟨64, scalarWord fr.original fr.rsi 1⟩)
    (h2 : args[13] = ⟨64, scalarWord fr.original fr.rsi 2⟩)
    (h3 : args[5] = ⟨64, scalarWord fr.original fr.rsi 3⟩)
    (widths : ArgumentWidths args) :
    ∃ out : Output Value Ram Reg.count,
      program.Exec (dialect code) ⟨⟨.l107880, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn107730.frameInfo.doneAtoms fr) ∧
      RamWriteFrame mem out.store [buffer fr.rdi 40] ∧ ArgumentWidths out.values ∧
      (if valid then memLoad out.store fr.rdi 64 = 0 ∧
        scalarLimbsAt out.store (fr.rdi + 8) fr.original fr.rsi
      else memLoad out.store fr.rdi 64 = 1) := by
  simp only [Fn107730.frameAt, Fn107730.frameAtG0, Atom.All, Atom.Holds] at hframe
  obtain ⟨hsp, hdf, hdi, hmxcsr, hftw, hfcw, hbx, hs12, hs13, hs14, hs15, hbp,
    hread, hret, hretLow, hwrite, hroom, _, _⟩ := hframe
  let branchArgs (ok : Bool) := args.set 19 (.ofBool ok)
  let retArgs := if valid then (branchArgs true).set 14 ⟨64, 0⟩ else branchArgs false
  let w := scalarWord fr.original fr.rsi
  let m1 := memStore mem (fr.rdi + 8) (w 0)
  let m2 := memStore m1 (fr.rdi + 16) (w 1)
  let m3 := memStore m2 (fr.rdi + 24) (w 2)
  let m4 := memStore m3 (fr.rdi + 32) (w 3)
  let retMem := if valid then m4 else mem
  let status : BitVec 64 := if valid then 0 else 1
  let finalMem := memStore retMem fr.rdi status
  have diNat (off : Nat) (hoff : off ≤ 40) :
      (fr.rdi + BitVec.ofNat 64 off).toNat = fr.rdi.toNat + off := by
    have := hw.readable.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have inBuffer (off : Nat) (hoff : off + 8 ≤ 40) :
      InRegions [buffer fr.rdi 40] (fr.rdi + BitVec.ofNat 64 off) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change fr.rdi.toNat ≤ _ ∧ _ ≤ fr.rdi.toNat + 40 ∧ _ ≤ 2 ^ 64
    rw [diNat off (by omega)]
    have := hw.readable.low
    omega
  have frame₀ := RamWriteFrame.refl mem [buffer fr.rdi 40]
  have frame₁ : RamWriteFrame mem m1 [buffer fr.rdi 40] :=
    frame₀.memStore (w 0) (inBuffer 8 (by decide))
  have frame₂ : RamWriteFrame mem m2 [buffer fr.rdi 40] :=
    frame₁.memStore (w 1) (inBuffer 16 (by decide))
  have frame₃ : RamWriteFrame mem m3 [buffer fr.rdi 40] :=
    frame₂.memStore (w 2) (inBuffer 24 (by decide))
  have frame₄ : RamWriteFrame mem m4 [buffer fr.rdi 40] :=
    frame₃.memStore (w 3) (inBuffer 32 (by decide))
  have frameRet : RamWriteFrame mem retMem [buffer fr.rdi 40] := by
    cases valid
    · exact frame₀
    · exact frame₄
  have diAddZero : fr.rdi + 0 = fr.rdi := BitVec.add_zero _
  have frameFinal : RamWriteFrame mem finalMem [buffer fr.rdi 40] := by
    apply frameRet.memStore status
    have hin := inBuffer 0 (by decide)
    change InRegions [buffer fr.rdi 40] (fr.rdi + 0) 8 at hin
    rwa [diAddZero] at hin
  have storeGuard {m : Ram} (hm : RamWriteFrame mem m [buffer fr.rdi 40])
      (off : Nat) (hoff : off + 8 ≤ 40) (base : BitVec 64) (bytes : List UInt8)
      (hbytes : ∀ x ∈ codeRange base bytes, x ∈ fnCode) (pcOff len : Nat)
      (hlen : pcOff + len ≤ bytes.length) :
      StoreOk code m (fr.rdi + BitVec.ofNat 64 off) 8 (base + BitVec.ofNat 64 pcOff) len := by
    have hn := diNat off (by omega)
    exact storeOk_of_codeRange ((hw.of_frame hm).sub (by omega) (by omega))
      (fun x hx => hcode x (hbytes x hx)) hlen
  have statusGuard : StoreOk code retMem fr.rdi 8 0x107897 3 := by
    have hg := storeGuard frameRet 0 (by decide) 0x107897 bytes_l107897 code_l107897 0 3 (by decide)
    change StoreOk code retMem (fr.rdi + 0) 8 0x107897 3 at hg
    rwa [diAddZero] at hg
  have vectorExt {a b : Vector Value 53} (h : ∀ i : Fin 53, a[i.val] = b[i.val]) : a = b :=
    Vector.ext fun i hi => h ⟨i, hi⟩
  have flagBits : (Value.get 64 args[0]).setWidth 8 = if valid then 1 else 0 := by
    rw [hflag]
    cases valid <;> rfl
  have branch : program.runBlock (dialect code) ⟨.l107880, args, mem⟩ =
      .jump ⟨(if valid then .l107884 else .l107897), branchArgs valid, mem⟩ := by
    cases valid <;>
      cfg_eval <;>
      rw [flagBits] <;>
      simp only [ite_true, ite_false, eq_self, Bool.false_eq_true,
        show (cmpSpec (0 : BitVec 8) 1).ZF = false from rfl,
        show (cmpSpec (1 : BitVec 8) 1).ZF = true from rfl,
        Bool.not_false, Bool.not_true] <;>
      congr 2 <;>
      apply vectorExt <;>
      intro i <;>
      finite_cases i <;> simp only [branchArgs, Vector.getElem_set] <;> rfl
  have branchReg (ok : Bool) (i : Fin 53) (hi : 19 ≠ i.val) :
      (branchArgs ok)[i.val] = args[i.val] :=
    Vector.getElem_set_ne _ _ hi
  have writeLimbs : program.runBlock (dialect code) ⟨.l107884, branchArgs true, mem⟩ =
      .jump ⟨.l107897, (branchArgs true).set 14 ⟨64, 0⟩, m4⟩ := by
    have hs₁ : StoreOk code mem (fr.rdi + 8) 8 0x107884 4 :=
      storeGuard frame₀ 8 (by decide) 0x107884 _ code_l107884 0 4 (by decide)
    have hs₂ : StoreOk code m1 (fr.rdi + 16) 8 0x107888 4 :=
      storeGuard frame₁ 16 (by decide) 0x107884 _ code_l107884 4 4 (by decide)
    have hs₃ : StoreOk code m2 (fr.rdi + 24) 8 0x10788c 4 :=
      storeGuard frame₂ 24 (by decide) 0x107884 _ code_l107884 8 4 (by decide)
    have hs₄ : StoreOk code m3 (fr.rdi + 32) 8 0x107890 4 :=
      storeGuard frame₃ 32 (by decide) 0x107884 _ code_l107884 12 4 (by decide)
    have rb : Value.get 64 (branchArgs true)[3] = fr.rdi :=
      congrArg (Value.get 64) ((branchReg true 3 (by decide)).trans hdi)
    have r₀ : Value.get 64 (branchArgs true)[15] = w 0 :=
      congrArg (Value.get 64) ((branchReg true 15 (by decide)).trans h0)
    have r₁ : Value.get 64 (branchArgs true)[12] = w 1 :=
      congrArg (Value.get 64) ((branchReg true 12 (by decide)).trans h1)
    have r₂ : Value.get 64 (branchArgs true)[13] = w 2 :=
      congrArg (Value.get 64) ((branchReg true 13 (by decide)).trans h2)
    have r₃ : Value.get 64 (branchArgs true)[5] = w 3 :=
      congrArg (Value.get 64) ((branchReg true 5 (by decide)).trans h3)
    dsimp only [m3, m2, m1] at hs₂ hs₃ hs₄
    dsimp only [branchArgs] at rb r₀ r₁ r₂ r₃
    cfg_eval
    simp only [rb, r₀, r₁, r₂, r₃, hs₁, hs₂, hs₃, hs₄, ↓reduceIte]
    congr 2
    apply vectorExt
    intro i
    finite_cases i <;> simp only [branchArgs, Vector.getElem_set] <;> rfl
  have stackNat (off : Nat) (hoff : off ≤ 0x170) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    have hn : (BitVec.ofNat 64 off).toNat = off := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle : BitVec.ofNat 64 off ≤ fr.rsp := by
      rw [BitVec.le_def, hn]
      omega
    rw [BitVec.toNat_sub_of_le hle, hn]
  have loadSlot (off : Nat) (hmin : 8 ≤ off) (hmax : off ≤ 0x170) :
      LoadOk finalMem (fr.rsp - BitVec.ofNat 64 off) 8 := by
    have hs := stackNat off hmax
    have hb := stackNat 0x170 (by decide)
    exact LoadOk.of_region (hwrite.readable.of_frame frameFinal)
      (by change (fr.rsp - BitVec.ofNat 64 0x170).toNat ≤ _; omega)
      (by change _ ≤ (fr.rsp - BitVec.ofNat 64 0x170).toNat + 0x170; omega)
  have outsideSlot (off : Nat) (hoff : off ≤ 0x30) :
      Outside [buffer fr.rdi 40] (fr.rsp - BitVec.ofNat 64 off) 8 := by
    have hr := hread.low
    have hs := stackNat off (by omega)
    refine ⟨by omega, ?_⟩
    intro r hrmem
    rcases List.mem_singleton.mp hrmem with rfl
    have hap := hout.2 _ (List.mem_singleton_self _)
    change fr.rdi.toNat + 40 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at hap
    change _ ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 40 ≤ _
    omega
  have savedSlot (off : Nat) (hoff : off ≤ 0x30) :
      memLoad finalMem (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 :=
    frameFinal.memLoad_eq (outsideSlot off hoff)
  have retLoad : LoadOk finalMem fr.rsp 8 :=
    let hr := hread.of_frame frameFinal
    ⟨hr.low, hr.present⟩
  have retValue : memLoad finalMem fr.rsp 64 = fr.ret := by
    have he := savedSlot 0 (by decide)
    change memLoad finalMem (fr.rsp - 0) 64 = memLoad mem (fr.rsp - 0) 64 at he
    have hzero : fr.rsp - 0 = fr.rsp := BitVec.sub_zero _
    rwa [hzero, hret] at he
  have retReg (i : Fin 53) (hi : 19 ≠ i.val) (hj : 14 ≠ i.val) :
      retArgs[i.val] = args[i.val] := by
    cases valid
    · exact branchReg false i hi
    · exact (Vector.getElem_set_ne (xs := branchArgs true) (x := (⟨64, 0⟩ : Value)) (by decide) i.isLt hj).trans (branchReg true i hi)
  have spBits : Value.get 64 retArgs[4] = fr.rsp - 0x98 :=
    congrArg (Value.get 64) ((retReg 4 (by decide) (by decide)).trans hsp)
  have diBits : Value.get 64 retArgs[3] = fr.rdi :=
    congrArg (Value.get 64) ((retReg 3 (by decide) (by decide)).trans hdi)
  have statusBits : Value.get 64 retArgs[14] = status := by
    cases valid
    · exact congrArg (Value.get 64) ((branchReg false 14 (by decide)).trans herror)
    · change Value.get 64 ((branchArgs true).set 14 ⟨64, 0⟩)[14] = 0
      rw [Vector.getElem_set_self]
      rfl
  have storeMem : memStore retMem fr.rdi status = finalMem := rfl
  have retBlock : ∃ out,
      program.runBlock (dialect code) ⟨.l107897, retArgs, retMem⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code out.values out.store (Fn107730.frameInfo.doneAtoms fr) ∧
      out.store = finalMem ∧ ArgumentWidths out.values := by
    have ha104 : fr.rsp - 0x98 + 104 = fr.rsp - 0x30 := by bv_omega
    have ha112 : fr.rsp - 0x98 + 112 = fr.rsp - 0x28 := by bv_omega
    have ha120 : fr.rsp - 0x98 + 120 = fr.rsp - 0x20 := by bv_omega
    have ha128 : fr.rsp - 0x98 + 128 = fr.rsp - 0x18 := by bv_omega
    have ha136 : fr.rsp - 0x98 + 136 = fr.rsp - 0x10 := by bv_omega
    have ha144 : fr.rsp - 0x98 + 144 = fr.rsp - 0x8 := by bv_omega
    have ha152 : fr.rsp - 0x98 + 152 = fr.rsp := by bv_omega
    have ha160 : fr.rsp - 0x98 + 160 = fr.rsp + 8 := by bv_omega
    have hl104 : LoadOk finalMem (fr.rsp - 0x30) 8 := loadSlot 0x30 (by decide) (by decide)
    have hl112 : LoadOk finalMem (fr.rsp - 0x28) 8 := loadSlot 0x28 (by decide) (by decide)
    have hl120 : LoadOk finalMem (fr.rsp - 0x20) 8 := loadSlot 0x20 (by decide) (by decide)
    have hl128 : LoadOk finalMem (fr.rsp - 0x18) 8 := loadSlot 0x18 (by decide) (by decide)
    have hl136 : LoadOk finalMem (fr.rsp - 0x10) 8 := loadSlot 0x10 (by decide) (by decide)
    have hl144 : LoadOk finalMem (fr.rsp - 0x8) 8 := loadSlot 0x8 (by decide) (by decide)
    have hs104 : memLoad finalMem (fr.rsp - 0x30) 64 = fr.rbx :=
      (savedSlot 0x30 (by decide)).trans hbx
    have hs112 : memLoad finalMem (fr.rsp - 0x28) 64 = fr.r12 :=
      (savedSlot 0x28 (by decide)).trans hs12
    have hs120 : memLoad finalMem (fr.rsp - 0x20) 64 = fr.r13 :=
      (savedSlot 0x20 (by decide)).trans hs13
    have hs128 : memLoad finalMem (fr.rsp - 0x18) 64 = fr.r14 :=
      (savedSlot 0x18 (by decide)).trans hs14
    have hs136 : memLoad finalMem (fr.rsp - 0x10) 64 = fr.r15 :=
      (savedSlot 0x10 (by decide)).trans hs15
    have hs144 : memLoad finalMem (fr.rsp - 0x8) 64 = fr.rbp :=
      (savedSlot 0x8 (by decide)).trans hbp
    refine ⟨?_, ?eval, ?tag, ?atoms, ?memEq, ?retWidths⟩
    case eval =>
      dsimp only [retArgs] at spBits statusBits diBits
      dsimp only [retMem] at storeMem statusGuard
      cfg_eval
      simp only [spBits, diBits, statusBits, storeMem, statusGuard,
        ha104, ha112, ha120, ha128, ha136, ha144, ha152, ha160,
        hl104, hl112, hl120, hl128, hl136, hl144, retLoad, retValue, hretLow,
        hs104, hs112, hs120, hs128, hs136, hs144, and_self, ↓reduceIte]
      rfl
    case tag => rfl
    case memEq => rfl
    case atoms =>
      simp only [Fn107730.frameInfo, FrameInfo.doneAtoms, Activation.entryReg,
        Activation.entryValue, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        Atom.All, Atom.Holds]
      refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, trivial⟩
      · exact (retReg 22 (by decide) (by decide)).trans hdf
      · exact (retReg 39 (by decide) (by decide)).trans hmxcsr
      · exact (retReg 50 (by decide) (by decide)).trans hftw
      · exact (retReg 51 (by decide) (by decide)).trans hfcw
    case retWidths =>
      intro ⟨i, hi⟩ harg
      have hwidth := widths ⟨i, hi⟩ harg
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at harg
      rcases harg with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (congrArg Value.width
          (retReg _ (of_decide_eq_true rfl) (of_decide_eq_true rfl))).trans hwidth
  obtain ⟨out, heval, htag, hdone, hstore, hwidths⟩ := retBlock
  have hretExec : program.Exec (dialect code) ⟨⟨.l107897, retArgs, retMem⟩, []⟩ out := by
    apply Program.Exec.done
    simp only [Program.step, heval, Transfer.next]
  refine ⟨out, ?_, htag, hdone, hstore ▸ frameFinal, hwidths, ?_⟩
  · apply Program.Exec.next (next := ⟨⟨if valid then .l107884 else .l107897, branchArgs valid, mem⟩, []⟩)
    · simp only [Program.step, branch, Transfer.next]
    · cases valid
      · exact hretExec
      · change program.Exec (dialect code) ⟨⟨.l107884, branchArgs true, mem⟩, []⟩ out
        apply Program.Exec.next (next := ⟨⟨.l107897, retArgs, retMem⟩, []⟩)
        · simp only [Program.step, writeLimbs, Transfer.next]
          rfl
        · exact hretExec
  · rw [hstore]
    have hstatus := memLoad_memStore_same retMem fr.rdi status (by decide) (by decide)
    cases valid
    · exact hstatus
    · refine ⟨hstatus, ?_⟩
      intro i hi
      have hap (off src : BitVec 64)
          (hne : 8 ≤ (off - src).toNat ∧ 8 ≤ (src - off).toNat) :
          RangeApart (fr.rdi + src) 8 (fr.rdi + off) 8 :=
        RangeApart.of_offsets rfl rfl hne
      have hapStatus (off : BitVec 64)
          (hne : 8 ≤ off.toNat ∧ 8 ≤ (0 - off).toNat) :
          RangeApart fr.rdi 8 (fr.rdi + off) 8 :=
        RangeApart.of_offsets (addr_self _) rfl (by
          have he : off - 0 = off := BitVec.sub_zero _
          rwa [he])
      have hload (off : BitVec 64) (hne : 8 ≤ off.toNat ∧ 8 ≤ (0 - off).toNat) :
          memLoad finalMem (fr.rdi + off) 64 = memLoad m4 (fr.rdi + off) 64 :=
        memLoad_memStore_of_rangeApart m4 fr.rdi _ 0 64 (hapStatus off hne)
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl | rfl
      · show memLoad finalMem (fr.rdi + 8 + 0) 64 = w 0
        have ha : fr.rdi + 8 + 0 = fr.rdi + 8 := BitVec.add_zero _
        rw [ha, hload 8 (by decide)]
        dsimp only [m4, m3, m2, m1]
        rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (hap 8 32 (by decide)),
          memLoad_memStore_of_rangeApart _ _ _ _ 64 (hap 8 24 (by decide)),
          memLoad_memStore_of_rangeApart _ _ _ _ 64 (hap 8 16 (by decide)),
          memLoad_memStore_same _ _ _ (by decide) (by decide)]
      · show memLoad finalMem (fr.rdi + 8 + 8) 64 = w 1
        have ha : fr.rdi + 8 + 8 = fr.rdi + 16 := BitVec.add_assoc _ _ _
        rw [ha, hload 16 (by decide)]
        dsimp only [m4, m3, m2]
        rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (hap 16 32 (by decide)),
          memLoad_memStore_of_rangeApart _ _ _ _ 64 (hap 16 24 (by decide)),
          memLoad_memStore_same _ _ _ (by decide) (by decide)]
      · show memLoad finalMem (fr.rdi + 8 + 16) 64 = w 2
        have ha : fr.rdi + 8 + 16 = fr.rdi + 24 := BitVec.add_assoc _ _ _
        rw [ha, hload 24 (by decide)]
        dsimp only [m4, m3]
        rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (hap 24 32 (by decide)),
          memLoad_memStore_same _ _ _ (by decide) (by decide)]
      · show memLoad finalMem (fr.rdi + 8 + 24) 64 = w 3
        have ha : fr.rdi + 8 + 24 = fr.rdi + 32 := BitVec.add_assoc _ _ _
        rw [ha, hload 32 (by decide)]
        exact memLoad_memStore_same m3 (fr.rdi + 32) (w 3) (by decide) (by decide)

end K256.Proofs.ParseSignature.Scalar
