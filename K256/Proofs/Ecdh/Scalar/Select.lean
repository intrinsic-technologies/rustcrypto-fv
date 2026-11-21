import K256.Proofs.Ecdh.LIR.Fn10a220.Frame
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Ecdh.Scalar

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR

set_option maxHeartbeats 480000 in
set_option maxRecDepth 8192 in
theorem select_call {code : CodeMap}
    (hcode : ∀ x ∈ fnCode, x ∈ code) (fr : Activation)
    (choice : fr.rcx.setWidth 8 = 1)
    (left : Readable fr.original fr.rsi 32) (right : Readable fr.original fr.rdx 32)
    (dst : Writable code fr.original fr.rdi 32)
    (rightApart : Outside [fr.region] fr.rdx 32)
    (dstApart : Outside [ParseSignature.callStack fr] fr.rdi 32)
    (args : Values Value Reg.count)
    (entry : Atom.All code args fr.original (Fn10a220.frameInfo.entryAtoms fr)) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l10a220, args, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn10a220.frameInfo.doneAtoms fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ParseSignature.buffer fr.rdi 32] ∧
      ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 64
        (Vector.ofFn fun i : Fin 4 => memLoad fr.original (wordAddr fr.rdx 64 i.val) 64) := by
  change Atom.All code args fr.original (Fn10a220.frameAt .l10a220 fr) at entry
  simp only [Fn10a220.frameAt, Fn10a220.frameAtG1, Atom.All, Atom.Holds] at entry
  rcases entry with ⟨hsp, hdf, hcx, hdx, hbx, hbp, hsi, hdi, h8, h9, h12, h13, h14, h15,
    hmxcsr, hftw, hfcw, hread, hret, hretLow, hwrite, hroom, _, _⟩
  let slot := fr.rsp - 1
  let word (off : BitVec 64) := memLoad fr.original (fr.rdx + off) 64
  let saved := memStore fr.original slot (1 : BitVec 8)
  let m1 := memStore saved fr.rdi (word 0)
  let m2 := memStore m1 (fr.rdi + 8) (word 8)
  let m3 := memStore m2 (fr.rdi + 16) (word 16)
  let m4 := memStore m3 (fr.rdi + 24) (word 24)
  let regions := [fr.region, ParseSignature.buffer fr.rdi 32]
  have hslotNat : slot.toNat + 1 = fr.rsp.toNat := by
    dsimp only [slot]
    bv_omega
  have slotInside : InRegion fr.region slot 1 := by
    have := fr.rsp.isLt
    change fr.low.toNat ≤ slot.toNat ∧
      slot.toNat + 1 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ slot.toNat + 1 ≤ 2^64
    omega
  have savedFrame : RamWriteFrame fr.original saved [fr.region] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, slotInside⟩
  have rightLoad (off : BitVec 64) (h : off.toNat + 8 ≤ 32) :
      LoadOk saved (fr.rdx + off) 8 :=
    LoadOk.of_offsets (c := off) (d := 0) (right.of_frame savedFrame) rfl (addr_self _) (by
      simpa only [show off - (0 : BitVec 64) = off by bv_omega] using h)
  have rightValue (off : BitVec 64) (h : off.toNat + 8 ≤ 32) :
      memLoad saved (fr.rdx + off) 64 = word off := by
    apply savedFrame.memLoad_eq
    have hsum := right.low
    have ha : (fr.rdx + off).toNat = fr.rdx.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    rw [ha]
    rcases rightApart.2 r hr with h' | h' <;> omega
  have leftLoad (off : BitVec 64) (h : off.toNat + 8 ≤ 32) :
      LoadOk fr.original (fr.rsi + off) 8 :=
    LoadOk.of_offsets (c := off) (d := 0) left rfl (addr_self _) (by simpa only [show off - (0 : BitVec 64) = off by bv_omega] using h)
  have storeInCode {m : Ram} {addr : BitVec 64} {size : Nat}
      (w : Writable code m addr size) (off len : Nat)
      (bounds : off + len ≤ bytes_l10a220.length) :
      StoreOk code m addr size (0x10a220 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange w (fun x hx => hcode x (code_l10a220 x hx)) bounds
  have storeDest {m : Ram} (f : RamWriteFrame fr.original m regions)
      (d : BitVec 64) (off len : Nat) (fits : d.toNat + 8 ≤ 32)
      (inside : off + len ≤ bytes_l10a220.length) :
      StoreOk code m (fr.rdi + d) 8 (0x10a220 + BitVec.ofNat 64 off) len :=
    storeInCode ((dst.of_frame f).of_offsets (c := d) (d := 0) rfl (addr_self _) (by
      simpa only [show d - (0 : BitVec 64) = d by bv_omega] using fits)) off len inside
  have destLow := dst.readable.low
  have destNat (d : BitVec 64) (fits : d.toNat + 8 ≤ 32) :
      (fr.rdi + d).toNat = fr.rdi.toNat + d.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have destInside (d : BitVec 64) (fits : d.toNat + 8 ≤ 32) :
      InRegions regions (fr.rdi + d) 8 := by
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change fr.rdi.toNat ≤ _ ∧ _ ≤ fr.rdi.toNat + 32 ∧ _ ≤ 2^64
    rw [destNat d fits]
    omega
  have f0 : RamWriteFrame fr.original saved regions :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self, slotInside⟩
  have f1 : RamWriteFrame fr.original m1 regions := by
    apply f0.memStore
    exact BitVec.add_zero fr.rdi ▸ destInside 0 (by decide)
  have f2 : RamWriteFrame fr.original m2 regions := f1.memStore _ (destInside 8 (by decide))
  have f3 : RamWriteFrame fr.original m3 regions := f2.memStore _ (destInside 16 (by decide))
  have f4 : RamWriteFrame fr.original m4 regions := f3.memStore _ (destInside 24 (by decide))
  have retOutside : Outside regions fr.rsp 8 := by
    have low := hread.low
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
      omega
    · rcases dstApart.2 (ParseSignature.callStack fr) (List.mem_singleton_self _) with hd | hd
      · right
        exact Nat.le_trans hd (Nat.le_of_succ_le hroom)
      · left
        change fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at hd
        change fr.rsp.toNat + 8 ≤ fr.rdi.toNat
        omega
  have retLoad : LoadOk m4 fr.rsp 8 :=
    let h := hread.of_frame f4
    ⟨h.low, h.present⟩
  have retValue : memLoad m4 fr.rsp 64 = fr.ret := (f4.memLoad_eq retOutside).trans hret
  have scratchLoad : LoadOk saved slot 1 :=
    let h := hwrite.readable.of_frame savedFrame
    ⟨h.low, h.present⟩
  have scratchValue : memLoad saved slot 8 = 1 :=
    memLoad_memStore_same fr.original slot (1 : BitVec 8) (by decide) (by decide)
  have wScratch : StoreOk code fr.original slot 1 0x10a236 3 :=
    storeInCode hwrite 0x16 3 (by decide +kernel)
  have w0 : StoreOk code saved fr.rdi 8 0x10a267 3 := by
    exact BitVec.add_zero fr.rdi ▸ storeDest f0 0 0x47 3 (by decide) (by decide +kernel)
  have w1 : StoreOk code m1 (fr.rdi + 8) 8 0x10a26a 4 :=
    storeDest f1 8 0x4a 4 (by decide) (by decide +kernel)
  have w2 : StoreOk code m2 (fr.rdi + 16) 8 0x10a26e 4 :=
    storeDest f2 16 0x4e 4 (by decide) (by decide +kernel)
  have w3 : StoreOk code m3 (fr.rdi + 24) 8 0x10a272 4 :=
    storeDest f3 24 0x52 4 (by decide) (by decide +kernel)
  have l0 : LoadOk fr.original fr.rsi 8 := by
    exact BitVec.add_zero fr.rsi ▸ leftLoad 0 (by decide)
  have l1 := leftLoad 8 (by decide)
  have l2 := leftLoad 16 (by decide)
  have l3 := leftLoad 24 (by decide)
  have r0 : LoadOk saved fr.rdx 8 := by
    exact BitVec.add_zero fr.rdx ▸ rightLoad 0 (by decide)
  have r1 := rightLoad 8 (by decide)
  have r2 := rightLoad 16 (by decide)
  have r3 := rightLoad 24 (by decide)
  have v0 : memLoad saved fr.rdx 64 = word 0 := by
    exact BitVec.add_zero fr.rdx ▸ rightValue 0 (by decide)
  have v1 := rightValue 8 (by decide)
  have v2 := rightValue 16 (by decide)
  have v3 := rightValue 24 (by decide)
  have selectRight : (!(testFlags (1 : BitVec 8)).ZF.getD false) = true := by decide
  refine ⟨?out, .done ?execution, ?tag, ?atoms, ?frame, ?widths, ?post⟩
  case execution =>
    change program.step (dialect code) _ = _
    have spBits : args[4].get 64 = fr.rsp := congrArg (Value.get 64) hsp
    have cxBits : args[1].get 64 = fr.rcx := congrArg (Value.get 64) hcx
    have dxBits : args[2].get 64 = fr.rdx := congrArg (Value.get 64) hdx
    have siBits : args[6].get 64 = fr.rsi := congrArg (Value.get 64) hsi
    have diBits : args[7].get 64 = fr.rdi := congrArg (Value.get 64) hdi
    have stackBack : fr.rsp - (1 : BitVec 64) + 1 = fr.rsp := by bv_omega
    dsimp only [slot, saved] at scratchValue wScratch scratchLoad r0 r1 r2 r3 v0 v1 v2 v3
    dsimp only [slot, saved, m1, m2, m3, m4] at w0 w1 w2 w3 retLoad retValue
    cfg_eval [spBits, cxBits, dxBits, siBits, diBits, choice, scratchValue, wScratch,
      scratchLoad, l0, l1, l2, l3, r0, r1, r2, r3, v0, v1, v2, v3,
      w0, w1, w2, w3, retLoad, retValue, hretLow, selectRight, stackBack,
      and_self, ite_true]
    simp only [retValue, hretLow, and_self, ite_true]
    rfl
  case tag => rfl
  case atoms =>
    change Atom.All code _ _ (Fn10a220.doneAt fr)
    simp only [Fn10a220.doneAt, Atom.All, Atom.Holds]
    exact ⟨rfl, hdf, hbx, hbp, h12, h13, h14, h15, hmxcsr, hftw, hfcw, trivial⟩
  case frame => exact f4
  case widths =>
    intro ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case post =>
    have apart (a b : BitVec 64) (h : 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :
        RangeApart (fr.rdi + a) 8 (fr.rdi + b) 8 :=
      RangeApart.of_offsets rfl rfl h
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · change memLoad m4 (fr.rdi + 0) 64 = word 0
      dsimp only [m4, m3, m2]
      rw [memLoad_memStore_of_rangeApart m3 _ _ _ 64 (apart 24 0 (by decide)),
        memLoad_memStore_of_rangeApart m2 _ _ _ 64 (apart 16 0 (by decide)),
        memLoad_memStore_of_rangeApart m1 _ _ _ 64 (apart 8 0 (by decide))]
      rw [show fr.rdi + (0 : BitVec 64) = fr.rdi from BitVec.add_zero _]
      exact memLoad_memStore_same saved _ _ (by decide) (by decide)
    · change memLoad m4 (fr.rdi + 8) 64 = word 8
      dsimp only [m4, m3]
      rw [memLoad_memStore_of_rangeApart m3 _ _ _ 64 (apart 24 8 (by decide)),
        memLoad_memStore_of_rangeApart m2 _ _ _ 64 (apart 16 8 (by decide))]
      exact memLoad_memStore_same m1 _ _ (by decide) (by decide)
    · change memLoad m4 (fr.rdi + 16) 64 = word 16
      dsimp only [m4]
      rw [memLoad_memStore_of_rangeApart m3 _ _ _ 64 (apart 24 16 (by decide))]
      exact memLoad_memStore_same m2 _ _ (by decide) (by decide)
    · change memLoad m4 (fr.rdi + 24) 64 = word 24
      exact memLoad_memStore_same m3 _ _ (by decide) (by decide)

end K256.Proofs.Ecdh.Scalar
