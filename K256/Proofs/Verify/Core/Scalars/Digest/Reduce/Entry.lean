import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Barrier
import K256.Proofs.Verify.Core.Scalars.Digest.Prepare
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3

namespace K256.Proofs.Verify.Core.Reduce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply ParseSignature

local macro "entry_addr" : tactic => `(tactic|
  (simp only [sp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow,
     Nat.reduceDiv] at *
   omega))

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
theorem entry {fr : Activation} {a : Registers} {w : Vector (BitVec 64) 4}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn109f80.frameAt .l109f80 fr))
    (src : Readable fr.original fr.rsi 32) (apart : Outside [callStack fr] fr.rsi 32)
    (words : WordsAt fr.original fr.rsi 64 w) :
    ∃ b m, Core.Reaches .l109f80 a fr.original .l10a053 b m ∧ Live fr w b m ∧
      b[0] = ⟨64,borrow w⟩ := by
  simp only [Fn109f80.frameAt, Fn109f80.frameAtG11, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp,df,rcx,rdx,rbx,rbp,rsi,rdi,r8,r9,r12,r13,r14,r15,mx,ft,fc,
    retRead,retMem,retLow,win,room,align,_⟩ := atoms
  have top := retRead.low
  have sep := apart.2 _ (List.mem_singleton_self _)
  dsimp only [callStack] at sep
  have included := fun x hx => Common.fnCode_subset_programImage x (code_l109f80 x hx)
  have inside (off : BitVec 64) (hd : off.toNat ≤ 97) (hb : 8 ≤ off.toNat) :
      InRegions [fr.region] (fr.rsp-off) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    dsimp only [InRegion,Activation.region]
    entry_addr
  have sourceWords {m : Ram} (frame : RamWriteFrame fr.original m [fr.region]) :
      WordsAt m fr.rsi 64 w := by
    apply words.of_frame frame (by decide)
    refine ⟨apart.1, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    dsimp only [Activation.region]
    omega
  let d := difference w
  let carry (i : Fin 4) := (~~~w[i] ||| d[i]) >>> 63
  have f0 := RamWriteFrame.refl fr.original [fr.region]
  let m1 := memStore fr.original (fr.rsp-8) (fr.rbp)
  have f1 : RamWriteFrame fr.original m1 [fr.region] :=
    f0.memStore (fr.rbp) (inside 8 (by decide) (by decide))
  let m2 := memStore m1 (fr.rsp-16) (fr.r15)
  have f2 : RamWriteFrame fr.original m2 [fr.region] :=
    f1.memStore (fr.r15) (inside 16 (by decide) (by decide))
  let m3 := memStore m2 (fr.rsp-24) (fr.r14)
  have f3 : RamWriteFrame fr.original m3 [fr.region] :=
    f2.memStore (fr.r14) (inside 24 (by decide) (by decide))
  let m4 := memStore m3 (fr.rsp-32) (fr.r13)
  have f4 : RamWriteFrame fr.original m4 [fr.region] :=
    f3.memStore (fr.r13) (inside 32 (by decide) (by decide))
  let m5 := memStore m4 (fr.rsp-40) (fr.r12)
  have f5 : RamWriteFrame fr.original m5 [fr.region] :=
    f4.memStore (fr.r12) (inside 40 (by decide) (by decide))
  let m6 := memStore m5 (fr.rsp-48) (fr.rbx)
  have f6 : RamWriteFrame fr.original m6 [fr.region] :=
    f5.memStore (fr.rbx) (inside 48 (by decide) (by decide))
  let m7 := memStore m6 (fr.rsp-56) (fr.rdi)
  have f7 : RamWriteFrame fr.original m7 [fr.region] :=
    f6.memStore (fr.rdi) (inside 56 (by decide) (by decide))
  let m8 := memStore m7 (fr.rsp-64) (d[0])
  have f8 : RamWriteFrame fr.original m8 [fr.region] :=
    f7.memStore (d[0]) (inside 64 (by decide) (by decide))
  let m9 := memStore m8 (fr.rsp-80) (carry 0)
  have f9 : RamWriteFrame fr.original m9 [fr.region] :=
    f8.memStore (carry 0) (inside 80 (by decide) (by decide))
  let m10 := memStore m9 (fr.rsp-80) (carry 1)
  have f10 : RamWriteFrame fr.original m10 [fr.region] :=
    f9.memStore (carry 1) (inside 80 (by decide) (by decide))
  let m11 := memStore m10 (fr.rsp-72) (d[2])
  have f11 : RamWriteFrame fr.original m11 [fr.region] :=
    f10.memStore (d[2]) (inside 72 (by decide) (by decide))
  let m12 := memStore m11 (fr.rsp-80) (carry 2)
  have f12 : RamWriteFrame fr.original m12 [fr.region] :=
    f11.memStore (carry 2) (inside 80 (by decide) (by decide))
  let m13 := memStore m12 (fr.rsp-80) (carry 3)
  have f13 : RamWriteFrame fr.original m13 [fr.region] :=
    f12.memStore (carry 3) (inside 80 (by decide) (by decide))
  have word0 : memLoad m7 fr.rsi 64 = w[0] := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using sourceWords f7 0 (by decide)
  have word1 : memLoad m9 (fr.rsi+8) 64 = w[1] := sourceWords f9 1 (by decide)
  have word2 : memLoad m10 (fr.rsi+16) 64 = w[2] := sourceWords f10 2 (by decide)
  have word3 : memLoad m12 (fr.rsi+24) 64 = w[3] := sourceWords f12 3 (by decide)
  have bit0 : memLoad m9 (fr.rsp-80) 64 = carry 0 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have bit1 : memLoad m10 (fr.rsp-80) 64 = carry 1 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have bit2 : memLoad m12 (fr.rsp-80) 64 = carry 2 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have bit3 : memLoad m13 (fr.rsp-80) 64 = carry 3 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have readBit0 : LoadOk m9 (fr.rsp-80) 8 :=
    LoadOk.of_offsets (win.of_frame f9).readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have readBit1 : LoadOk m10 (fr.rsp-80) 8 :=
    LoadOk.of_offsets (win.of_frame f10).readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have readBit2 : LoadOk m12 (fr.rsp-80) 8 :=
    LoadOk.of_offsets (win.of_frame f12).readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have readBit3 : LoadOk m13 (fr.rsp-80) 8 :=
    LoadOk.of_offsets (win.of_frame f13).readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have readWord0 : LoadOk m7 fr.rsi 8 :=
    LoadOk.of_offsets (src.of_frame f7) (addr_self _) (addr_self _) (by decide)
  have readWord1 : LoadOk m9 (fr.rsi+8) 8 :=
    LoadOk.of_offsets (src.of_frame f9) rfl (addr_self _) (by decide)
  have readWord2 : LoadOk m10 (fr.rsi+16) 8 :=
    LoadOk.of_offsets (src.of_frame f10) rfl (addr_self _) (by decide)
  have readWord3 : LoadOk m12 (fr.rsi+24) 8 :=
    LoadOk.of_offsets (src.of_frame f12) rfl (addr_self _) (by decide)
  have store0 : StoreOk Extracted.programImage fr.original (fr.rsp-8) 8 0x109f80 1 :=
    storeOk_of_codeRange (off := 0) ((win.of_frame f0).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store1 : StoreOk Extracted.programImage m1 (fr.rsp-16) 8 0x109f81 2 :=
    storeOk_of_codeRange (off := 1) ((win.of_frame f1).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store2 : StoreOk Extracted.programImage m2 (fr.rsp-24) 8 0x109f83 2 :=
    storeOk_of_codeRange (off := 3) ((win.of_frame f2).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store3 : StoreOk Extracted.programImage m3 (fr.rsp-32) 8 0x109f85 2 :=
    storeOk_of_codeRange (off := 5) ((win.of_frame f3).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store4 : StoreOk Extracted.programImage m4 (fr.rsp-40) 8 0x109f87 2 :=
    storeOk_of_codeRange (off := 7) ((win.of_frame f4).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store5 : StoreOk Extracted.programImage m5 (fr.rsp-48) 8 0x109f89 1 :=
    storeOk_of_codeRange (off := 9) ((win.of_frame f5).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store6 : StoreOk Extracted.programImage m6 (fr.rsp-56) 8 0x109f8e 5 :=
    storeOk_of_codeRange (off := 14) ((win.of_frame f6).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store7 : StoreOk Extracted.programImage m7 (fr.rsp-64) 8 0x109fa3 5 :=
    storeOk_of_codeRange (off := 35) ((win.of_frame f7).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store8 : StoreOk Extracted.programImage m8 (fr.rsp-80) 8 0x109fb5 5 :=
    storeOk_of_codeRange (off := 53) ((win.of_frame f8).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store9 : StoreOk Extracted.programImage m9 (fr.rsp-80) 8 0x109feb 5 :=
    storeOk_of_codeRange (off := 107) ((win.of_frame f9).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store10 : StoreOk Extracted.programImage m10 (fr.rsp-72) 8 0x10a009 5 :=
    storeOk_of_codeRange (off := 137) ((win.of_frame f10).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store11 : StoreOk Extracted.programImage m11 (fr.rsp-80) 8 0x10a01b 5 :=
    storeOk_of_codeRange (off := 155) ((win.of_frame f11).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store12 : StoreOk Extracted.programImage m12 (fr.rsp-80) 8 0x10a040 5 :=
    storeOk_of_codeRange (off := 192) ((win.of_frame f12).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have store13 : StoreOk Extracted.programImage m13 (fr.rsp-96) 8 0x10a04e 5 :=
    storeOk_of_codeRange (off := 206) ((win.of_frame f13).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) included (by decide +kernel)
  have write1 : memStore fr.original (fr.rsp-8) (fr.rbp) = m1 := rfl
  have write2 : memStore m1 (fr.rsp-16) (fr.r15) = m2 := rfl
  have write3 : memStore m2 (fr.rsp-24) (fr.r14) = m3 := rfl
  have write4 : memStore m3 (fr.rsp-32) (fr.r13) = m4 := rfl
  have write5 : memStore m4 (fr.rsp-40) (fr.r12) = m5 := rfl
  have write6 : memStore m5 (fr.rsp-48) (fr.rbx) = m6 := rfl
  have write7 : memStore m6 (fr.rsp-56) (fr.rdi) = m7 := rfl
  have write8 : memStore m7 (fr.rsp-64) ((0x402da1732fc9bebf : BitVec 64) + w[0]) = m8 := rfl
  have write9 : memStore m8 (fr.rsp-80) ((~~~w[0] ||| ((0x402da1732fc9bebf : BitVec 64) + w[0])) >>> 63) = m9 := rfl
  have write10 : memStore m9 (fr.rsp-80) ((~~~w[1] ||| ((0x4551231950b75fc5 : BitVec 64) + w[1] + ((0 : BitVec 64)-carry 0).sshiftRight 63)) >>> 63) = m10 := rfl
  have write11 : memStore m10 (fr.rsp-72) (((0 : BitVec 64)-carry 1).sshiftRight 63 + w[2] + 2) = m11 := rfl
  have write12 : memStore m11 (fr.rsp-80) ((~~~w[2] ||| (((0 : BitVec 64)-carry 1).sshiftRight 63 + w[2] + 2)) >>> 63) = m12 := rfl
  have write13 : memStore m12 (fr.rsp-80) ((~~~w[3] ||| (((carry 2-1) >>> 63) + w[3])) >>> 63) = m13 := rfl
  have rspBits : a[4].get 64 = fr.rsp := congrArg (Value.get 64) rsp
  have rbxBits : a[3].get 64 = fr.rbx := congrArg (Value.get 64) rbx
  have rbpBits : a[5].get 64 = fr.rbp := congrArg (Value.get 64) rbp
  have rsiBits : a[6].get 64 = fr.rsi := congrArg (Value.get 64) rsi
  have rdiBits : a[7].get 64 = fr.rdi := congrArg (Value.get 64) rdi
  have r12Bits : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have r13Bits : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have r14Bits : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have r15Bits : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  suffices h : ∃ (b : Registers) (m : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l109f80,a,fr.original⟩ =
      .call ⟨.l127d50,b,memStore m (fr.rsp-96) (0x10a053 : BitVec 64)⟩ (resume .l10a053 0x10a053) ∧
      b[4].get 64 = fr.rsp-96 ∧ Writable Extracted.programImage m (fr.rsp-97) 9 ∧
      (∀ (c : Registers) (n : Ram), c[4] = (⟨64,sp fr⟩ : Value) →
        c[0] = (⟨64, ((b[7].get 64).setWidth 8).setWidth 64⟩ : Value) →
        RamWriteFrame m n [scratch (sp fr)] →
        (∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
          c[i] = b[i]) → Live fr w c n ∧ c[0] = ⟨64,borrow w⟩) by
    obtain ⟨b,m,call,stack,window,cont⟩ := h
    have addr8 : sp fr - 8 = fr.rsp - 96 := by unfold sp; bv_omega
    have addr9 : sp fr - 9 = fr.rsp - 97 := by unfold sp; bv_omega
    rw [← addr8] at call stack
    rw [← addr9] at window
    obtain ⟨c,n,step,hsp,flag,frame,keep⟩ := barrier call stack window (by entry_addr) (by decide)
    exact ⟨c,n,step,cont c n hsp flag frame keep⟩
  refine ⟨?b,m13,?step,?stack,?window,?post⟩
  case step =>
    cfg_eval [rspBits, rbxBits, rbpBits, rsiBits, rdiBits, r12Bits, r13Bits, r14Bits, r15Bits, word0,
      word1, word2, word3, bit0, bit1, bit2, bit3, readBit0, readBit1, readBit2, readBit3, readWord0,
      readWord1, readWord2, readWord3, store0, store1, store2, store3, store4, store5, store6, store7,
      store8, store9, store10, store11, store12, store13, write1, write2, write3, write4, write5, write6,
      write7, write8, write9, write10, write11, write12, write13]
    rw [write8]
    simp only [word1, word2, word3, bit0, bit1, bit2, bit3, readBit0, readBit1, readBit2, readBit3,
      readWord1, readWord2, readWord3, store8, store9, store10, store11, store12, store13, write9,
      write10, write11, write12, write13, ite_true]
    rfl
  case stack => rfl
  case window => exact (win.of_frame f13).sub (by omega) (by omega)
  case post =>
    intro c n stack flag frame keep
    have wf : RamWriteFrame fr.original n [fr.region] := by
      refine f13.trans frame ?_
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_,List.mem_cons_self,?_⟩
      dsimp only [scratch,Activation.region]
      entry_addr
    have slot (off : BitVec 64) (bound : off.toNat ≤ 80) :
        memLoad n (fr.rsp-off) 64 = memLoad m13 (fr.rsp-off) 64 := by
      apply frame.memLoad_eq
      refine ⟨by entry_addr,fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      right
      dsimp only [scratch]
      entry_addr
    have returnSlot : memLoad n fr.rsp 64 = fr.ret := by
      apply Eq.trans _ retMem
      apply wf.memLoad_eq
      refine ⟨by entry_addr, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      right
      dsimp only [Activation.region]
      omega
    constructor
    · refine ⟨?_,wf,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp only [Fn109f80.frameAt,Fn109f80.frameAtG11,Atom.All,Atom.Holds]
        refine ⟨stack,(keep 22 (by decide)).trans df,(keep 39 (by decide)).trans mx,
          (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
          ?_,?_,?_,?_,?_,?_,?_,retRead.of_frame wf,returnSlot,retLow,win.of_frame wf,room,align,trivial⟩
        all_goals rw [slot _ (by decide)]
        all_goals simp (disch := store_disch) only [m13,m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,
          memLoad_memStore_same,memLoad_memStore_of_rangeApart]
      · intro ⟨i,hi⟩ h
        simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals rw [keep _ (by decide +revert)]
        all_goals first | rfl | exact congrArg Value.width rsi | exact congrArg Value.width r8 | exact congrArg Value.width r9
      · exact keep 14 (by decide)
      · exact keep 12 (by decide)
      · exact keep 5 (by decide)
      · exact keep 15 (by decide)
      · rw [show sp fr + 24 = fr.rsp-64 by unfold sp; bv_omega,slot _ (by decide)]
        simp (disch := store_disch) only [m13,m12,m11,m10,m9,m8,memLoad_memStore_same,memLoad_memStore_of_rangeApart] <;> rfl
      · exact keep 13 (by decide)
      · rw [show sp fr + 16 = fr.rsp-72 by unfold sp; bv_omega,slot _ (by decide)]
        simp (disch := store_disch) only [m13,m12,m11,memLoad_memStore_same,memLoad_memStore_of_rangeApart] <;> rfl
      · exact keep 3 (by decide)
    · have eq : carry 3 = borrow w := by
        dsimp only [borrow,Scalar.borrowChain]
        rw [BitVec.or_comm _ (~~~w[2])]
        rfl
      rw [flag]
      change (⟨64, ((((0 - carry 3) >>> 63).setWidth 8).setWidth 64)⟩ : Value) = _
      rw [eq,show borrow w = _ from Scalar.borrowChain_eq ..]
      split <;> rfl

end K256.Proofs.Verify.Core.Reduce
