import K256.Proofs.Signing.Nonce.Start.State
import K256.Proofs.Signing.Nonce.Initialize
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee

namespace K256.Proofs.Signing.Nonce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Standards.SECG.ECC
open Verify.Hash

namespace Start

private def orderArgument (sp : BitVec 64) (m : Ram) : Ram :=
  memStore m (sp - 8) (sp + 592)

private def extraArgument (sp : BitVec 64) (m : Ram) : Ram :=
  memStore (orderArgument sp m) (sp - 16) (0 : BitVec 64)

private def initializeMemory (sp : BitVec 64) (m : Ram) : Ram :=
  memStore (extraArgument sp m) (sp - 24) (0x10584e : BitVec 64)

private def initializeActivation (sp : BitVec 64) (a : Registers) (m : Ram) : Activation where
  original := initializeMemory sp m
  rsp := sp - 24
  ret := 0x10584e
  low := sp - 2232
  rbx := a[3].get 64
  rbp := a[5].get 64
  r12 := sp + 8
  r13 := sp + 256
  r14 := a[14].get 64
  r15 := a[15].get 64
  rdi := sp + 688
  rsi := sp + 8
  rdx := 32
  rcx := sp + 352
  r8 := 32
  r9 := 1
  mxcsr := a[39].get 32
  ftw := a[50].get 16
  fcw := a[51].get 16
  fs := default

private theorem registerOfWidth (v : Value) {w : Nat} (h : v.width = w) :
    v = ⟨w, v.get w⟩ := by
  cases v
  subst w
  simp only [Value.get_mk]

private theorem initializeBlock {a : Registers} {m : Ram} {sp : BitVec 64}
    {d : Nat} {message : ByteArray} (ready : Prepared a m sp d message)
    (first : StoreOk Extracted.programImage m (sp-8) 8 0x105846 1)
    (second : StoreOk Extracted.programImage (orderArgument sp m) (sp-16) 8 0x105847 2)
    (third : StoreOk Extracted.programImage (extraArgument sp m) (sp-24) 8 0x105849 5) :
    let fr := initializeActivation sp a m
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10581a,a,m⟩ =
      .call ⟨.l100ea0,b,fr.original⟩ ⟨.l10584e,#v[],rfl,some ⟨64,fr.ret⟩⟩ ∧
      b[4] = ⟨64,fr.rsp⟩ ∧ b[1] = ⟨64,fr.rcx⟩ ∧ b[2] = ⟨64,fr.rdx⟩ ∧
      b[6] = ⟨64,fr.rsi⟩ ∧ b[7] = ⟨64,fr.rdi⟩ ∧ b[8] = ⟨64,fr.r8⟩ ∧
      b[9] = ⟨64,fr.r9⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have getSp : a[4].get 64 = sp := congrArg (Value.get 64) ready.rsp
  have getSecret : a[12].get 64 = sp + 8 := congrArg (Value.get 64) ready.r12
  have step1 : sp - 8 - 8 = sp - 16 := by bv_omega
  have step2 : sp - 16 - 8 = sp - 24 := by bv_omega
  refine ⟨?_, ?run, ?post⟩
  case run =>
    simp only [orderArgument, extraArgument] at second third
    cfg_eval [getSp, getSecret, step1, step2]
    rw [ite_eq_left first, ite_eq_left second, ite_eq_left third]
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem bytesOutside {m n : Ram} {regions : List MemoryRegion} {a : BitVec 64}
    {len : Nat} {bytes : ByteArray} (h : (⟨a.toNat,len⟩ : MemoryRegion).HasBytes m bytes)
    (frame : RamWriteFrame m n regions) (outside : Outside regions a len) :
    (⟨a.toNat,len⟩ : MemoryRegion).HasBytes n bytes := by
  refine ⟨h.1, fun i => (frame.outside _ ?_).trans (h.2 i)⟩
  have size : bytes.size = len := h.1
  have hi := i.isLt
  have low := outside.1
  unfold Outside
  dsimp only
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, fun r hr => ?_⟩
  rcases outside.2 r hr with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem initializeSlotsApart {m : Ram} {sp : BitVec 64}
    (stack : Writable Extracted.programImage m (sp-2232) 3392)
    (base : (sp-2232).toNat = sp.toNat - 2232) (depth : 2232 ≤ sp.toNat)
    (limit : sp.toNat + 1160 < 2^32) :
    0x2046c8 ≤ sp.toNat - 24 ∨ sp.toNat - 24 ≤ 0x203dc8 := by
  apply Classical.byContradiction
  intro h
  let i := max (sp.toNat - 2232) 0x203dc8
  have iLow : 0x203dc8 ≤ i := Nat.le_max_right _ _
  have iHigh : i < 0x203e28 := by
    change max (sp.toNat - 2232) 0x203dc8 < 0x203e28
    omega
  have inside : sp.toNat - 2232 ≤ i := Nat.le_max_left _ _
  have upper : i < sp.toNat + 1160 := by
    change max (sp.toNat - 2232) 0x203dc8 < sp.toNat + 1160
    omega
  have aNat : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
  have ro : rodataSection ∈ Extracted.programSections := by
    simp [Extracted.programSections, rodataSection]
  obtain ⟨b, hb⟩ := Fn100ea0.callSlots_span ro (BitVec.ofNat 64 i)
    (by rw [aNat]; exact iLow) (by rw [aNat]; exact iHigh)
  apply stack.notCode (_, b) hb (i - (sp.toNat - 2232)) (by omega)
  change BitVec.ofNat 64 i = (sp-2232) + BitVec.ofNat 64 (i - (sp.toNat - 2232))
  rw [← ofNat_toNat_add, base, Nat.add_sub_cancel' inside]

theorem initializeCall {a : Registers} {m : Ram} {sp : BitVec 64} {d : Nat} {message : ByteArray}
    (ready : Prepared a m sp d message)
    (mxcsr : a[39].width = 32) (ftw : a[50].width = 16) (fcw : a[51].width = 16)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (stack : Writable Extracted.programImage m (sp-2232) 3392)
    (depth : 2232 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32) (align : sp.toNat % 16 = 0)
    (pos : 0 < d) (bound : d < domain.n) :
    ∃ b t, Reaches .l10581a a m .l10584e b t ∧ b[4] = ⟨64,sp-16⟩ ∧ b[22] = ⟨1,0⟩ ∧
      b[12] = ⟨64,sp+8⟩ ∧ b[13] = ⟨64,sp+256⟩ ∧ b[14].width = 64 ∧
      ParseSignature.ArgumentWidths b ∧
      (∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m t (initializationRegions sp) ∧
      (⟨(sp+352).toNat,32⟩ : MemoryRegion).HasBytes t (SHA256.hashBytes message) ∧
      WordsAt t (sp+592) 64 (scalarWords domain.n) ∧ memLoad t (sp+688) 64 = sp+592 ∧
      Initialize.StateAt t (sp+696) (initialNonceState d message) := by
  let fr := initializeActivation sp a m
  let writes : List MemoryRegion := [⟨(sp-2232).toNat,2232⟩,⟨(sp+688).toNat,72⟩]
  have subNat (i : Nat) (hi : i ≤ 2232) :
      (sp - BitVec.ofNat 64 i).toNat = sp.toNat - i := by
    have natI : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [natI]; omega)), natI]
  have addNat (i : Nat) (hi : i ≤ 1160) :
      (sp + BitVec.ofNat 64 i).toNat = sp.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega), Nat.mod_eq_of_lt (show sp.toNat + i < 2^64 by omega)]
  have base : (sp-2232).toNat = sp.toNat - 2232 := subNat 2232 (by decide)
  have dstNat : (sp+688).toNat = sp.toNat + 688 := addNat 688 (by decide)
  have keyNat : (sp+696).toNat = sp.toNat + 696 := addNat 696 (by decide)
  have frRsp : fr.rsp.toNat = sp.toNat - 24 := subNat 24 (by decide)
  have frLow : fr.low.toNat = sp.toNat - 2232 := base
  have frDst : fr.rdi.toNat = sp.toNat + 688 := dstNat
  have frameOffset (i : Nat) (hi : 8 ≤ i) (hj : i ≤ 2232) :
      InRegions writes (sp - BitVec.ofNat 64 i) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    dsimp only [InRegion]
    rw [subNat i hj, base]
    exact ⟨by omega, by omega, by omega⟩
  have pushed : RamWriteFrame m fr.original writes := by
    change RamWriteFrame m (initializeMemory sp m) writes
    unfold initializeMemory extraArgument orderArgument
    exact ((((RamWriteFrame.refl m writes).memStore _ (frameOffset 8 (by decide) (by decide))).memStore _
      (frameOffset 16 (by decide) (by decide))).memStore _ (frameOffset 24 (by decide) (by decide)))
  have inStack : RamWriteFrame m fr.original [⟨(sp-2232).toNat,3392⟩] := by
    refine (RamWriteFrame.refl _ _).trans pushed ?_
    intro r hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Nat.le_refl _, by dsimp only; omega⟩
    · dsimp only
      rw [base, dstNat]
      exact ⟨by omega, by omega⟩
  have image' := Generate.Generator.Affine.Invert.Core.stackImage stack inStack image
  have stack' := stack.of_frame pushed
  have covered : ∀ x ∈ codeRange 0x10581a bytes_l10581a, x ∈ Extracted.programImage :=
    fun x h => Verify.Core.Affine.coreText x (code_l10581a x h)
  have w₁ : Writable Extracted.programImage m (sp-8) 8 :=
    stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have w₂ : Writable Extracted.programImage (orderArgument sp m) (sp-16) 8 :=
    (stack.memStore (sp-8) (sp+592 : BitVec 64)).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have w₃ : Writable Extracted.programImage (extraArgument sp m) (sp-24) 8 :=
    ((stack.memStore (sp-8) (sp+592 : BitVec 64)).memStore (sp-16) (0 : BitVec 64)).of_offsets
      (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨b, call, rsp, cx, dx, si, di, r8, r9, keep⟩ := initializeBlock ready
    (ParseSignature.storeOk_of_codeRange (off := 44) w₁ covered (by decide))
    (ParseSignature.storeOk_of_codeRange (off := 45) w₂ covered (by decide))
    (ParseSignature.storeOk_of_codeRange (off := 47) w₃ covered (by decide))
  have childLow : fr.rsp - 2208 = fr.low := by
    change sp - 24 - 2208 = sp - 2232
    bv_omega
  have childStack : Writable Extracted.programImage fr.original (fr.rsp-2208) 2208 := by
    rw [childLow]
    exact stack'.sub (Nat.le_refl _) (by omega)
  have childWindow : Writable Extracted.programImage fr.original fr.rsp 784 := by
    apply stack'.sub <;> rw [base, frRsp] <;> omega
  have childRet : memLoad fr.original fr.rsp 64 = fr.ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have slots := Fn100ea0.callSlots_loaded (sections := Extracted.programSections)
    (by simp [Extracted.programSections, rodataSection]) image'
  obtain ⟨read1,load1⟩ := slots (0x203dc8,0x12965d) (by decide)
  obtain ⟨read2,load2⟩ := slots (0x203dd0,0x12a820) (by decide)
  obtain ⟨read3,load3⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨read4,load4⟩ := slots (0x203e10,0x12a700) (by decide)
  obtain ⟨read5,load5⟩ := slots (0x203e20,0x100a20) (by decide)
  have entry : Atom.All Extracted.programImage b fr.original (Fn100ea0.frameAt .l100ea0 fr) := by
    simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds]
    exact ⟨rsp, (keep 22 (by decide)).trans ready.df, cx, dx,
      (keep 3 (by decide)).trans (registerOfWidth _ (ready.widths 3 (by decide))),
      (keep 5 (by decide)).trans (registerOfWidth _ (ready.widths 5 (by decide))),
      si, di, r8, r9, (keep 12 (by decide)).trans ready.r12, (keep 13 (by decide)).trans ready.r13,
      (keep 14 (by decide)).trans (registerOfWidth _ (ready.widths 14 (by decide))),
      (keep 15 (by decide)).trans (registerOfWidth _ (ready.widths 15 (by decide))),
      (keep 39 (by decide)).trans (registerOfWidth _ mxcsr),
      (keep 50 (by decide)).trans (registerOfWidth _ ftw),
      (keep 51 (by decide)).trans (registerOfWidth _ fcw),
      (childWindow.sub (Nat.le_refl _) (by omega)).readable, childRet,
      by change (0x10584e : Nat) < 2^32; decide,
      childStack, by rw [frLow, frRsp]; omega, by rw [frRsp]; omega, read1, load1,
      read2, load2, read3, load3, read4, load4, read5, load5,
      (by rw [frRsp]; exact initializeSlotsApart stack base depth limit), trivial⟩
  have outside (i : Nat) (hi : i ≤ 656) : Outside writes (sp+BitVec.ofNat 64 i) 32 := by
    refine ⟨by rw [addNat i (by omega)]; omega, fun r hr => ?_⟩
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      dsimp only
      rw [base, addNat i (by omega)]
      omega
    · left
      dsimp only
      rw [dstNat, addNat i (by omega)]
      omega
  have outsideSecret : Outside writes (sp+8) 32 := outside 8 (by decide)
  have outsideDigest : Outside writes (sp+352) 32 := outside 352 (by decide)
  have outsideOrder : Outside writes (sp+592) 32 := outside 592 (by decide)
  have pop8 : fr.rsp+8 = sp-16 := by change sp-24+8 = _; bv_omega
  have pop16 : fr.rsp+16 = sp-8 := by change sp-24+16 = _; bv_omega
  have orderAddress : fr.rsp + 616 = sp+592 := by change sp-24+616 = _; bv_omega
  have apart (i j : BitVec 64)
      (h : 8 ≤ ((0-j)-(0-i)).toNat ∧ 8 ≤ ((0-i)-(0-j)).toNat) :
      RangeApart (sp-i) 8 (sp-j) 8 :=
    RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) h
  have extraLen : memLoad fr.original (fr.rsp + 8) 64 = 0 := by
    rw [pop8]
    change memLoad (memStore (extraArgument sp m) (sp-24) (0x10584e : BitVec 64)) (sp-16) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 24 16 (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have orderPtr : memLoad fr.original (fr.rsp + 16) 64 = fr.rsp + 616 := by
    rw [pop16, orderAddress]
    change memLoad (memStore (memStore (orderArgument sp m) (sp-16) (0 : BitVec 64))
      (sp-24) (0x10584e : BitVec 64)) (sp-8) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 24 8 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 16 8 (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have childOrder : WordsAt fr.original (fr.rsp + 616) 64 (scalarWords domain.n) := by
    rw [orderAddress]
    exact ready.order.of_frame pushed (by decide) outsideOrder
  obtain ⟨out, run, tag, done, widths, changed, ptr, key, value⟩ := initializeGenerator
    entry image' (by rw [frRsp]; omega) childLow.symm (by rw [frRsp]; omega) childWindow
    (by change sp+688 = sp-24+712; bv_omega)
    (by change sp+8 = sp-24+32; bv_omega)
    (by change sp+352 = sp-24+376; bv_omega)
    rfl rfl rfl extraLen orderPtr childOrder (bytesOutside ready.secret pushed outsideSecret)
    (bytesOutside ready.digest pushed outsideDigest) pos bound
  have reach := Verify.Core.Affine.resumeCoreCall call run tag
  obtain ⟨outRsp,outDf,_,_,out12,out13,out14,_,outMx,outFt,outFc,_⟩ := done
  have kept : ∀ i : Fin Reg.count, i.val ∈ [39,50,51] → out.values[i] = a[i] := by
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact outMx.trans (registerOfWidth _ mxcsr).symm
    · exact outFt.trans (registerOfWidth _ ftw).symm
    · exact outFc.trans (registerOfWidth _ fcw).symm
  have final := pushed.trans changed (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨_, List.mem_cons_self, ?_⟩
      simp only [Activation.region, frRsp, frLow, base]
      exact ⟨Nat.le_refl _, by omega⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩)
  have frame : RamWriteFrame m out.store (initializationRegions sp) := by
    refine (RamWriteFrame.refl _ _).trans final ?_
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨_, List.mem_cons_self, ?_⟩
      dsimp only [initializationRegions]
      rw [base]
      exact ⟨Nat.le_refl _, by omega⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, .tail _ (.tail _ (.tail _ (.head _))), ?_⟩
      dsimp only [initializationRegions]
      rw [dstNat]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨out.values,out.store,reach,?_,outDf,out12,out13,congrArg Value.width out14,widths,kept,frame,
    bytesOutside ready.digest final outsideDigest, ready.order.of_frame final (by decide) outsideOrder,
    ptr.trans orderAddress, ?_⟩
  · rwa [pop8] at outRsp
  · constructor
    · simpa only [frDst, keyNat, Nat.add_assoc, Nat.reduceAdd] using key
    · simpa only [frDst, keyNat, Nat.add_assoc, Nat.reduceAdd] using value

end Start
end K256.Proofs.Signing.Nonce
