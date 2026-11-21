import K256.Proofs.Signing.Composition.Attempt.Coordinates.Blocks
import K256.Proofs.Signing.Composition.Attempt.Coordinates.Memory
import K256.Proofs.Signing.Generator
import K256.Proofs.Signing.Transfer.Generator
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Verify.LIR.Fn106dd0.Frame

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

structure CoordinateMemory (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (m : Ram) : Prop extends LoopMemory s d msg st m where
  digest : WordsAt m (sp s+656) 64 (scalarWords (digestScalar msg))
  inverse : WordsAt m (sp s+424) 64 (scalarWords (Curve.inverse domain.n k))

structure CoordinateRegisters (s : RamState) (a : Registers) (bx : BitVec 64) : Prop where
  rsp : a[4] = ⟨64,sp s⟩
  df : a[22] = ⟨1,0⟩
  rbx : a[3] = ⟨64,bx⟩
  rbp : a[5] = ⟨64,sp s+192⟩
  r12 : a[12] = ⟨64,sp s+8⟩
  r13 : a[13] = ⟨64,sp s+656⟩
  r14 : a[14].width = 64
  r15 : a[15] = ⟨64,sp s+456⟩
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16

theorem subcallApart {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (g : StackBounds s) :
    (sp s - 8).toNat ≤ 0x203de0 ∨ 0x203e28 + 9768 ≤ (sp s - 8).toNat := by
  have ro : Verify.LIR.rodataSection ∈ Extracted.programSections := by
    simp [Verify.LIR.rodataSection, Extracted.programSections]
  have span := Verify.LIR.Fn106dd0.callSlots_span ro
  have mem : Stack.region s signingKeyTrySign.minStackBytes ∈ writtenRegions signingKeyTrySign s := by
    simp [writtenRegions]
  have apart := apart_of_avoids (lo := 0x203dd0) (hi := 0x203e28) (call.separation.2 _ mem).1
    (fun a h₁ h₂ => by
      obtain ⟨b,hb⟩ := span a h₁ h₂
      exact Or.inl ⟨b,Common.programSections_fetchByte_of_mem hb⟩)
    (by rw [stackRegion call]; change 0 < 11200; decide) (by decide) (by decide)
  rw [stackRegion call, show stackPtr s - 11192 = sp s - 9904 by unfold sp; bv_omega] at apart
  have nat8 : (sp s - 8).toNat = (sp s).toNat - 8 := g.below 8 (by decide)
  have nat9904 : (sp s - 9904).toNat = (sp s).toNat - 9904 := g.below 9904 (by decide)
  change (sp s - 9904).toNat + 11200 ≤ 0x203dd0 ∨ 0x203e28 ≤ (sp s - 9904).toNat at apart
  have := g.room
  omega

abbrev coordinateActivation (s : RamState) (b : Registers) (n : Ram) (depth : Nat) (tag : BitVec 64)
    (bx src dst : BitVec 64) : Activation :=
  { activation s n b depth tag with
    rbx := bx
    rbp := sp s+192
    rdi := dst
    rsi := src
    r12 := sp s+8
    r13 := sp s+656
    r15 := sp s+456 }

theorem activationRegisters {s : RamState} {b : Registers} {n : Ram} {depth tag bx src dst}
    {out : Output Value Ram Reg.count}
    (h : Atom.All Extracted.programImage out.values out.store
      (Generate.LIR.Fn10ee80.doneAt (coordinateActivation s b n depth tag bx src dst))) :
    CoordinateRegisters s out.values bx := by
  obtain ⟨rsp,df,rbx,rbp,r12,r13,r14,r15,mx,ft,fc,_⟩ := h
  change out.values[4] = ⟨64,sp s-8+8⟩ at rsp
  rw [BitVec.sub_add_cancel] at rsp
  exact ⟨rsp,df,rbx,rbp,r12,r13,
    congrArg Value.width r14,r15,congrArg Value.width mx,congrArg Value.width ft,congrArg Value.width fc⟩

theorem smallFrameOutside {s : RamState} (g : StackBounds s) {rs : List MemoryRegion}
    (past : ∀ r ∈ rs, r.start + r.size ≤ (sp s).toNat + 424)
    (off : BitVec 64) (n : Nat) (lo : 424 ≤ off.toNat) (hi : off.toNat + n ≤ 1296) :
    Outside rs (sp s+off) n :=
  g.outside off n hi fun r hr => Or.inr (by have := past r hr; omega)

theorem CoordinateMemory.preserve {s : RamState} {secret msg : ByteArray} {d k : Nat} {st : State}
    {m n : Ram} {rs : List MemoryRegion} (g : StackBounds s)
    (call : ValidCall signingKeyTrySign s [secret,msg]) (h : CoordinateMemory s d msg st k m)
    (writes : RamWriteFrame m n rs)
    (lower : ∀ r ∈ rs, (sp s).toNat - 9904 ≤ r.start)
    (upper : ∀ r ∈ rs, r.start + r.size ≤ (sp s).toNat + 344) : CoordinateMemory s d msg st k n := by
  have outside := smallFrameOutside g (rs := rs) (fun r hr => by have := upper r hr; omega)
  exact ⟨h.toLoopMemory.preserveCoordinates g call writes lower (fun r hr => Or.inl (upper r hr)),
    h.digest.of_frame writes (by decide) (outside 656 32 (by decide) (by decide)),
    h.inverse.of_frame writes (by decide) (outside 424 32 (by decide) (by decide))⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem multiplyNonce {s : RamState} {secret msg : ByteArray} {d k : Nat} {st : State}
    {a : Registers} {m : Ram} (call : ValidCall signingKeyTrySign s [secret,msg])
    (h : ScalarsReady s d msg st k a m) (pos : 0 < k) (bound : k < domain.n) :
    ∃ b n, Reach (core .l105b23 a m) (core .l105b62 b n) ∧
      CoordinateRegisters s b (sp s+624) ∧ CoordinateMemory s d msg st k n ∧
      Generate.Generator.Affine.ProjectiveAt n (sp s+8) (Generate.Curve.generatorWindow k) := by
  let p := sp s
  have pEq : p.toNat = (sp s).toNat := rfl
  let w := scalarWords (Curve.inverse domain.n k)
  let m1 := memStore m (p+424) w[0]
  let m2 := memStore m1 (p+432) w[1]
  let m3 := memStore m2 (p+440) w[2]
  let m4 := inverseCopy m p w
  let pushed := memStore m4 (p-8) (0x105b62 : BitVec 64)
  let rs : List MemoryRegion := [⟨(p-8).toNat,8⟩,⟨(p+424).toNat,32⟩]
  let g := StackBounds.ofCall call
  have bottom := g.room
  have high := g.high
  have nat8 : (p-8).toNat = p.toNat-8 := g.below 8 (by decide)
  have nat9776 : (p-9776).toNat = p.toNat-9776 := g.below 9776 (by decide)
  have ag (i : BitVec 64) (hi : i.toNat ≤ 1296) : (p+i).toNat = p.toNat+i.toNat := g.above i hi
  have slot (i : BitVec 64) (n : Nat) (bound : i.toNat+n ≤ 1296) :
      Writable Extracted.programImage m (p+i) n := by
    apply g.slot call h.toMemory <;> rw [ag i (by omega)] <;> omega
  have slotPush : Writable Extracted.programImage m (p-8) 8 :=
    g.slot call h.toMemory (by rw [nat8]; omega) (by rw [nat8]; omega)
  have save {x : Ram} (f : RamWriteFrame m x rs) (i : BitVec 64)
      (lo : 424 ≤ i.toNat) (hi : i.toNat+8 ≤ 456) (v : BitVec 64) :
      RamWriteFrame m (memStore x (p+i) v) rs := by
    apply f.memStore
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change (p+424).toNat ≤ (p+i).toNat ∧ (p+i).toNat+8 ≤ (p+424).toNat+32 ∧
      (p+i).toNat+8 ≤ 2^64
    rw [ag i (by omega), g.above 424 (by decide)]
    change p.toNat + 424 ≤ p.toNat+i.toNat ∧ p.toNat+i.toNat+8 ≤ p.toNat+424+32 ∧ _
    omega
  have f1 : RamWriteFrame m m1 rs := save (.refl _ _) 424 (by decide) (by decide) _
  have f2 : RamWriteFrame m m2 rs := save f1 432 (by decide) (by decide) _
  have f3 : RamWriteFrame m m3 rs := save f2 440 (by decide) (by decide) _
  have f4 : RamWriteFrame m m4 rs := save f3 448 (by decide) (by decide) _
  have fp : RamWriteFrame m pushed rs := by
    apply f4.memStore
    refine ⟨_,List.mem_cons_self,?_⟩
    change (p-8).toNat ≤ (p-8).toNat ∧ (p-8).toNat+8 ≤ (p-8).toNat+8 ∧ (p-8).toNat+8 ≤ 2^64
    exact ⟨Nat.le_refl _,Nat.le_refl _,by omega⟩
  have outside (i : BitVec 64) (n : Nat) (fit : i.toNat+n ≤ 1296)
      (sep : i.toNat+n ≤ 424 ∨ 456 ≤ i.toNat) : Outside rs (p+i) n :=
    g.outside i n fit (by
      intro r hr
      simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · right
        change (p-8).toNat+8 ≤ p.toNat+i.toNat
        omega
      · have off : (p+424).toNat = p.toNat+424 := g.above 424 (by decide)
        change _ ≤ (p+424).toNat ∨ (p+424).toNat+32 ≤ _
        rcases sep with h | h
        · left; omega
        · right; omega)
  have guard {x : Ram} (f : RamWriteFrame m x rs) (addr : BitVec 64) (n j len : Nat)
      (fits : addr.toNat+n ≤ 1296) (covered : j+len ≤ LIR.bytes_l105b23.length) :=
    ParseSignature.storeOk_of_codeRange (off := j) ((slot addr n fits).of_frame f)
      (fun y hy => Common.fnCode_subset_programImage y (LIR.code_l105b23 y hy)) covered
  have pushOk : StoreOk Extracted.programImage m4 (p-8) 8 0x105b5d 5 :=
    ParseSignature.storeOk_of_codeRange (off := 58) (slotPush.of_frame f4)
      (fun y hy => Common.fnCode_subset_programImage y (LIR.code_l105b23 y hy)) (by decide)
  have l0 : LoadOk m (p+8) 8 := ⟨(slot 8 8 (by decide)).readable.low,(slot 8 8 (by decide)).readable.present⟩
  have l1 : LoadOk m (p+16) 8 := ⟨(slot 16 8 (by decide)).readable.low,(slot 16 8 (by decide)).readable.present⟩
  have l2 := ((slot 24 8 (by decide)).of_frame f2).readable
  have l3 := ((slot 32 8 (by decide)).of_frame f3).readable
  have v0 : memLoad m (p+8) 64 = w[0] := by
    simpa only [p,w,wordAddr,Nat.reduceDiv,Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
      using h.inverse 0 (by decide)
  have v1 : memLoad m (p+16) 64 = w[1] := by
    rw [show p+16 = wordAddr (sp s+8) 64 1 by change p+16 = p+8+8; bv_omega]
    exact h.inverse 1 (by decide)
  have v2 : memLoad m2 (p+24) 64 = w[2] := by
    rw [f2.memLoad_eq (outside 24 8 (by decide) (by decide))]
    rw [show p+24 = wordAddr (sp s+8) 64 2 by change p+24 = p+8+16; bv_omega]
    exact h.inverse 2 (by decide)
  have v3 : memLoad m3 (p+32) 64 = w[3] := by
    rw [f3.memLoad_eq (outside 32 8 (by decide) (by decide))]
    rw [show p+32 = wordAddr (sp s+8) 64 3 by change p+32 = p+8+24; bv_omega]
    exact h.inverse 3 (by decide)
  obtain ⟨b, block, b4,b6,b7,b1,keep⟩ := generatorCall
    (congrArg (Value.get 64) h.rsp) (congrArg (Value.get 64) h.rbx) (congrArg (Value.get 64) h.r12)
    l0 v0 l1 v1 (guard (.refl m rs) 424 8 10 8 (by decide) (by decide)) rfl
    (guard f1 432 8 18 8 (by decide) (by decide)) rfl ⟨l2.low,l2.present⟩ v2
    (guard f2 440 8 31 8 (by decide) (by decide)) rfl ⟨l3.low,l3.present⟩ v3
    (guard f3 448 8 44 8 (by decide) (by decide)) rfl pushOk
  have memory : LoopMemory s d msg st pushed := h.toLoopMemory.preserveCoordinates g call fp (by
    intro r hr
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change _ ≤ (p-8).toNat; omega
    · change _ ≤ (p+424).toNat
      rw [g.above 424 (by decide)]; omega) (by
    intro r hr
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · left
      change (p-8).toNat+8 ≤ _
      omega
    · right
      change _ ≤ (p+424).toNat ∧ (p+424).toNat+32 ≤ _
      rw [g.above 424 (by decide)]
      change p.toNat+424 ≤ p.toNat+424 ∧ p.toNat+424+32 ≤ p.toNat+592
      omega)
  have copied : WordsAt pushed (p+424) 64 w := by
    have moved (i : Nat) (hi : i < 4) : memLoad pushed (wordAddr (p+424) 64 i) 64 = w[i] := by
      have h := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
      rcases h with rfl | rfl | rfl | rfl <;>
        simp (disch := store_disch) only [pushed,m4,inverseCopy,wordAddr,Nat.reduceDiv,Nat.reduceMul,
          BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,
          memLoad_memStore_of_rangeApart,memLoad_memStore_same]
    exact moved
  have before : CoordinateMemory s d msg st k pushed :=
    ⟨memory, h.digest.of_frame fp (by decide) (outside 656 32 (by decide) (by decide)),copied⟩
  let fr := coordinateActivation s b pushed 9768 0x105b62 (p+624) (p+624) (p+8)
  have image := memory.toMemory.image call
  have got := Generate.LIR.Fn10ee80.callSlots_loaded
    (sections := Extracted.programSections) (by simp [Generate.LIR.rodataSection, Extracted.programSections]) image
  obtain ⟨read1, val1⟩ := got (0x203de0,0x129770) (by decide)
  obtain ⟨read2, val2⟩ := got (0x203e20,0x100a20) (by decide)
  have low : fr.low = p-9776 := by change p-8-9768 = p-9776; bv_omega
  have localStack : Writable Extracted.programImage pushed (fr.rsp-9768) 9768 :=
    g.slot call memory.toMemory (by rw [show fr.rsp-9768 = p-9776 from low,nat9776]; omega)
      (by rw [show fr.rsp-9768 = p-9776 from low,nat9776]; omega)
  have addr8 : (p+8).toNat = p.toNat+8 := g.above 8 (by decide)
  have addr624 : (p+624).toNat = p.toNat+624 := g.above 624 (by decide)
  have rq : fr.rsp.toNat = p.toNat-8 := nat8
  have apart : (p-8).toNat ≤ 0x203de0 ∨ 0x203e28+9768 ≤ (p-8).toNat := subcallApart call g
  have al := g.alignment
  have atom : Atom.All Extracted.programImage b pushed (Generate.LIR.Fn10ee80.frameAt .l10ee80 fr) := by
    simp only [Generate.LIR.Fn10ee80.frameAt,Generate.LIR.Fn10ee80.frameAtG1,Atom.All,Atom.Holds]
    refine ⟨b4,(keep 22 (by decide)).trans h.df,?_,?_,(keep 3 (by decide)).trans h.rbx,
      (keep 5 (by decide)).trans h.rbp,b6,b7,?_,?_,(keep 12 (by decide)).trans h.r12,
      (keep 13 (by decide)).trans h.r13,?_,(keep 15 (by decide)).trans h.r15,?_,?_,?_,
      (slotPush.of_frame fp).readable,memLoad_memStore_same _ _ _ (by decide) (by decide),
      by change (0x105b62 : Nat) < 2^32; decide,localStack,?_,?_,read1,val1,read2,val2,?_,trivial⟩
    · exact value_eq (congrArg Value.width b1)
    · exact value_eq ((congrArg Value.width (keep 2 (by decide))).trans (h.widths 2 (by decide)))
    · exact value_eq ((congrArg Value.width (keep 8 (by decide))).trans (h.widths 8 (by decide)))
    · exact value_eq ((congrArg Value.width (keep 9 (by decide))).trans (h.widths 9 (by decide)))
    · exact value_eq ((congrArg Value.width (keep 14 (by decide))).trans h.r14)
    · exact value_eq ((congrArg Value.width (keep 39 (by decide))).trans h.fp.1)
    · exact value_eq ((congrArg Value.width (keep 50 (by decide))).trans h.fp.2.1)
    · exact value_eq ((congrArg Value.width (keep 51 (by decide))).trans h.fp.2.2)
    · change fr.low.toNat + 9768 ≤ fr.rsp.toNat
      rw [show fr.low.toNat = p.toNat-9776 from congrArg BitVec.toNat low |>.trans nat9776,rq]
      omega
    · change fr.rsp.toNat % 16 = 8
      rw [rq]; omega
    · change 0x206450 ≤ (p-8).toNat ∨ (p-8).toNat ≤ 0x203de0
      omega
  have keptNonce := h.nonce.of_frame fp (by decide) (outside 624 32 (by decide) (by decide))
  have subRoom : 9768 ≤ fr.rsp.toNat := by rw [rq]; omega
  have subHigh : fr.rsp.toNat+664 ≤ 2^32 := by rw [rq]; omega
  have srcOffset : fr.rsi = fr.rsp+632 := by change p+624 = p-8+632; bv_omega
  have dstOffset : fr.rdi = fr.rsp+16 := by change p+8 = p-8+16; bv_omega
  obtain ⟨out, exec, tag, done, _, writes, point⟩ := Generator.nonceExecution (d := k) atom image
    subRoom rfl subHigh srcOffset dstOffset ((slot 624 32 (by decide)).of_frame fp).readable
    ((slot 8 120 (by decide)).of_frame fp) keptNonce pos bound
  have past : ∀ r ∈ [fr.region,⟨fr.rdi.toNat,120⟩], r.start+r.size ≤ p.toNat+344 := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change fr.low.toNat + (fr.rsp.toNat-fr.low.toNat) ≤ _
      rw [low,nat9776,rq]; omega
    · change (p+8).toNat+120 ≤ _
      omega
  have lower : ∀ r ∈ [fr.region,⟨fr.rdi.toNat,120⟩], p.toNat-9904 ≤ r.start := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change _ ≤ fr.low.toNat
      rw [low,nat9776]; omega
    · change _ ≤ (p+8).toNat
      omega
  exact ⟨out.values,out.store, callReaches block (Transfer.verifyExecAt (src := .l10ee80) rfl (Transfer.generator (dst := .l10ee80) List.mem_cons_self exec)) tag,
    activationRegisters done, before.preserve g call writes lower past,point⟩

end K256.Proofs.Signing.Composition.Attempt
