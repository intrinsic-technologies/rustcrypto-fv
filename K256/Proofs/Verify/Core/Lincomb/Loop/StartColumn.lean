import K256.Proofs.Verify.Core.Lincomb.Loop.Column
import K256.Proofs.Verify.Core.Lincomb.Double
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Double

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Generator.Multiply.Lookup (copyGuard copyStored)

private abbrev slot (sp : BitVec 64) (off : Nat) := baseSp sp + BitVec.ofNat 64 off
private abbrev slotRegion (sp : BitVec 64) (off len : Nat) : MemoryRegion :=
  ⟨(slot sp off).toNat, len⟩
private abbrev doubleWrites (sp : BitVec 64) : List MemoryRegion :=
  [scratch (baseSp sp) 0x2a0, slotRegion sp 0x58 120, slotRegion sp 0x130 120]
private abbrev columnWrites (sp : BitVec 64) := [slotRegion sp 0x10 16]

private theorem baseNat {sp : BitVec 64} (room : 0x478 ≤ sp.toNat) :
    (baseSp sp).toNat = sp.toNat - 0x1d8 :=
  Recode.subNat (by change 0x1d8 ≤ sp.toNat; omega)

private theorem slotNat {sp : BitVec 64} (room : 0x478 ≤ sp.toNat) (low : sp.toNat + 8 ≤ 2^32)
    {off : Nat} (fits : off ≤ 0x1d8) :
    (slot sp off).toNat = sp.toNat - 0x1d8 + off := by
  rw [BitVec.toNat_add, baseNat room, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem slotWrite {a : Registers} {m n : Ram} {sp : BitVec 64}
    (entry : RoutineEntry a m sp 0x478) (frame : RamWriteFrame m n [scratch sp 0x478])
    {off len : Nat} (fits : off + len ≤ 0x1d8) :
    Writable Extracted.programImage n (slot sp off) len := by
  have room := entry.room
  have addr := slotNat room entry.returnSlot.low (off := off) (by omega)
  have beginAddr : (sp - (0x478 : BitVec 64)).toNat = sp.toNat - 0x478 :=
    Recode.subNat room
  apply (entry.stack.of_frame frame).sub
  · change (sp - (0x478 : BitVec 64)).toNat ≤ (slot sp off).toNat
    rw [addr, beginAddr]
    omega
  · change (slot sp off).toNat + len ≤ (sp - (0x478 : BitVec 64)).toNat + 0x478
    rw [addr, beginAddr]
    omega

private theorem withinScratch {sp : BitVec 64} {rs : List MemoryRegion}
    (h : ∀ r ∈ rs, sp.toNat - 0x478 ≤ r.start ∧ r.start + r.size ≤ sp.toNat) :
    RegionsWithin rs [scratch sp 0x478] := by
  intro r hr
  obtain ⟨lower, upper⟩ := h r hr
  exact ⟨_, .head _, lower, by change r.start + r.size ≤ sp.toNat - 0x478 + 0x478; omega⟩

private theorem doubleWithin {sp : BitVec 64} (room : 0x478 ≤ sp.toNat) (low : sp.toNat+8 ≤ 2^32) :
    RegionsWithin (doubleWrites sp) [scratch sp 0x478] := by
  apply withinScratch
  intro r hr
  simp only [doubleWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change sp.toNat-0x478 ≤ (baseSp sp).toNat-0x2a0 ∧
      (baseSp sp).toNat-0x2a0+0x2a0 ≤ sp.toNat
    rw [baseNat room]
    omega
  · change sp.toNat-0x478 ≤ (slot sp 0x58).toNat ∧ (slot sp 0x58).toNat+120 ≤ sp.toNat
    rw [slotNat room low (by decide)]
    omega
  · change sp.toNat-0x478 ≤ (slot sp 0x130).toNat ∧ (slot sp 0x130).toNat+120 ≤ sp.toNat
    rw [slotNat room low (by decide)]
    omega

private theorem outsideDouble {sp : BitVec 64} (room : 0x478 ≤ sp.toNat) (low : sp.toNat+8 ≤ 2^32)
    {off len : Nat} (fits : off + len ≤ 0x1d8)
    (temp : off + len ≤ 0x58 ∨ 0xd0 ≤ off)
    (acc : off + len ≤ 0x130 ∨ 0x1a8 ≤ off) :
    Outside (doubleWrites sp) (slot sp off) len := by
  have addr := slotNat room low (off := off) (by omega)
  refine ⟨by omega, fun r hr => ?_⟩
  simp only [doubleWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right
    change (baseSp sp).toNat - 0x2a0 + 0x2a0 ≤ _
    rw [baseNat room, addr]
    omega
  · change _ ≤ (slot sp 0x58).toNat ∨ (slot sp 0x58).toNat + 120 ≤ _
    rw [slotNat room low (off := 0x58) (by decide), addr]
    omega
  · change _ ≤ (slot sp 0x130).toNat ∨ (slot sp 0x130).toNat + 120 ≤ _
    rw [slotNat room low (off := 0x130) (by decide), addr]
    omega

private theorem outsideColumn {sp : BitVec 64} (room : 0x478 ≤ sp.toNat) (low : sp.toNat+8 ≤ 2^32)
    {off len : Nat} (fits : off + len ≤ 0x1d8) (apart : off + len ≤ 0x10 ∨ 0x20 ≤ off) :
    Outside (columnWrites sp) (slot sp off) len := by
  have addr := slotNat room low (off := off) (by omega)
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change _ ≤ (slot sp 0x10).toNat ∨ (slot sp 0x10).toNat + 16 ≤ _
  rw [slotNat room low (off := 0x10) (by decide), addr]
  omega

private theorem jumpColumn {l l' : Label} {a b : Registers} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨l',b,n⟩) :
    Reaches l a m l' b n :=
  .single (by simp only [Program.sem, Program.step, step, Transfer.next])

private theorem reachColumn {source target finish : Label} {a b c : Registers} {m n p : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨source,a,m⟩ = .jump ⟨target,b,n⟩)
    (rest : Reaches target b n finish c p) : Reaches source a m finish c p :=
  (jumpColumn step).trans rest

private structure BeforeCounter (a : Registers) (m : Ram) (sp table : BitVec 64)
    (value : Curve.Point) (k : Nat) (b : Registers) (n : Ram) : Prop where
  stack : b[4] = a[4]
  last : b[5] = a[5]
  count : b[3].get 64 = BitVec.ofNat 64 (k+1)
  front : b[13].get 64 = 0
  next : b[14].get 64 = table
  back : b[8] = ⟨64,0⟩
  control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]
  frame : RamWriteFrame m n (doubleWrites sp)
  point : ∃ p : Projective, p.Stored n (slot sp 0x130) ∧ p.valid ∧ p.value = value
  inactive : (memLoad n (slot sp 0x28) 8 &&& 1) = 0 → value = .infinity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem doubleAccumulator {a b : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {bases : Fin 4 → Curve.Point} {ds : Fin 4 → List Int} {k : Nat}
    (entry : RoutineEntry a m sp 0x478) (state : RoundState a m sp dst table bases ds (k+1) b n) :
    ∃ c store, Reaches .l110278 b n .l1102c2 c store ∧
      BeforeCounter b n sp table
        (Curve.add domain (suffix bases ds (k+1)) (suffix bases ds (k+1))) k c store := by
  let q := baseSp sp
  let child := q - 8
  let src := slot sp 0x130
  let tmp := slot sp 0x58
  let pushed := memStore n child (0x1102a0 : BitVec 64)
  have room := entry.room
  have low := entry.returnSlot.low
  have base := baseNat room
  have childEq : child = sp - 0x1e0 := by dsimp only [child, q, baseSp]; bv_omega
  have childNat : child.toNat = sp.toNat - 0x1e0 := by
    rw [childEq]
    exact Recode.subNat (by change 0x1e0 ≤ sp.toNat; omega)
  have srcNat : src.toNat = sp.toNat - 0x1d8 + 0x130 := slotNat room low (by decide)
  have tmpNat : tmp.toNat = sp.toNat - 0x1d8 + 0x58 := slotNat room low (by decide)
  have rsp : b[4].get 64 = q := congrArg (Value.get 64) state.rsp
  have df : b[22] = ⟨1,0⟩ := (state.control 22 (by decide)).trans entry.df
  have pushSlot : Writable Extracted.programImage n child 8 := by
    rw [childEq]
    exact (Recode.stackSlot entry (by decide) (by decide)).of_frame state.frame
  have pushGuard : StoreOk Extracted.programImage n (q - 8) 8 0x11029b 5 :=
    Recode.storeGuard (off := 25) pushSlot code_l110282 (by decide)
  have pushFrame : RamWriteFrame n pushed (doubleWrites sp) := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, .head _, ?_⟩
    change q.toNat-0x2a0 ≤ child.toNat ∧ child.toNat+8 ≤ q.toNat-0x2a0+0x2a0 ∧ child.toNat+8 ≤ 2^64
    rw [base,childNat]
    omega
  have pushedFrame := state.frame.trans pushFrame (doubleWithin room low)
  have onlyPush : RamWriteFrame n pushed [scratch q 8] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, .head _, ?_⟩
    change q.toNat-8 ≤ child.toNat ∧ child.toNat+8 ≤ q.toNat-8+8 ∧ child.toNat+8 ≤ 2^64
    rw [base,childNat]
    omega
  have srcPush : Outside [scratch q 8] src 120 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change q.toNat-8+8 ≤ src.toNat
    rw [base]
    omega
  have pushTag : memLoad pushed child 64 = 0x1102a0 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have flagRead : LoadOk n (q+0x28) 1 := by
    let w := (slotWrite entry state.frame (off := 0x28) (len := 1) (by decide)).readable
    exact ⟨w.low,w.present⟩
  obtain ⟨p, stored, valid, value⟩ := state.point
  let flag := memLoad n (q+0x28) 8 &&& 1
  have selection : ∃ c, Reaches .l110278 b n (if flag = 0 then .l1102c2 else .l110282) c n ∧
      c[3] = ⟨64,BitVec.ofNat 64 (k+1)⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,5,8,12,13,14,22,39,50,51] → c[i] = b[i]) := by
    have word : (memLoad n (q+0x28) 8 &&& 1) = flag := rfl
    by_cases h : flag = 0
    · have z : (flag == 0) = true := beq_iff_eq.mpr h
      rw [ite_eq_left h]
      refine ⟨?_, jumpColumn ?step, ?post⟩
      case step =>
        cfg_eval [rsp, state.counter, flagRead, testFlags, word, z]
        rfl
      case post =>
        refine ⟨rfl, ?_⟩
        rintro ⟨i,hi⟩ hi'
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
        rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · have z : (flag == 0) = false := beq_eq_false_iff_ne.mpr h
      rw [ite_eq_right h]
      refine ⟨?_, jumpColumn ?step, ?post⟩
      case step =>
        cfg_eval [rsp, state.counter, flagRead, testFlags, word, z]
        rfl
      case post =>
        refine ⟨rfl, ?_⟩
        rintro ⟨i,hi⟩ hi'
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
        rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨c,test,bx,keep⟩ := selection
  have controls (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : c[i] = b[i] :=
    keep i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] →
      i.val ∈ [4,5,8,12,13,14,22,39,50,51]) i hi)
  by_cases inactive : flag = 0
  · rw [ite_eq_left inactive] at test
    have identity := state.inactive inactive
    have doubledIdentity : Curve.add domain (suffix bases ds (k+1)) (suffix bases ds (k+1)) = .infinity := by
      rw [identity]; rfl
    refine ⟨c,n,test,⟨keep 4 (by decide),keep 5 (by decide),?_,?_,?_,
      (keep 8 (by decide)).trans state.back,controls,.refl _ _,?_,fun _ => doubledIdentity⟩⟩
    · exact congrArg (Value.get 64) bx
    · exact (congrArg (Value.get 64) (keep 13 (by decide))).trans state.front
    · exact (congrArg (Value.get 64) (keep 14 (by decide))).trans state.nextTable
    · exact ⟨p,stored,valid,value.trans (identity.trans doubledIdentity.symm)⟩
  · rw [ite_eq_right inactive] at test
    have csp : c[4].get 64 = q := (congrArg (Value.get 64) (keep 4 (by decide))).trans rsp
    have cfront : c[13].get 64 = 0 := (congrArg (Value.get 64) (keep 13 (by decide))).trans state.front
    have cnext : c[14].get 64 = table := (congrArg (Value.get 64) (keep 14 (by decide))).trans state.nextTable
    have cbp := (keep 5 (by decide)).trans state.tableEnd
    have call : ∃ d, program.runBlock (dialect Extracted.programImage) ⟨.l110282,c,n⟩ =
        .call ⟨.l110cd0,d,pushed⟩ (callResume .l1102a0 0x1102a0) ∧
        d[4] = ⟨64,child⟩ ∧ d[6].get 64 = src ∧ d[7].get 64 = tmp ∧
        d[3] = c[3] ∧ d[5] = c[5] ∧ d[12] = ⟨64,table⟩ ∧ d[13] = ⟨64,src⟩ ∧
        d[14] = ⟨64,0⟩ ∧ d[15].width = 64 ∧
        (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → d[i] = c[i]) := by
      refine ⟨?_, ?run, ?post⟩
      case run =>
        cfg_eval [csp, cfront, cnext, pushGuard]
        first | rfl | (rw [ite_eq_left pushGuard]; rfl)
      case post =>
        refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
        rintro ⟨i,hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl <;> rfl
    obtain ⟨d,call,dsp,dsi,ddi,d3,d5,d12,d13,d14,d15,dctrl⟩ := call
    have dcontrol (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : d[i] = a[i] :=
      (dctrl i hi).trans ((controls i hi).trans (state.control i hi))
    have ent : RoutineEntry d pushed child 0x298 := by
      refine ⟨dsp,?_,(dcontrol 22 (by decide)).trans entry.df,
        (congrArg Value.width (dcontrol 39 (by decide))).trans entry.mxcsr,
        (congrArg Value.width (dcontrol 50 (by decide))).trans entry.ftw,
        (congrArg Value.width (dcontrol 51 (by decide))).trans entry.fcw,?_,?_,?_,?_,?_,
        Recode.imageFromFrame entry pushedFrame⟩
      · rintro ⟨i,hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl
        · exact congrArg Value.width (d3.trans bx)
        · exact congrArg Value.width (d5.trans cbp)
        · exact congrArg Value.width d12
        · exact congrArg Value.width d13
        · exact congrArg Value.width d14
        · exact d15
      · have align := entry.aligned
        rw [childNat]
        omega
      · omega
      · have addr : child - BitVec.ofNat 64 0x298 = sp - 0x478 := by rw [childEq]; bv_omega
        rw [addr]
        change Writable _ pushed (sp - BitVec.ofNat 64 0x478) 0x298
        exact (entry.stack.of_frame pushedFrame).sub (Nat.le_refl _) (Nat.add_le_add_left (by decide) _)
      · exact pushSlot.readable.of_frame pushFrame
      · rw [pushTag]; decide
    have childSrc : Outside [scratch child 0x298, ⟨tmp.toNat,120⟩] src 120 := by
      refine ⟨by omega, fun r hr => ?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · right
        change child.toNat-0x298+0x298 ≤ src.toNat
        omega
      · exact Or.inr (by change tmp.toNat + 120 ≤ src.toNat; omega)
    have childTmp : Outside [scratch child 0x298, ⟨child.toNat,8⟩] tmp 120 := by
      refine ⟨by omega, fun r hr => ?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · right
        change child.toNat-0x298+0x298 ≤ tmp.toNat
        omega
      · exact Or.inr (by change child.toNat + 8 ≤ tmp.toNat; omega)
    obtain ⟨out,run,ret,doubled⟩ := Lincomb.double ent ddi dsi
      (slotWrite entry pushedFrame (off := 0x130) (by decide)).readable
      (slotWrite entry pushedFrame (off := 0x58) (by decide)) childSrc childTmp
      (stored.of_frame onlyPush srcPush) valid
    have childWithin : RegionsWithin [scratch child 0x298, ⟨tmp.toNat,120⟩] (doubleWrites sp) := by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_,.head _,?_,?_⟩
        all_goals dsimp only [scratch] ; rw [childNat,base] ; omega
      · exact ⟨_,.tail _ (.head _),Nat.le_refl _,Nat.le_refl _⟩
    have dblFrame := pushFrame.trans ret.frame childWithin
    have whole := state.frame.trans dblFrame (doubleWithin room low)
    have backAddr : slot sp 0 = q := Lift.add_zero_lit _
    have backWord : memLoad out.store q 64 = 0 := by
      have eq := dblFrame.memLoad_eq (k := 64) (outsideDouble room low (off := 0) (by decide) (by decide) (by decide))
      rw [backAddr] at eq
      exact eq.trans state.savedBack
    have backRead : LoadOk out.store q 8 := by
      rw [← backAddr]
      let w := (slotWrite entry whole (off := 0) (len := 8) (by decide)).readable
      exact ⟨w.low,w.present⟩
    have read8 : LoadOk out.store (q+8) 8 :=
      let w := (slotWrite entry whole (off := 8) (len := 8) (by decide)).readable
      ⟨w.low,w.present⟩
    have copy : RepMovsOk Extracted.programImage out.store 0 (q+0x58) src 15 8 0x1102bf 3 :=
      copyGuard (slotWrite entry whole (off := 0x58) (by decide)).readable
        (Recode.storeGuard (off := 31) (slotWrite entry whole (off := 0x130) (by decide)) code_l1102a0 (by decide))
        (Or.inl (by change tmp.toNat + 120 ≤ src.toNat; omega))
    have accepted := ret.tag.trans (congrArg (fun x => some (Value.mk 64 x)) pushTag)
    have path := reachesCall call run accepted
    have qRet : child + 8 = q := BitVec.sub_add_cancel _ _
    have osp : out.values[4] = ⟨64,q⟩ := ret.rsp.trans (congrArg (Value.mk 64) qRet)
    have ospBits : out.values[4].get 64 = q := congrArg (Value.get 64) osp
    have oSrc : out.values[13].get 64 = src :=
      congrArg (Value.get 64) ((ret.saved 13 (by decide)).trans d13)
    have oFront : out.values[14].get 64 = 0 :=
      congrArg (Value.get 64) ((ret.saved 14 (by decide)).trans d14)
    have oNext : out.values[12].get 64 = table :=
      congrArg (Value.get 64) ((ret.saved 12 (by decide)).trans d12)
    have odf : out.values[22].get 1 = 0 :=
      congrArg (Value.get 1) ((ret.saved 22 (by decide)).trans ((dctrl 22 (by decide)).trans ((controls 22 (by decide)).trans df)))
    let copied := memCopy out.store src tmp 120
    have copying : ∃ e, program.runBlock (dialect Extracted.programImage) ⟨.l1102a0,out.values,out.store⟩ =
        .jump ⟨.l1102c2,e,copied⟩ ∧ e[4] = b[4] ∧ e[5] = b[5] ∧
        e[3].get 64 = BitVec.ofNat 64 (k+1) ∧ e[13].get 64 = 0 ∧ e[14].get 64 = table ∧
        e[8] = ⟨64,0⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → e[i] = b[i]) := by
      refine ⟨?_,?run,?post⟩
      case run =>
        cfg_eval [ospBits, oSrc, oFront, oNext, odf, backRead, backWord, read8, copy, false_or]
        first | rfl | (rw [ite_eq_left copy]; rfl)
      case post =>
        refine ⟨osp.trans state.rsp.symm, (ret.saved 5 (by decide)).trans (d5.trans (keep 5 (by decide))),
          congrArg (Value.get 64) ((ret.saved 3 (by decide)).trans (d3.trans bx)),rfl,rfl,rfl,?_⟩
        have savedControl (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : out.values[i] = b[i] :=
          (ret.saved i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] →
            i.val ∈ [3,5,12,13,14,15,22,39,50,51]) i hi)).trans ((dctrl i hi).trans (controls i hi))
        rintro ⟨i,hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl
        · exact savedControl 22 (by decide)
        · exact savedControl 39 (by decide)
        · exact savedControl 50 (by decide)
        · exact savedControl 51 (by decide)
    obtain ⟨e,copyRun,e4,e5,e3,e13,e14,e8,ectrl⟩ := copying
    have copyIn : InRegions (doubleWrites sp) src 120 := by
      refine ⟨_, .tail _ (.tail _ (.head _)),Nat.le_refl _,Nat.le_refl _,by omega⟩
    have copiedFrame := Sec1.Wrapper.Copy.memCopy_frame (src := tmp) dblFrame copyIn
    obtain ⟨pValid,pValue⟩ := p.double_correct valid
    refine ⟨e,copied,test.trans (path.trans (jumpColumn copyRun)),
      ⟨e4,e5,e3,e13,e14,e8,ectrl,copiedFrame,⟨p.double,copyStored doubled,pValid,?_⟩,?_⟩⟩
    · rw [pValue,value]
    · intro zero
      have eq := copiedFrame.memLoad_eq (k := 8)
        (outsideDouble room low (off := 0x28) (by decide) (by decide) (by decide))
      change memLoad copied (q+0x28) 8 = memLoad n (q+0x28) 8 at eq
      change memLoad copied (q+0x28) 8 &&& 1 = 0 at zero
      rw [eq] at zero
      exact False.elim (inactive zero)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem startColumn {a b : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {bases : Fin 4 → Curve.Point} {ds : Fin 4 → List Int} {k : Nat}
    (entry : RoutineEntry a m sp 0x478) (bound : k < 129)
    (nonzero : table ≠ 0) (read : Readable m table 0x1340)
    (state : RoundState a m sp dst table bases ds (k+1) b n) :
    ∃ c store, Reaches .l110278 b n .l11034e c store ∧
      Column a m sp dst table k (Curve.add domain (suffix bases ds (k+1)) (suffix bases ds (k+1))) c store ∧
      Cursor sp table 0 0 c store := by
  obtain ⟨c,prefixStore,prefixRun,atCounter⟩ := doubleAccumulator entry state
  let q := baseSp sp
  let counter := BitVec.ofNat 64 k
  let counted := memStore prefixStore (q+0x10) counter
  let staged := memStore counted (q+0x18) (memLoad counted (q+0xd8) 64)
  let final := memStore staged (q+0x18) (table+0x780)
  have room := entry.room
  have low := entry.returnSlot.low
  have whole := state.frame.trans atCounter.frame (doubleWithin room low)
  have hereNat : (q+0x10).toNat = sp.toNat-0x1d8+0x10 := slotNat room low (off := 0x10) (by decide)
  have writes (off : Nat) (fits : 0x10 ≤ off ∧ off + 8 ≤ 0x20) :
      InRegions (columnWrites sp) (slot sp off) 8 := by
    have addr := slotNat room low (off := off) (by omega)
    refine ⟨_,.head _,?_⟩
    change (q+0x10).toNat ≤ (slot sp off).toNat ∧
      (slot sp off).toNat+8 ≤ (q+0x10).toNat+16 ∧ (slot sp off).toNat+8 ≤ 2^64
    rw [addr,hereNat]
    omega
  have countFrame : RamWriteFrame prefixStore counted (columnWrites sp) :=
    (RamWriteFrame.refl _ _).memStore _ (writes 0x10 (by decide))
  have stageFrame : RamWriteFrame prefixStore staged (columnWrites sp) :=
    countFrame.memStore _ (writes 0x18 (by decide))
  have finalFrame : RamWriteFrame prefixStore final (columnWrites sp) :=
    stageFrame.memStore _ (writes 0x18 (by decide))
  have within : RegionsWithin (columnWrites sp) [scratch sp 0x478] := by
    apply withinScratch
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change sp.toNat-0x478 ≤ (q+0x10).toNat ∧ (q+0x10).toNat+16 ≤ sp.toNat
    omega
  have countWhole := whole.trans countFrame within
  have stageWhole := whole.trans stageFrame within
  have finalWhole := whole.trans finalFrame within
  have countWrite : StoreOk Extracted.programImage prefixStore (q+0x10) 8 0x1102cd 5 :=
    Recode.storeGuard (off := 11) (slotWrite entry whole (off := 0x10) (by decide)) code_l1102c2 (by decide)
  have stageWrite : StoreOk Extracted.programImage counted (q+0x18) 8 0x1102e5 5 :=
    Recode.storeGuard (off := 13) (slotWrite entry countWhole (off := 0x18) (by decide)) code_l1102d8 (by decide)
  have digitWrite : StoreOk Extracted.programImage staged (q+0x18) 8 0x110337 5 :=
    Recode.storeGuard (off := 7) (slotWrite entry stageWhole (off := 0x18) (by decide)) code_l110330 (by decide)
  have load {mem : Ram} (fr : RamWriteFrame m mem [scratch sp 0x478])
      (off : Nat) (fits : off + 8 ≤ 0x1d8) : LoadOk mem (slot sp off) 8 :=
    let rd := (slotWrite entry fr fits).readable
    ⟨rd.low,rd.present⟩
  have read48 : LoadOk counted (q+0x48) 8 := load countWhole 0x48 (by decide)
  have readD8 : LoadOk counted (q+0xd8) 8 := load countWhole 0xd8 (by decide)
  have read50 : LoadOk staged (q+0x50) 8 := load stageWhole 0x50 (by decide)
  have read20 : LoadOk staged (q+0x20) 8 := load stageWhole 0x20 (by decide)
  have rsp : c[4] = ⟨64,q⟩ := atCounter.stack.trans state.rsp
  have rspBits : c[4].get 64 = q := congrArg (Value.get 64) rsp
  have last : c[5] = ⟨64,table + 0x1340⟩ := atCounter.last.trans state.tableEnd
  have lastBits : c[5].get 64 = table + 0x1340 := by
    rw [last]
    rfl
  have small : (BitVec.ofNat 64 (k+1)).toNat = k+1 := Nat.mod_eq_of_lt (by omega)
  have dec : BitVec.ofNat 64 (k+1) - 1 = counter := by
    dsimp only [counter]
    rw [Nat.add_comm k 1, BitVec.ofNat_add]
    bv_omega
  have cf : (cmpSpec (BitVec.ofNat 64 (k+1)) 0x101).CF = true := by
    rw [cmpSpec_CF, small]
    exact decide_eq_true (by change k+1 < 0x101; omega)
  have unequal : (table == table+0x1340) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have high := read.low
    have same := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change table.toNat + 0x1340 < 2^64; omega)] at same
    change table.toNat = table.toNat + 0x1340 at same
    omega
  have nz : (table == 0) = false := beq_eq_false_iff_ne.mpr nonzero
  have foldedCount : memStore prefixStore (q+0x10) counter = counted := rfl
  have foldedStage : memStore counted (q+0x18) (memLoad counted (q+0xd8) 64) = staged := rfl
  have route : ∃ e, Reaches .l1102c2 c prefixStore .l11034e e final ∧
      e[4] = ⟨64,q⟩ ∧ e[5] = ⟨64,table+0x1340⟩ ∧ e[8] = ⟨64,0⟩ ∧
      e[9] = ⟨64,counter⟩ ∧ e[3] = ⟨64,2⟩ ∧ e[12] = ⟨64,0⟩ ∧ e[13] = ⟨64,table⟩ ∧
      e[14] = ⟨64,table+0x9a0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → e[i] = c[i]) := by
    refine ⟨?_,?run,?post⟩
    case run =>
      refine reachColumn (target := .l1102d8) (b := ?_) (n := counted) ?edge ?_
      case edge =>
        cfg_eval [atCounter.count, rspBits, cf, dec, Bool.true_or, Bool.not_true, countWrite, foldedCount]
        rfl
      refine reachColumn (target := .l11031a) (b := ?_) (n := staged) ?edge ?_
      case edge =>
        cfg_eval [rspBits, foldedCount, read48, readD8, stageWrite, foldedStage, read50]
        rfl
      refine reachColumn (target := .l11037b) (b := ?_) (n := staged) ?edge ?_
      case edge =>
        cfg_eval [rspBits, foldedStage, read20]
        rfl
      refine reachColumn (target := .l110385) (b := ?_) (n := staged) ?edge ?_
      case edge =>
        cfg_eval [atCounter.front, testFlags]
        rfl
      refine reachColumn (target := .l11038a) (b := ?_) (n := staged) ?edge ?_
      case edge =>
        cfg_eval [atCounter.next, testFlags, BitVec.and_self, nz]
        rfl
      refine reachColumn (target := .l110330) (b := ?_) (n := staged) ?edge ?_
      case edge =>
        cfg_eval [atCounter.next, lastBits, cmpSpec_ZF, unequal]
        rfl
      apply jumpColumn
      cfg_eval [rspBits, atCounter.next, foldedStage, digitWrite]
      rfl
    case post =>
      refine ⟨rsp,last,atCounter.back,rfl,rfl,rfl,rfl,rfl,?_⟩
      rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨e,run,e4,e5,e8,e9,e3,e12,e13,e14,ectrl⟩ := route
  have preserved (off : Nat) (fits : off + 8 ≤ 0x1d8)
      (metadata : off+8 ≤ 0x10 ∨ 0x20 ≤ off) (temp : off+8 ≤ 0x58 ∨ 0xd0 ≤ off)
      (acc : off+8 ≤ 0x130 ∨ 0x1a8 ≤ off) :
      memLoad final (slot sp off) 64 = memLoad n (slot sp off) 64 :=
    (finalFrame.memLoad_eq (outsideColumn room low fits metadata)).trans
      (atCounter.frame.memLoad_eq (outsideDouble room low fits temp acc))
  have save (off : BitVec 64) (h : off.toNat ≤ 48) (h' : 8 ≤ off.toNat) :
      memLoad final (sp-off) 64 = memLoad n (sp-off) 64 := by
    let localOff := 0x1d8-off.toNat
    have ho : (BitVec.ofNat 64 localOff).toNat = localOff := Nat.mod_eq_of_lt (by dsimp only [localOff]; omega)
    have addr : slot sp localOff = sp-off := by
      apply BitVec.eq_of_toNat_eq
      rw [slotNat room low (by dsimp only [localOff]; omega), Recode.subNat (by omega)]
      dsimp only [localOff]
      omega
    rw [← addr]
    apply preserved <;> dsimp only [localOff] <;> omega
  have savedBack : memLoad final q 64 = 0 := by
    have eq := preserved 0 (by decide) (by decide) (by decide) (by decide)
    rw [show slot sp 0 = q from Lift.add_zero_lit _] at eq
    exact eq.trans state.savedBack
  have savedCounter : memLoad final (q+0x10) 64 = counter := by
    dsimp only [final, staged, counted]
    have apart : RangeApart (q+0x18) 8 (q+0x10) 8 :=
      RangeApart.of_offsets (x := q) rfl rfl (by decide)
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart,
      memLoad_memStore_of_rangeApart _ _ _ _ _ apart,
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
  have saved : SavedFrame a m sp dst e final := by
    refine ⟨e4,(preserved 0xd0 (by decide) (by decide) (by decide) (by decide)).trans state.dest,
      (save 48 (by decide) (by decide)).trans state.rbx,
      (save 40 (by decide) (by decide)).trans state.r12,
      (save 32 (by decide) (by decide)).trans state.r13,
      (save 24 (by decide) (by decide)).trans state.r14,
      (save 16 (by decide) (by decide)).trans state.r15,
      (save 8 (by decide) (by decide)).trans state.rbp,?_,finalWhole⟩
    intro i hi
    exact (ectrl i hi).trans ((atCounter.control i hi).trans (state.control i hi))
  refine ⟨e,final,prefixRun.trans run,⟨saved,e5,e8,e9,savedCounter,
    (preserved 0x40 (by decide) (by decide) (by decide) (by decide)).trans state.savedFront,
    (preserved 0x38 (by decide) (by decide) (by decide) (by decide)).trans state.savedNext,savedBack,?_,?_⟩,
    ⟨e3,e12,e13,e14,?_⟩⟩
  · obtain ⟨p,store,valid,value⟩ := atCounter.point
    exact ⟨p,store.of_frame finalFrame (outsideColumn room low (by decide) (by decide)),valid,value⟩
  · intro h
    apply atCounter.inactive
    rw [← finalFrame.memLoad_eq (k := 8) (outsideColumn room low (off := 0x28) (by decide) (by decide))]
    exact h
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Verify.Core.Lincomb.Loop
