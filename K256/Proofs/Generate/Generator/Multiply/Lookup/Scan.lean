import K256.Proofs.Generate.Generator.Multiply.Lookup.Choice
import K256.Proofs.Generate.Generator.Multiply.Lookup.Digit
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Generate.Generator.Multiply.Lookup.SelectCall
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.ECC K256.Proofs.Common.Tactic

private def selectReturn : Nat → Label
  | 0 => .l11c574
  | 1 => .l11c5a3
  | 2 => .l11c5d5
  | 3 => .l11c607
  | 4 => .l11c639
  | 5 => .l11c66b
  | 6 => .l11c69d
  | _ => .l11c6d2

private theorem roundIndex {i : Nat} (h : i < 8) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega

private theorem scanReturnLow {i : Nat} (hi : i < 8) :
    (address (selectReturn i)).toNat < 2^32 ∧ (address (stage (i+1))).toNat < 2^32 := by
  rcases roundIndex hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private abbrev selectPreserved := [3, 5, 13, 14, 22, 39, 50, 51]

set_option hygiene false in
local macro "select_step" label:term " using " code:term : tactic =>
  `(tactic| (
    refine ⟨?_, ?run, ?post⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨$label, a, m⟩ = _
      arithmetic_segment using $code [rsp, table, acc, temporary, flag]
    case post =>
      refine ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · first | rfl | (change tablePtr = tablePtr + 0; bv_omega)
      · first | rfl | exact temporary
      · change (((a[0].get 64).setWidth 8).setWidth 64).setWidth 8 = _
        simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
          BitVec.setWidth_eq]
        exact (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans flag
      · intro ⟨j, hj⟩ keep
        simp only [selectPreserved, List.mem_cons, List.not_mem_nil, or_false] at keep
        rcases keep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · intro h
        first | rfl | omega))

set_option maxRecDepth 4096 in
private theorem selectStep {a : Registers} {m : Ram} {sp tablePtr accumulator temporaryPtr : Word}
    {i : Nat} (index : i < 8) (choiceFlag : Bool)
    (rsp : a[4].get 64 = sp) (table : a[15].get 64 = tablePtr)
    (acc : a[14].get 64 = accumulator) (tempEq : sp + 240 = temporaryPtr)
    (temporary : 0 < i → a[12].get 64 = temporaryPtr)
    (flag : a[0].get 8 = (if choiceFlag then 1 else 0))
    (push : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨stage i, a, m⟩ =
        .call ⟨.l10fcc0, b, memStore m (sp - 8) (address (selectReturn i))⟩
          (callFrame (selectReturn i) (address (selectReturn i))) ∧
      b[4].get 64 = sp - 8 ∧ b[6].get 64 = accumulator ∧
      b[2].get 64 = tablePtr + BitVec.ofNat 64 (120*i) ∧ b[7] = ⟨64,temporaryPtr⟩ ∧
      b[12].get 64 = temporaryPtr ∧ (b[1].get 64).setWidth 8 = (if choiceFlag then 1 else 0) ∧
      (∀ j : Fin Reg.count, j.val ∈ selectPreserved → b[j] = a[j]) ∧
      (i+1 < 8 → b[15] = a[15]) := by
  rcases roundIndex index with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have temporary : sp + (240 : Word) = temporaryPtr := tempEq
    select_step .l11c55b using code_l11c55b
  all_goals have temporary := temporary (by decide)
  · select_step .l11c591 using code_l11c591
  · select_step .l11c5c0 using code_l11c5c0
  · select_step .l11c5f2 using code_l11c5f2
  · select_step .l11c624 using code_l11c624
  · select_step .l11c656 using code_l11c656
  · select_step .l11c688 using code_l11c688
  · select_step .l11c6ba using code_l11c6ba

private abbrev copyPreserved := [3, 12, 14, 22, 39, 50, 51]
private abbrev nextPreserved := [5, 13, 15]

private theorem byte_sub_zero (x y : BitVec 8) : ((x - y) = 0) ↔ x = y := by bv_omega

private theorem magnitude_eq {n j : Nat} (hn : n < 256) (hj : j < 256) :
    (BitVec.ofNat 8 n = BitVec.ofNat 8 j) ↔ n = j := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hj]

private theorem magnitudeFlag {d : Int} {j : Nat} (dn : d.natAbs < 256) (hj : j < 8) :
    (if (cmpSpec (BitVec.ofNat 8 d.natAbs) (BitVec.ofNat 8 (j+1))).ZF then 1 else 0 : BitVec 8) =
      (if choice d j then 1 else 0) := by
  have jn : j + 1 < 256 := by omega
  simp only [choice, hj, ite_true, cmpSpec, subSpec, Bool.beq_eq_decide_eq, decide_eq_true_eq,
    byte_sub_zero, magnitude_eq dn jn]

set_option hygiene false in
local macro "copy_step" label:term " at " pc:term " using " code:term " comparing " count:term : tactic =>
  `(tactic| (
    have rep : RepMovsOk Extracted.programImage m 0 temporaryPtr sp 15 8 $pc 3 :=
      copyGuard source (by slot_guard using $code) apart
    have copiedPush : Writable Extracted.programImage (memCopy m sp temporaryPtr 120) (sp - 8) 8 :=
      push.memStore _ _
    refine ⟨?_, ?run, ?post⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨$label, a, m⟩ = _
      generate_block [rsp, direction, acc, temporary]
      refine Eq.trans (ite_eq_left (Or.inr rep)) ?_
      refine Eq.trans (ite_eq_left (by slot_guard using $code)) ?_
      rfl
    case post =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · first
        | change (mergeGPR 8 (if (cmpSpec ((a[13].get 64).setWidth 8) $count).ZF then 1 else 0)
              (0 : Word)).setWidth 8 = _
          rw [setWidth_mergeGPR8, abs64]
          exact magnitudeFlag absBound (by decide)
        | change (((mergeGPR 8 ((a[5].get 64).setWidth 8 >>> 7)
              (a[5].get 64)).setWidth 8).setWidth 64).setWidth 8 = _
          simp only [setWidth_mergeGPR8, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
            BitVec.setWidth_eq, digit64, sign, choice, Nat.reduceAdd, Nat.reduceLT, ite_false,
            decide_eq_true_eq]
      · intro ⟨j, hj⟩ keep
        simp only [copyPreserved, List.mem_cons, List.not_mem_nil, or_false] at keep
        rcases keep with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · intro active ⟨j, hj⟩ keep
        first
        | omega
        | simp only [nextPreserved, List.mem_cons, List.not_mem_nil, or_false] at keep
          rcases keep with rfl | rfl | rfl <;> rfl))

set_option maxRecDepth 4096 in
private theorem copyStep {a : Registers} {m : Ram} {sp temporaryPtr : Word}
    {i : Nat} (index : i < 8) (digit : Int)
    (rsp : a[4].get 64 = sp) (direction : a[22].get 1 = 0)
    (acc : a[14].get 64 = sp) (temporary : a[12].get 64 = temporaryPtr)
    (absByte : a[13].get 8 = BitVec.ofNat 8 digit.natAbs)
    (digitByte : a[5].get 8 = BitVec.ofInt 8 digit)
    (bounds : -8 ≤ digit ∧ digit ≤ 8)
    (source : Readable m temporaryPtr 120) (dest : Writable Extracted.programImage m sp 120)
    (apart : temporaryPtr.toNat + 120 ≤ sp.toNat ∨ sp.toNat + 120 ≤ temporaryPtr.toNat)
    (push : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨selectReturn i, a, m⟩ =
        .call ⟨.l127d50, b, memStore (memCopy m sp temporaryPtr 120) (sp - 8) (address (stage (i+1)))⟩
          (callFrame (stage (i+1)) (address (stage (i+1)))) ∧
      b[4].get 64 = sp - 8 ∧ (b[7].get 64).setWidth 8 = (if choice digit (i+1) then 1 else 0) ∧
      (∀ j : Fin Reg.count, j.val ∈ copyPreserved → b[j] = a[j]) ∧
      (i+1 < 8 → ∀ j : Fin Reg.count, j.val ∈ nextPreserved → b[j] = a[j]) := by
  have abs64 : (a[13].get 64).setWidth 8 = BitVec.ofNat 8 digit.natAbs :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans absByte
  have digit64 : (a[5].get 64).setWidth 8 = BitVec.ofInt 8 digit :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans digitByte
  have absBound : digit.natAbs < 256 := by omega
  have sign := (digitBytes digit bounds.1 bounds.2).2
  rcases roundIndex index with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · copy_step .l11c574 at 0x11c57f using code_l11c574 comparing 2
  · copy_step .l11c5a3 at 0x11c5ae using code_l11c5a3 comparing 3
  · copy_step .l11c5d5 at 0x11c5e0 using code_l11c5d5 comparing 4
  · copy_step .l11c607 at 0x11c612 using code_l11c607 comparing 5
  · copy_step .l11c639 at 0x11c644 using code_l11c639 comparing 6
  · copy_step .l11c66b at 0x11c676 using code_l11c66b comparing 7
  · copy_step .l11c69d at 0x11c6a8 using code_l11c69d comparing 8
  · copy_step .l11c6d2 at 0x11c6dd using code_l11c6d2 comparing 9

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem scanEntry {fr : Activation} {a : Registers} {m entry : Ram} {digit : Int}
    (i : Fin 8) {t next : Projective} (state : Scanning fr entry digit i.val a m t)
    (src : Readable entry fr.rsi 960) (above : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (bounds : -8 ≤ digit ∧ digit ≤ 8)
    (nextEntry : next.Stored entry (fr.rsi + BitVec.ofNat 64 (120*i.val))) :
    ∃ b n, Reaches (stage i.val) a m (stage (i.val+1)) b n ∧
      Scanning fr entry digit (i.val+1) b n (if digit.natAbs = i.val+1 then next else t) := by
  have atoms := state.atoms
  simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨spReg, direction, bx, _, _, _, _, _, _, _, _, _, retSlot, _, _, stack, lower, _, _⟩ := atoms
  let sp := fr.rsp - (408 : Word)
  let temp := fr.rsp - (168 : Word)
  let addr := fr.rsi + BitVec.ofNat 64 (120*i.val)
  have low : 496 ≤ fr.rsp.toNat := by omega
  have high := retSlot.low
  have toNat_sub (k : Word) (hk : k.toNat ≤ 496) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have spNat : sp.toNat = fr.rsp.toNat - 408 := toNat_sub 408 (by decide)
  have tempNat : temp.toNat = fr.rsp.toNat - 168 := toNat_sub 168 (by decide)
  have baseNat : (fr.rsp - 496).toNat = fr.rsp.toNat - 496 := toNat_sub 496 (by decide)
  have childBase : sp - 88 = fr.rsp - 496 := by dsimp only [sp]; bv_omega
  have pushBase : sp - 8 = fr.rsp - 416 := by dsimp only [sp]; bv_omega
  have choiceBase : sp - 8 - 1 = fr.rsp - 417 := by dsimp only [sp]; bv_omega
  have childNat : (sp - 88).toNat = fr.rsp.toNat - 496 := childBase ▸ baseNat
  have pushNat : (sp - 8).toNat = fr.rsp.toNat - 416 := pushBase ▸ toNat_sub 416 (by decide)
  have choiceNat : (sp - 8 - 1).toNat = fr.rsp.toNat - 417 := choiceBase ▸ toNat_sub 417 (by decide)
  have spTemp : sp + 240 = temp := by dsimp only [sp, temp]; bv_omega
  have spRead : Writable Extracted.programImage m sp 120 := by dsimp only [sp]; slot_state region
  have tempWrite : Writable Extracted.programImage m temp 120 := by dsimp only [temp]; slot_state region
  have push : Writable Extracted.programImage m (sp - 8) 8 := by rw [pushBase]; slot_state region
  have childStack : Writable Extracted.programImage m (sp - 88) 88 := by rw [childBase]; slot_state region
  have srcHigh := src.low
  have addrNat : addr.toNat = fr.rsi.toNat + 120*i.val := by
    have hi := i.isLt
    simp only [addr, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 120*i.val < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]
  have source : Readable m addr 120 := (src.of_frame state.writes).sub (by omega) (by have := i.isLt; omega)
  have original : next.Stored m addr := by
    apply nextEntry.of_frame state.writes
    change Outside [window fr] addr 120
    refine ⟨by have := source.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp - 496).toNat + 496 ≤ addr.toNat
    omega
  have byte (v : Value) : (v.get 64).setWidth 8 = v.get 8 :=
    BitVec.setWidth_setWidth_of_le _ (by decide)
  have flag : a[0].get 8 = (if choice digit i.val then 1 else 0) :=
    (byte _).symm.trans state.flag
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) spReg
  obtain ⟨b, call, childSp, left, right, childDst, temporary, flagSelect, saved, tableB⟩ :=
    selectStep i.isLt (choice digit i.val) rsp (state.table i.isLt) state.accumulator spTemp
      (fun h => state.temporary h i.isLt) flag push
  obtain ⟨retLow₁, retLow₂⟩ := scanReturnLow i.isLt
  have childDstGet : b[7].get 64 = temp := congrArg (Value.get 64) childDst
  have childDstWidth : b[7].width = 64 := congrArg Value.width childDst
  obtain ⟨c, m₁, step₁, top, calleeSaved, controls, _, point, frame₁⟩ :=
    resumeSelect (p := t) (q := next) (left := sp) (right := addr) (choice digit i.val) call childSp left right childDstGet
      childDstWidth flagSelect childStack (by omega) retLow₁ spRead.readable source tempWrite
      (Nat.le_refl _) (by omega) (by omega) state.stored original
  have keepC (j : Fin Reg.count) (h : j.val ∈ [3, 5, 13, 14]) :
      c[j] = ⟨64, a[j].get 64⟩ :=
    (calleeSaved j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)).trans
      (congrArg (fun v => Value.mk 64 (v.get 64))
        (saved j (by simp only [selectPreserved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)))
  have getC (j : Fin Reg.count) (h : j.val ∈ [3, 5, 13, 14]) :
      c[j].get 64 = a[j].get 64 :=
    (congrArg (Value.get 64) (keepC j h)).trans (Value.get_mk _ _)
  have tmpC : c[12].get 64 = temp :=
    (congrArg (Value.get 64) (calleeSaved 12 (by decide))).trans temporary
  have dirC : c[22].get 1 = 0 :=
    congrArg (Value.get 1) ((controls 22 (by decide)).trans ((saved 22 (by decide)).trans direction))
  have accC : c[14].get 64 = sp := (getC 14 (by decide)).trans state.accumulator
  have absC : c[13].get 8 = BitVec.ofNat 8 digit.natAbs :=
    (byte _).symm.trans ((congrArg (BitVec.setWidth 8) (getC 13 (by decide))).trans (state.magnitudeByte i.isLt))
  have digitC : c[5].get 8 = BitVec.ofInt 8 digit :=
    (byte _).symm.trans ((congrArg (BitVec.setWidth 8) (getC 5 (by decide))).trans (state.digitByte i.isLt))
  obtain ⟨d, choiceCall, choiceSp, choiceValue, copiedKeep, copiedNext⟩ :=
    copyStep (sp := sp) i.isLt digit (congrArg (Value.get 64) top) dirC accC tmpC absC digitC bounds
      (tempWrite.readable.of_frame frame₁) (spRead.of_frame frame₁) (Or.inr (by omega))
      (push.of_frame frame₁)
  let copied := memCopy m₁ sp temp 120
  let writes : List MemoryRegion := [⟨(fr.rsp - 496).toNat, 448⟩]
  have contain (r : MemoryRegion) (start : fr.rsp.toNat - 496 ≤ r.start)
      (finish : r.start + r.size ≤ fr.rsp.toNat - 48) :
      ∃ rr ∈ writes, rr.start ≤ r.start ∧ r.start + r.size ≤ rr.start + rr.size := by
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
    all_goals change _ ≤ _
    · change (fr.rsp - 496).toNat ≤ r.start
      omega
    · change r.start + r.size ≤ (fr.rsp - 496).toNat + 448
      omega
  have subset₁ : RegionsWithin [⟨(sp - 88).toNat,88⟩, ⟨temp.toNat,120⟩] writes := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> apply contain <;> dsimp only <;> omega
  have frameCopy : RamWriteFrame m copied writes := by
    apply Sec1.Wrapper.Copy.memCopy_frame ((RamWriteFrame.refl m writes).trans frame₁ subset₁)
    refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩
    · change (fr.rsp - 496).toNat ≤ sp.toNat
      omega
    · change sp.toNat + 120 ≤ (fr.rsp - 496).toNat + 448
      omega
    · omega
  have slot : Readable copied (sp - 8) 8 :=
    push.readable.of_frame frameCopy
  have tmpChoice : Writable Extracted.programImage copied (sp - 8 - 1) 1 := by
    rw [choiceBase]
    have win := stack.of_frame frameCopy
    slot_state region
  obtain ⟨e, n, step₂, top₂, flag₂, frame₂, kept₂⟩ :=
    resumeChoice (m := copied) (sp := sp) choiceCall choiceSp tmpChoice slot retLow₂
  have framePush : RamWriteFrame m (memStore copied (sp - 8) (address (stage (i.val+1)))) writes := by
    apply frameCopy.memStore
    refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩
    · change (fr.rsp - 496).toNat ≤ (sp - 8).toNat
      omega
    · change (sp - 8).toNat + 8 ≤ (fr.rsp - 496).toNat + 448
      omega
    · change (sp - 8).toNat + 8 ≤ 2^64
      omega
  have frame : RamWriteFrame m n writes := by
    apply framePush.trans frame₂
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    apply contain <;> dsimp only <;> omega
  have keepControls (j : Fin Reg.count) (h : j.val ∈ [22,39,50,51]) : e[j] = a[j] := by
    have h₁ : j.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega
    have h₂ : j.val ∈ copyPreserved := by
      simp only [copyPreserved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega
    have h₃ : j.val ∈ selectPreserved := by
      simp only [selectPreserved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega
    exact (kept₂ j h₁).trans ((copiedKeep j h₂).trans ((controls j h).trans (saved j h₃)))
  have bxC : c[3] = a[3] := by
    have hb : a[(3 : Fin Reg.count)] = ⟨64,fr.rdi⟩ := bx
    apply (keepC 3 (by decide)).trans
    rw [hb, Value.get_mk]
    exact bx.symm
  have keepFrame (j : Fin Reg.count) (h : j.val ∈ [3,4,22,39,50,51]) : e[j] = a[j] := by
    obtain ⟨j, hj⟩ := j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (kept₂ 3 (by decide)).trans ((copiedKeep 3 (by decide)).trans bxC)
    · exact top₂.trans spReg.symm
    · exact keepControls 22 (by decide)
    · exact keepControls 39 (by decide)
    · exact keepControls 50 (by decide)
    · exact keepControls 51 (by decide)
  have bytes (j : Fin Reg.count) (h : j.val ∈ nextPreserved) (hi : i.val+1 < 8) :
      e[j] = c[j] :=
    (kept₂ j (by simp only [nextPreserved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)).trans
      (copiedNext hi j h)
  have outputPoint : (if choice digit i.val then next else t).Stored n sp := by
    have atCopy : (if choice digit i.val then next else t).Stored copied sp := copyStored point
    have outside : Outside [⟨(sp-8).toNat,8⟩] sp 120 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      dsimp only
      omega
    have onlyPush : RamWriteFrame copied (memStore copied (sp - 8) (address (stage (i.val+1)))) [⟨(sp-8).toNat,8⟩] := by
      apply (RamWriteFrame.refl _ _).memStore
      refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, ?_⟩
      change (sp - 8).toNat + 8 ≤ 2^64
      omega
    apply (atCopy.of_frame onlyPush outside).of_frame frame₂
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only
    omega
  refine ⟨e, n, step₁.trans step₂, ?_⟩
  refine ⟨frameAtomsAfter state.atoms frame ?_ keepFrame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (fr.rsp - 496).toNat + 448 ≤ fr.rsp.toNat - 48
    omega
  · exact (congrArg (Value.get 64) ((kept₂ 14 (by decide)).trans (copiedKeep 14 (by decide)))).trans accC
  · intro _ _
    exact (congrArg (Value.get 64) ((kept₂ 12 (by decide)).trans (copiedKeep 12 (by decide)))).trans tmpC
  · intro hi
    calc
      e[15].get 64 = c[15].get 64 := congrArg (Value.get 64) (bytes 15 (by decide) hi)
      _ = b[15].get 64 :=
        (congrArg (Value.get 64) (calleeSaved 15 (by decide))).trans (Value.get_mk _ _)
      _ = a[15].get 64 := congrArg (Value.get 64) (tableB hi)
      _ = fr.rsi := state.table i.isLt
  · intro hi
    exact (congrArg (fun v => (v.get 64).setWidth 8) (bytes 5 (by decide) hi)).trans
      ((byte _).trans digitC)
  · intro hi
    exact (congrArg (fun v => (v.get 64).setWidth 8) (bytes 13 (by decide) hi)).trans
      ((byte _).trans absC)
  · rw [flag₂, Value.get_mk, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq]
    exact choiceValue
  · simpa only [choice, i.isLt, ite_true, decide_eq_true_eq] using outputPoint
  · apply state.writes.trans frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, by dsimp only [window]; omega⟩

end K256.Proofs.Generate.Generator.Multiply.Lookup
