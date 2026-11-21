import K256.Proofs.Verify.Core.Lincomb.Double.Setup
import K256.Proofs.Verify.Core.Lincomb.Double.StackFrame
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Repr

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Field Common.Point Common.Tactic
open Generate.Generator.Multiply.Lookup (copyGuard copyStored)
open Sec1.Affine.Uncompressed
open Generate.Generator.Multiply (Projective)

private def writeY (m : Ram) (q : BitVec 64) (ys : Limbs) : Ram :=
  memStore (memStore (memStore (memStore (memStore m (q + 0x150) ys[0])
    (q + 0x158) ys[1]) (q + 0x160) ys[2]) (q + 0x168) ys[3]) (q + 0x170) ys[4]

private theorem writeY_words {m : Ram} {q : BitVec 64} {ys : Limbs} :
    WordsAt (writeY m q ys) (q + 0x150) 64 ys := by
  have address (i : Nat) :
      wordAddr (q + 0x150) 64 i = q + (0x150 + BitVec.ofNat 64 (8*i)) :=
    BitVec.add_assoc _ _ _
  intro i hi
  rw [address]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · change memLoad (writeY m q ys) (q + 0x150) 64 = ys[0]
    unfold writeY
    segment_words []
  · change memLoad (writeY m q ys) (q + 0x158) 64 = ys[1]
    unfold writeY
    segment_words []
  · change memLoad (writeY m q ys) (q + 0x160) 64 = ys[2]
    unfold writeY
    segment_words []
  · change memLoad (writeY m q ys) (q + 0x168) 64 = ys[3]
    unfold writeY
    segment_words []
  · change memLoad (writeY m q ys) (q + 0x170) 64 = ys[4]
    exact memLoad_memStore_same _ _ _ rfl (by decide)

private theorem writeY_frame {m : Ram} {sp : BitVec 64} {ys : Limbs}
    (room : 0x298 ≤ sp.toNat) (high : sp.toNat ≤ 2^32)
    (bound : (bottom sp).toNat + 0x298 ≤ 2^32) :
    RamWriteFrame m (writeY m (localStack sp) ys) (windows sp [(448,40)]) := by
  have inside (k : Nat) (lo : 0x150 ≤ k) (hi : k + 8 ≤ 0x178) :
      InRegions (windows sp [(448,40)]) (localStack sp + BitVec.ofNat 64 k) 8 := by
    refine ⟨_, .head _, ?_⟩
    change (below sp 448).toNat ≤ _ ∧
      _ + 8 ≤ (below sp 448).toNat + 40 ∧ _ + 8 ≤ 2^64
    rw [stackOffset rfl room high (by omega), edgeNat bound (by decide)]
    have base := Recode.subNat (sp := sp) (off := 0x298) (by exact room)
    change (bottom sp).toNat = sp.toNat - 0x298 at base
    rw [base]
    omega
  have f := (RamWriteFrame.refl m _).memStore ys[0] (inside 0x150 (by decide) (by decide))
  have f := f.memStore ys[1] (inside 0x158 (by decide) (by decide))
  have f := f.memStore ys[2] (inside 0x160 (by decide) (by decide))
  have f := f.memStore ys[3] (inside 0x168 (by decide) (by decide))
  exact f.memStore ys[4] (inside 0x170 (by decide) (by decide))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
theorem finishArithmetic {initial : Registers} {a : Values Value 3504} {orig m : Ram} {sp dst : BitVec 64}
    {p : Projective} {w : PointWords}
    (entry : RoutineEntry initial orig sp 0x298)
    (rsp : a[4] = ⟨64, sp - 0x228⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → a[i.val]'(by have := i.isLt; change i.val < 53 at this; omega) = initial[i])
    (frame : RamWriteFrame orig m [scratch sp 0x298])
    (saved : ∀ i : Fin 6, let r := (#v[5,15,14,13,12,3] : Vector (Fin Reg.count) 6)[i]
      (⟨64, memLoad m (sp - BitVec.ofNat 64 (8*(i.val+1))) 64⟩ : Value) = initial[r])
    (destPtr : memLoad m (sp - 0x228 + 0x1a0) 64 = dst)
    (destWrite : Writable Extracted.programImage orig dst 120)
    (dest : Outside [scratch sp 0x298, ⟨sp.toNat, 8⟩] dst 120)
    (x : WordsAt m (sp - 0x228 + 0x128) 64 w.x)
    (z : WordsAt m (sp - 0x228 + 0x178) 64 w.z)
    (y : w.y = #v[a[3482].get 64 &&& a[3368].get 64,
      a[3488].get 64 &&& a[3368].get 64, a[3494].get 64 &&& a[3368].get 64,
      a[3500].get 64 &&& a[3368].get 64, (a[3502].get 64 >>> 52) + a[3474].get 64])
    (r9 : a[3456].width = 64)
    (repr : Projective.WordsRepr w p) :
    ∃ out, b_l110d64_81.eval (dialect Extracted.programImage) a m = .returned out ∧
      RoutineReturn initial orig sp 0x298 [⟨dst.toNat,120⟩] out ∧
      ParseSignature.ArgumentWidths out.values ∧ p.Stored out.store dst := by
  let q := localStack sp
  let src := q + 0x128
  let ys : Limbs := #v[a[3482].get 64 &&& a[3368].get 64,
    a[3488].get 64 &&& a[3368].get 64, a[3494].get 64 &&& a[3368].get 64,
    a[3500].get 64 &&& a[3368].get 64, (a[3502].get 64 >>> 52) + a[3474].get 64]
  let n := writeY m q ys
  let buffer : MemoryRegion := ⟨dst.toNat,120⟩
  let final := memCopy n dst src 120
  have room := entry.room
  have low := entry.returnSlot.low
  have bound : (bottom sp).toNat + 0x298 ≤ 2^32 := entry.stack.readable.low
  have yFrame : RamWriteFrame m n (windows sp [(448,40)]) :=
    writeY_frame room (by omega) bound
  have stackFrame : RamWriteFrame orig n [scratch sp 0x298] :=
    frame.trans yFrame (windowsWithin room bound (by decide))
  have belowAddr (k : Nat) : q + BitVec.ofNat 64 k = below sp (112 + k) := by
    simp only [q, localStack, below, bottom, BitVec.ofNat_add]
    bv_omega
  have apartY {k len : Nat} (fit : k + len ≤ 0x298)
      (apart : k + len ≤ 448 ∨ 488 ≤ k) :
      Outside (windows sp [(448,40)]) (below sp k) len := by
    apply outsideWindows bound fit (by decide)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact apart
  have xAfter : WordsAt n src 64 w.x :=
    x.of_frame yFrame (by decide) ((belowAddr 0x128).symm ▸ apartY (by decide) (by decide))
  have zAfter : WordsAt n (q + 0x178) 64 w.z :=
    z.of_frame yFrame (by decide) ((belowAddr 0x178).symm ▸ apartY (by decide) (by decide))
  have yAfter : WordsAt n (q + 0x150) 64 w.y :=
    y.symm ▸ (writeY_words (ys := ys) (m := m) (q := q))
  have point : p.Stored n src := by
    refine ⟨w.x, w.y, w.z, xAfter, ?_, ?_, repr.x, repr.y, repr.z⟩
    · rw [show src + 40 = q + 0x150 by dsimp only [src]; bv_omega]
      exact yAfter
    · rw [show src + 80 = q + 0x178 by dsimp only [src]; bv_omega]
      exact zAfter
  have dstApart : dst.toNat + 120 ≤ sp.toNat - 0x298 ∨ sp.toNat + 8 ≤ dst.toNat := by
    have outsideStack := dest.2 (scratch sp 0x298) (.head _)
    have outsideReturn := dest.2 (⟨sp.toNat, 8⟩ : MemoryRegion) (.tail _ (.head _))
    change dst.toNat + 120 ≤ sp.toNat - 0x298 ∨ sp.toNat - 0x298 + 0x298 ≤ dst.toNat at outsideStack
    change dst.toNat + 120 ≤ sp.toNat ∨ sp.toNat + 8 ≤ dst.toNat at outsideReturn
    omega
  have addrSub {k off : Nat} (h : k + off = 0x228) :
      q + BitVec.ofNat 64 k = sp - BitVec.ofNat 64 off := by
    have e := congrArg (BitVec.ofNat 64) h
    simp only [BitVec.ofNat_add] at e
    change sp - (0x228 : BitVec 64) + BitVec.ofNat 64 k = _
    bv_omega
  have srcAddr : src = sp - 0x100 := addrSub (by decide)
  have srcNat : src.toNat = sp.toNat - 0x100 := by
    rw [srcAddr]
    exact Recode.subNat (by change 0x100 ≤ sp.toNat; omega)
  have srcRead : Readable n src 120 := by
    rw [srcAddr]
    exact ((Recode.stackSlot entry (by decide) (by decide)).of_frame stackFrame).readable
  have copy : RepMovsOk Extracted.programImage n 0 src dst 15 8 0x112922 3 := by
    apply copyGuard srcRead
      (Recode.storeGuard (off := 0x50) (destWrite.of_frame stackFrame) code_l110d64_81 (by decide))
    rw [srcNat]
    rcases dstApart with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have copiedFrame : RamWriteFrame n final [buffer] :=
    Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
      ⟨buffer, .head _, Nat.le_refl _, Nat.le_refl _, dest.1⟩
  have finalFrame : RamWriteFrame orig final [scratch sp 0x298, buffer] := by
    have extended : RamWriteFrame orig n [scratch sp 0x298, buffer] :=
      ⟨fun x h => stackFrame.outside x ⟨h.1, fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact h.2 _ (.head _)⟩, stackFrame.present⟩
    apply extended.trans copiedFrame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨buffer, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  have pop (off : BitVec 64) (fit : off.toNat ≤ 48) (top : 8 ≤ off.toNat) :
      LoadOk final (sp - off) 8 :=
    let h := ((Recode.stackSlot entry (by omega) top).of_frame finalFrame).readable
    ⟨h.low, h.present⟩
  have dstRead : LoadOk n (q + 0x1a0) 8 := by
    rw [show q + 0x1a0 = sp - 0x88 from addrSub (by decide)]
    let h := ((Recode.stackSlot entry (off := 0x88) (len := 8)
      (by decide) (by decide)).of_frame stackFrame).readable
    exact ⟨h.low, h.present⟩
  have dstLoaded : memLoad n (q + 0x1a0) 64 = dst := by
    exact (yFrame.memLoad_eq ((belowAddr 0x1a0).symm ▸ apartY (by decide) (by decide))).trans destPtr
  have sameCopy (off : BitVec 64) (fit : off.toNat ≤ 48) :
      memLoad final (sp - off) 64 = memLoad n (sp - off) 64 := by
    have addr : (sp - off).toNat = sp.toNat - off.toNat := Recode.subNat (by omega)
    apply copiedFrame.memLoad_eq
    refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (sp - off).toNat + 8 ≤ dst.toNat ∨ dst.toNat + 120 ≤ (sp - off).toNat
    rw [addr]
    rcases dstApart with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have savedValue (i : Fin 6) :
      (⟨64, memLoad final (sp - BitVec.ofNat 64 (8*(i.val+1))) 64⟩ : Value) =
        initial[(#v[5,15,14,13,12,3] : Vector (Fin Reg.count) 6)[i]] := by
    have hi := i.isLt
    have address : sp - BitVec.ofNat 64 (8*(i.val+1)) = below sp (0x298 - 8*(i.val+1)) := by
      simp only [below, bottom]
      rw [← BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      bv_omega
    rw [sameCopy _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
    rw [address, yFrame.memLoad_eq (apartY (by omega) (Or.inr (by omega))), ← address]
    exact saved i
  have ret : memLoad final sp 64 = memLoad orig sp 64 := by
    have h := sameCopy 0 (by decide)
    rw [show sp - (0 : BitVec 64) = sp from BitVec.sub_zero _] at h
    exact h.trans (stackFrame.memLoad_eq (Recode.outsideReturn low room))
  have retRead : LoadOk final sp 8 := ⟨low, (entry.returnSlot.of_frame finalFrame).present⟩
  have rspGet : a[4].get 64 = q := congrArg (Value.get 64) rsp
  have df : a[22].get 1 = 0 := congrArg (Value.get 1) ((keep 22 (by decide)).trans entry.df)
  have window : Writable Extracted.programImage m (sp - 0x298) 0x298 := entry.stack.of_frame frame
  have stack3 : q + 0x1f8 = sp - 48 := addrSub (by decide)
  have stack12 : q + 0x200 = sp - 40 := addrSub (by decide)
  have stack13 : q + 0x208 = sp - 32 := addrSub (by decide)
  have stack14 : q + 0x210 = sp - 24 := addrSub (by decide)
  have stack5 : sp - 16 + 8 = sp - 8 := by bv_omega
  have stackEnd : sp - 16 + 16 = sp := by bv_omega
  have stackReturn : sp - 16 + 24 = sp + 8 := by bv_omega
  refine ⟨?_, ?run, ?post, ?widths, ?stored⟩
  case run =>
    arithmetic_prefix [rspGet, df, BitVec.add_zero, false_or]
    iterate 5
      refine Eq.trans (ite_eq_left ?_) ?_
      · slot_guard using code_l110d64_81
    have memoryEq :
        memStore
          (memStore
            (memStore
              (memStore
                (memStore m (q + 0x150) (a[3482].get 64 &&& a[3368].get 64))
                (q + 0x158) (a[3488].get 64 &&& a[3368].get 64))
              (q + 0x160) (a[3494].get 64 &&& a[3368].get 64))
            (q + 0x168) (a[3500].get 64 &&& a[3368].get 64))
          (q + 0x170) ((a[3502].get 64 >>> 52) + a[3474].get 64) = n := rfl
    have copy' : RepMovsOk Extracted.programImage n 0 (q + 0x128) dst 15 8 0x112922 3 := copy
    have final' : memCopy n dst (q + 0x128) 120 = final := rfl
    have pop3 : LoadOk final (q + 0x1f8) 8 := stack3.symm ▸ pop 48 (by decide) (by decide)
    have pop12 : LoadOk final (q + 0x200) 8 :=
      stack12.symm ▸ pop 40 (by decide) (by decide)
    have pop13 : LoadOk final (q + 0x208) 8 :=
      stack13.symm ▸ pop 32 (by decide) (by decide)
    have pop14 : LoadOk final (q + 0x210) 8 :=
      stack14.symm ▸ pop 24 (by decide) (by decide)
    simp only [memoryEq, dstRead, dstLoaded, copy', final', pop3, pop12, pop13, pop14, ite_true]
    have pre15 : q + 0x218 = sp - 16 := addrSub (by decide)
    change b_l110d64_82.eval (dialect Extracted.programImage) _ final = .returned _
    arithmetic_prefix
    simp only [Block.eval, Terminator.eval, Option.map_some, Fin.getElem_fin, ↓arithmeticRead, Value.get_mk,
      pre15, stack5, stackEnd, stackReturn, pop 16 (by decide) (by decide),
      pop 8 (by decide) (by decide), retRead, ret, entry.returnLow, and_self, ite_true]
    exact Eq.refl _
  case post =>
    refine ⟨?_, ?_, ?_, finalFrame⟩
    · rfl
    · simp only [Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead]
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead]
      · rw [stack3]
        exact savedValue 5
      · exact savedValue 0
      · rw [stack12]
        exact savedValue 4
      · rw [stack13]
        exact savedValue 3
      · rw [stack14]
        exact savedValue 2
      · exact savedValue 1
      · exact keep 22 (by decide)
      · exact keep 39 (by decide)
      · exact keep 50 (by decide)
      · exact keep 51 (by decide)
  case widths =>
    intro ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead] <;> exact r9
  case stored => exact copyStored point

end K256.Proofs.Verify.Core.Lincomb.Double
