import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update.State
import K256.Proofs.Verify.Core.Scalars.Inverse.LinearShift
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Choice
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)
open Generate.Generator.Affine.Invert.Core.Batch (signedAt_of_frame)
open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

private def callWrites (x : Word) : List MemoryRegion :=
  [⟨(x - 8).toNat, 8⟩, ⟨(x + 7).toNat, 1⟩, ⟨(x + 304).toNat, 32⟩]

private structure RowCall (c : Registers) (m : Ram) (x dst ret u v : Word) (n : Nat) : Prop where
  rsp : c[4] = ⟨64, x - 8⟩
  rdi : c[7] = ⟨64, x + dst⟩
  left : c[6].get 64 = x + 8
  right : c[2].get 64 = x + 48
  coeffLeft : c[1].get 64 = u
  coeffRight : c[8].get 64 = v
  shift : c[9].get 32 = BitVec.ofNat 32 (count n)
  returnAddr : memLoad m (x - 8) 64 = ret

private theorem shiftWide (n : Nat) :
    (BitVec.ofNat 32 (count n)).setWidth 64 = BitVec.ofNat 64 (count n) :=
  BitVec.setWidth_ofNat_of_le_of_lt (by decide) (Nat.lt_of_le_of_lt (Nat.min_le_left ..) (by decide))

local macro "row_controls" : tactic =>
  `(tactic| (
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h <;> subst i <;> rfl))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
private theorem firstRowCall {c : Registers} {m : Ram} {x : Word} {n : Nat} {w : Words}
    (rsp : c[4].get 64 = x) (rows : Rows c w) (k : c[9].get 32 = BitVec.ofNat 32 (count n))
    (lo : 8 ≤ x.toNat) (hi : x.toNat + 336 ≤ 2^32)
    (win : Writable Extracted.programImage m (x - 8) 344) :
    ∃ c' m', program.runBlock (dialect Extracted.programImage) ⟨.l1095c1, c, m⟩ =
      .call ⟨.l108890, c', m'⟩ (resumeAt .l10960c 0x10960c) ∧
      RowCall c' m' x 176 0x10960c w.u w.v n ∧ Rows c' w ∧
      c'[5] = ⟨64, BitVec.ofNat 64 (count n)⟩ ∧ Controls c c' ∧
      RamWriteFrame m m' (callWrites x) := by
  have narrow : (c[9].get 64).setWidth 32 = BitVec.ofNat 32 (count n) :=
    (setWidth_get _ (by decide)).trans k
  have u := congrArg (Value.get 64) rows.u
  have v := congrArg (Value.get 64) rows.v
  have wide := shiftWide n
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l1095c1, rsp, u, v, narrow, wide, resumeAt]
    segment_words [rsp, u, v, narrow, wide, resumeAt]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1095c1)
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, k, ?_⟩,
      ⟨rows.delta, rows.u, rows.v, rows.q, rows.r⟩, rfl, ?_, ?_⟩
    · lifted_word_reads []
      lifted_word_eq []
    · row_controls
    · unfold callWrites
      slot_state region

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
private theorem secondRowCall {c : Registers} {m : Ram} {x : Word} {n : Nat} {w : Words}
    (rsp : c[4].get 64 = x) (rows : Rows c w) (k : c[5] = ⟨64, BitVec.ofNat 64 (count n)⟩)
    (lo : 8 ≤ x.toNat) (hi : x.toNat + 336 ≤ 2^32)
    (win : Writable Extracted.programImage m (x - 8) 344) :
    ∃ c' m', program.runBlock (dialect Extracted.programImage) ⟨.l10960c, c, m⟩ =
      .call ⟨.l108890, c', m'⟩ (resumeAt .l109657 0x109657) ∧
      RowCall c' m' x 216 0x109657 w.q w.r n ∧ Rows c' w ∧
      c'[5] = ⟨64, BitVec.ofNat 64 (count n)⟩ ∧ Controls c c' ∧
      RamWriteFrame m m' (callWrites x) := by
  have shift := congrArg (Value.get 64) k
  have narrow : (BitVec.ofNat 64 (count n)).setWidth 32 = BitVec.ofNat 32 (count n) :=
    BitVec.setWidth_ofNat_of_le (by decide) _
  have q := congrArg (Value.get 64) rows.q
  have r := congrArg (Value.get 64) rows.r
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l10960c, rsp, q, r, shift, narrow, resumeAt]
    segment_words [rsp, q, r, shift, narrow, resumeAt]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10960c)
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩,
      ⟨rows.delta, rows.u, rows.v, rows.q, rows.r⟩, k, ?_, ?_⟩
    · change ((BitVec.ofNat 32 (count n)).setWidth 64).setWidth 32 = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · lifted_word_reads []
      lifted_word_eq []
    · row_controls
    · unfold callWrites
      slot_state region

private theorem setupWithinLinear {sp : Word} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32) : RegionsWithin (setupWrites sp) (linearWrites sp) := by
  intro r hr
  simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, by dsimp only; omega⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
    unfold base
    bv_omega

private theorem callsWithinLinear {sp : Word} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32) : RegionsWithin (callWrites (base sp)) (linearWrites sp) := by
  intro r hr
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Nat.le_refl _, by dsimp only; omega⟩

private theorem calleeWithinLinear {sp dst : Word} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32) (slot : 176 ≤ dst.toNat ∧ dst.toNat + 33 ≤ 256) :
    RegionsWithin [⟨(base sp - 8 - BitVec.ofNat 64 208).toNat, 208⟩,
      ⟨(base sp + dst).toNat, 33⟩] (linearWrites sp) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    unfold base
    bv_omega

private theorem linearWithinStack {sp : Word} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32) :
    RegionsWithin (linearWrites sp) [⟨(sp - 720).toNat, 720⟩] := by
  intro r hr
  simp only [linearWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    refine ⟨_, List.mem_cons_self, ?_⟩ <;> (try unfold base) <;> bv_omega

private theorem outsideLinear {sp off : Word} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32) (slot : 8 ≤ off.toNat ∧ off.toNat + 33 ≤ 176) :
    Outside (linearWrites sp) (base sp + off) 33 := by
  simp only [Outside, linearWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, base]
  bv_omega

private theorem outsideCall {sp off : Word} {len : Nat} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32)
    (slot : (8 ≤ off.toNat ∧ off.toNat + len ≤ 304) ∨ (336 ≤ off.toNat ∧ off.toNat + len ≤ 392)) :
    Outside (callWrites (base sp)) (base sp + off) len := by
  simp only [Outside, callWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, base]
  bv_omega

private theorem outsideShift {sp dst off : Word} {len : Nat} (lo : 720 ≤ sp.toNat)
    (hi : sp.toNat + 360 ≤ 2^32) (dstBound : dst.toNat + 33 ≤ 392)
    (offBound : off.toNat + len ≤ 392)
    (apart : off.toNat + len ≤ dst.toNat ∨ dst.toNat + 33 ≤ off.toNat) :
    Outside [⟨(base sp - 8 - BitVec.ofNat 64 208).toNat, 208⟩, ⟨(base sp + dst).toNat, 33⟩]
      (base sp + off) len := by
  simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base]
  bv_omega

private theorem keptRows {c : Registers} {m : Ram} {sp dst ret : Word}
    {out : Output Value Ram Reg.count} (post : CalleeResult c m sp dst ret 208 33 out)
    {w : Words} (rows : Rows c w) (k : Nat) (shift : c[5] = ⟨64, BitVec.ofNat 64 k⟩) :
    Rows out.values w ∧ out.values[5] = ⟨64, BitVec.ofNat 64 k⟩ := by
  have kept {i : Fin Reg.count} {value : Word} (hi : i.val ∈ [3, 5, 12, 13, 14, 15])
      (eq : c[i] = ⟨64, value⟩) : out.values[i] = ⟨64, value⟩ :=
    (post.kept i hi (congrArg Value.width eq)).trans eq
  exact ⟨⟨kept (i := 12) (by decide) rows.delta, kept (i := 3) (by decide) rows.u,
    kept (i := 15) (by decide) rows.v, kept (i := 13) (by decide) rows.q,
    kept (i := 14) (by decide) rows.r⟩, kept (i := 5) (by decide) shift⟩

private theorem runRowShift {a b c : Registers} {m p q : Ram} {sp dst ret u v : Word}
    {s n : Nat} {d e result : Int}
    (h : Entry a m sp s) (more : n < 591)
    (state : LoopState a m sp s n b p d e) (call : RowCall c q (base sp) dst ret u v n)
    (frame : RamWriteFrame p q (linearWrites sp)) (df : c[22] = ⟨1, 0⟩)
    (slot : 176 ≤ dst.toNat ∧ dst.toNat + 33 ≤ 256) (retLow : ret.toNat < 2^32)
    (exactShift : (2:Int)^count n * result =
      (Inverse.model s n).f * u.toInt + (Inverse.model s n).g * v.toInt)
    (fits : result.natAbs < 2^256) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l108890, c, q⟩, []⟩ out ∧
      CalleeResult c q (base sp - 8) (base sp + dst) ret 208 33 out ∧
      signedAt out.store (base sp + dst) result := by
  have stackFrame := state.frame.trans frame (linearWithinStack h.depthBound h.high)
  have win := h.stack.of_frame stackFrame
  have fr : CalleeFrame c q (base sp - 8) (base sp + dst) ret 208 33 :=
    shiftFrame h stackFrame (Or.inl rfl) (by decide) (by omega)
      call.rsp call.rdi df call.returnAddr retLow
  have positive : 0 < count n := by exact Nat.lt_min.mpr ⟨by decide, by omega⟩
  apply Inverse.linearShift fr ?_ call.shift positive (Nat.min_le_left ..) exactShift fits
  refine ⟨?_, ?_, call.coeffLeft, call.coeffRight⟩
  · rw [call.left]
    exact shiftSource win h.depthBound h.high (k := 8) (srcOff := 8) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega) (by omega)
      (signedAt_of_frame state.fValue frame (outsideLinear h.depthBound h.high (by decide)))
  · rw [call.right]
    exact shiftSource win h.depthBound h.high (k := 8) (srcOff := 48) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega) (by omega)
      (signedAt_of_frame state.gValue frame (outsideLinear h.depthBound h.high (by decide)))

theorem linearRows {a b c : Registers} {m p q : Ram} {sp : Word}
    {s n : Nat} {d e : Int} {w : Words} (h : Entry a m sp s)
    (state : LoopState a m sp s n b p d e) (more : n < 591)
    (rows : Rows c w) (rsp : c[4] = b[4]) (k : c[9].get 32 = BitVec.ofNat 32 (count n))
    (controls : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (frame : RamWriteFrame p q (setupWrites sp))
    (remaining : memLoad q (base sp + 336) 64 = BitVec.ofNat 64 (591-n))
    (rep : (SafeGcd.Batch.matrix w).Represents ((2:Int)^(count n)) (Inverse.model s n).f
      (Inverse.model s n).g (Inverse.model s (n+count n))) :
    ∃ c' q', Reaches .l1095c1 c q .l109657 c' q' ∧ LinearRows b p sp s n w c' q' := by
  have lo := h.depthBound
  have hi := h.high
  have xlo : 8 ≤ (base sp).toNat := by unfold base; bv_omega
  have xhi : (base sp).toNat + 336 ≤ 2^32 := by unfold base; bv_omega
  have linearFrame : RamWriteFrame p q (linearWrites sp) :=
    (RamWriteFrame.refl _ _).trans frame (setupWithinLinear lo hi)
  have win : Writable Extracted.programImage p (base sp - 8) 344 :=
    (h.stack.of_frame state.frame).sub (by unfold base; bv_omega) (by unfold base; bv_omega)
  have df : c[22] = ⟨1, 0⟩ :=
    (controls 22 (by decide)).trans ((state.kept 22 (by decide)).trans h.df)
  have entryRsp : c[4].get 64 = base sp := congrArg (Value.get 64) (rsp.trans state.rsp)
  obtain ⟨c₁, q₁, call₁, args₁, rows₁, shift₁, keep₁, prep₁⟩ :=
    firstRowCall entryRsp rows k xlo xhi (win.of_frame frame)
  have pre₁ := linearFrame.trans prep₁ (callsWithinLinear lo hi)
  have exactF : (2:Int)^count n * (Inverse.model s (n + count n)).f =
      (Inverse.model s n).f * w.u.toInt + (Inverse.model s n).g * w.v.toInt := by
    rw [Int.mul_comm _ w.u.toInt, Int.mul_comm _ w.v.toInt]
    exact rep.1.symm
  have fits := modelFits h.bound (n + count n)
  obtain ⟨out₁, exec₁, post₁, f⟩ := runRowShift h more state args₁ pre₁
    ((keep₁ 22 (by decide)).trans df) (by decide) (by decide) exactF fits.1
  have frame₁ := pre₁.trans post₁.frame (calleeWithinLinear lo hi (by decide))
  have postRsp₁ : out₁.values[4] = ⟨64, base sp⟩ := by
    rw [post₁.rsp, BitVec.sub_add_cancel]
  obtain ⟨savedRows, savedShift⟩ := keptRows post₁ rows₁ (count n) shift₁
  have nextRsp : out₁.values[4].get 64 = base sp := congrArg (Value.get 64) postRsp₁
  obtain ⟨c₂, q₂, call₂, args₂, rows₂, shift₂, keep₂, prep₂⟩ :=
    secondRowCall nextRsp savedRows savedShift xlo xhi (win.of_frame frame₁)
  have pre₂ := frame₁.trans prep₂ (callsWithinLinear lo hi)
  have df₂ : c₂[22] = ⟨1, 0⟩ := (keep₂ 22 (by decide)).trans
    ((post₁.controls 22 (by decide)).trans ((keep₁ 22 (by decide)).trans df))
  have exactG : (2:Int)^count n * (Inverse.model s (n + count n)).g =
      (Inverse.model s n).f * w.q.toInt + (Inverse.model s n).g * w.r.toInt := by
    rw [Int.mul_comm _ w.q.toInt, Int.mul_comm _ w.r.toInt]
    exact rep.2.symm
  obtain ⟨out₂, exec₂, post₂, g⟩ := runRowShift h more state args₂ pre₂ df₂
    (by decide) (by decide) exactG fits.2
  have frame₂ := pre₂.trans post₂.frame (calleeWithinLinear lo hi (by decide))
  have head : Reaches .l1095c1 c q .l10960c out₁.values out₁.store :=
    reachesOfCall call₁ exec₁ post₁.returned
  have tail : Reaches .l10960c out₁.values out₁.store .l109657 out₂.values out₂.store :=
    reachesOfCall call₂ exec₂ post₂.returned
  obtain ⟨finalRows, finalShift⟩ := keptRows post₂ rows₂ (count n) shift₂
  refine ⟨out₂.values, out₂.store, head.trans tail, ?_⟩
  refine ⟨?_, finalShift, finalRows, ?_, ?_, ?_, g, frame₂⟩
  · rw [post₂.rsp, BitVec.sub_add_cancel]
  · intro i hx
    exact (post₂.controls i hx).trans ((keep₂ i hx).trans
      ((post₁.controls i hx).trans ((keep₁ i hx).trans (controls i hx))))
  · have outsideCounter : Outside (callWrites (base sp)) (base sp + 336) 8 :=
      outsideCall lo hi (by decide)
    have from₁ : memLoad out₁.store (base sp + 336) 64 = BitVec.ofNat 64 (591 - n) :=
      (post₁.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans
        ((prep₁.memLoad_eq outsideCounter).trans remaining)
    exact (post₂.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans
      ((prep₂.memLoad_eq outsideCounter).trans from₁)
  · have before := signedAt_of_frame f prep₂ (outsideCall lo hi (by decide))
    exact signedAt_of_frame before post₂.frame (outsideShift lo hi (by decide) (by decide) (by decide))

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
