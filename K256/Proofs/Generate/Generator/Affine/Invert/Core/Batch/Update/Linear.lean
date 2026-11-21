import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Frame
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearShift
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

private def callWrites (sp : Word) : List MemoryRegion :=
  [⟨(base sp - 8).toNat, 8⟩, ⟨(base sp + 7).toNat, 9⟩,
   ⟨(base sp + 96).toNat, 16⟩, ⟨(base sp + 336).toNat, 16⟩]

private structure RowCall (c : Registers) (q : Ram) (sp dst ret u v : Word) (j : Nat) : Prop where
  rsp : c[4] = ⟨64, base sp - 8⟩
  rdi : c[7] = ⟨64, base sp + dst⟩
  left : c[6].get 64 = base sp + 120
  right : c[2].get 64 = base sp + 168
  uWord : c[1].get 64 = u
  vWord : c[8].get 64 = v
  shift : c[9].get 32 = BitVec.ofNat 32 (count j)
  returnAddr : memLoad q (base sp - 8) 64 = ret

private theorem shiftWidths {j : Nat} (hj : j < 10) :
    (BitVec.ofNat 32 (count j)).setWidth 64 = BitVec.ofNat 64 (count j) := by
  have bound := (count_spec hj).2.1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
private theorem firstRowCall {c : Registers} {q : Ram} {sp : Word} {j : Nat} {s : Words}
    (hj : j < 10) (rows : Rows c q sp s)
    (lo : 736 ≤ sp.toNat) (hi : sp.toNat + 129 ≤ 2^32)
    (win : Writable Extracted.programImage q (base sp - 8) 368)
    (shift : memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j)) :
    ∃ next ram, program.runBlock (dialect Extracted.programImage) ⟨.l108f97, c, q⟩ =
      .call ⟨.l108890, next, ram⟩ (callFrame .l108fe2 0x108fe2) ∧
      RowCall next ram sp 16 0x108fe2 s.u s.v j ∧
      next[3] = ⟨64, s.v⟩ ∧ next[5] = ⟨64, s.delta⟩ ∧ next[12] = ⟨64, s.r⟩ ∧
      next[14] = ⟨64, BitVec.ofNat 64 (count j)⟩ ∧ next[15] = ⟨64, s.u⟩ ∧
      Controls c next ∧ RamWriteFrame q ram (callWrites sp) ∧
      memLoad ram (base sp + 8) 64 = s.q := by
  have rsp : c[4].get 64 = base sp := congrArg (Value.get 64) rows.rsp
  have dst : c[14].get 64 = base sp + 16 := congrArg (Value.get 64) rows.scratch
  have u : c[15].get 64 = s.u := congrArg (Value.get 64) rows.u
  have v : c[3].get 64 = s.v := congrArg (Value.get 64) rows.v
  have wide := shiftWidths hj
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l108f97 [rsp, dst, u, v, shift, wide, callFrame]
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩, rows.v, rows.delta, rows.r,
      rfl, rows.u, ?_, ?_, ?_⟩
    · change (BitVec.ofNat 64 (count j)).setWidth 32 = _
      exact BitVec.setWidth_ofNat_of_le (by decide) _
    · lifted_word_reads []
      lifted_word_eq []
    · intro ⟨i, _⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · have baseLo : 8 ≤ (base sp).toNat := by unfold base; bv_omega
      have baseHi : (base sp).toNat + 360 ≤ 2^32 := by unfold base; bv_omega
      unfold callWrites
      slot_state region
    · segment_words [rows.q]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
private theorem secondRowCall {c : Registers} {q : Ram} {sp : Word} {j : Nat} {s : Words}
    (rsp : c[4] = ⟨64, base sp⟩)
    (delta : c[5] = ⟨64, s.delta⟩) (r : c[12] = ⟨64, s.r⟩)
    (shift : c[14] = ⟨64, BitVec.ofNat 64 (count j)⟩)
    (u : c[15] = ⟨64, s.u⟩) (v : c[3] = ⟨64, s.v⟩)
    (lo : 736 ≤ sp.toNat) (hi : sp.toNat + 129 ≤ 2^32)
    (win : Writable Extracted.programImage q (base sp - 8) 368)
    (qWord : memLoad q (base sp + 8) 64 = s.q) :
    ∃ next ram, program.runBlock (dialect Extracted.programImage) ⟨.l108fe2, c, q⟩ =
      .call ⟨.l108890, next, ram⟩ (callFrame .l109036 0x109036) ∧
      RowCall next ram sp 56 0x109036 s.q s.r j ∧
      next[3] = ⟨64, s.v⟩ ∧ next[5] = ⟨64, s.delta⟩ ∧ next[12] = ⟨64, base sp + 56⟩ ∧
      next[14] = ⟨64, BitVec.ofNat 64 (count j)⟩ ∧ next[15] = ⟨64, s.u⟩ ∧
      Controls c next ∧ RamWriteFrame q ram (callWrites sp) ∧
      memLoad ram (base sp + 8) 64 = s.q ∧ memLoad ram (base sp + 104) 64 = s.r := by
  have rspWord : c[4].get 64 = base sp := congrArg (Value.get 64) rsp
  have rWord : c[12].get 64 = s.r := congrArg (Value.get 64) r
  have shiftWord : c[14].get 64 = BitVec.ofNat 64 (count j) := congrArg (Value.get 64) shift
  have narrow : (BitVec.ofNat 64 (count j)).setWidth 32 = BitVec.ofNat 32 (count j) := by
    exact BitVec.setWidth_ofNat_of_le (by decide) _
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l108fe2 [rspWord, rWord, shiftWord, narrow, qWord, callFrame]
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩, v, delta, rfl, shift, u, ?_, ?_, ?_, ?_⟩
    · change ((BitVec.ofNat 32 (count j)).setWidth 64).setWidth 32 = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · lifted_word_reads []
      lifted_word_eq []
    · intro ⟨i, _⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · have baseLo : 8 ≤ (base sp).toNat := by unfold base; bv_omega
      have baseHi : (base sp).toNat + 360 ≤ 2^32 := by unfold base; bv_omega
      unfold callWrites
      slot_state region
    · segment_words []
    · segment_words []

private theorem setupWithinLinear {sp : Word} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) : RegionsWithin (setupWrites sp) (linearWrites sp) := by
  intro r hr
  simp only [setupWrites, work, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self), Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)), ?_⟩
    unfold base
    bv_omega

private theorem callsWithinLinear {sp : Word} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) : RegionsWithin (callWrites sp) (linearWrites sp) := by
  intro r hr
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · refine ⟨_, List.mem_cons_self, ?_⟩
    unfold base
    bv_omega
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)),
      Nat.le_refl _, ?_⟩
    change (base sp + 336).toNat + 16 ≤ (base sp + 336).toNat + 24
    omega

private theorem calleeWithinLinear {sp dst : Word} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) (slot : dst.toNat + 33 ≤ 112) :
    RegionsWithin [⟨(base sp - 8 - BitVec.ofNat 64 208).toNat, 208⟩,
      ⟨(base sp + dst).toNat, 33⟩] (linearWrites sp) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    refine ⟨_, List.mem_cons_self, ?_⟩ <;> (try unfold base) <;> bv_omega

private theorem linearWithinStack {sp : Word} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) :
    RegionsWithin (linearWrites sp) [⟨(sp - 736).toNat, 736⟩] := by
  intro r hr
  simp only [linearWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    refine ⟨_, List.mem_cons_self, ?_⟩ <;> (try unfold base) <;> bv_omega

private theorem sourceOutsideLinear {sp off : Word} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) (lower : 120 ≤ off.toNat) (upper : off.toNat + 33 ≤ 336) :
    Outside (linearWrites sp) (base sp + off) 33 := by
  simp only [Outside, linearWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  unfold base
  bv_omega

private theorem outsideRowCall {sp off : Word} {n : Nat} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) (offBound : off.toNat + n ≤ 408)
    (apart : (16 ≤ off.toNat ∧ off.toNat + n ≤ 96) ∨ 352 ≤ off.toNat) :
    Outside (callWrites sp) (base sp + off) n := by
  simp only [Outside, callWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  unfold base
  bv_omega

private theorem outsideShift {sp dst off : Word} {n : Nat} (lo : 736 ≤ sp.toNat)
    (hi : sp.toNat + 129 ≤ 2^32) (dstBound : dst.toNat + 33 ≤ 112) (offBound : off.toNat + n ≤ 408)
    (apart : off.toNat + n ≤ dst.toNat ∨ dst.toNat + 33 ≤ off.toNat) :
    Outside [⟨(base sp - 8 - BitVec.ofNat 64 208).toNat, 208⟩, ⟨(base sp + dst).toNat, 33⟩]
      (base sp + off) n := by
  simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  unfold base
  bv_omega

private theorem runRowShift {a b c : Registers} {m p q : Ram} {sp dst ret u v : Word}
    {z : Fin modulus} {w : Vector Word 4} {j : Nat} {d e result : Int}
    (h : Entry a m sp z w) (hj : j < 10)
    (state : LoopState a m sp z (roundsBefore j) b p d e) (call : RowCall c q sp dst ret u v j)
    (frame : RamWriteFrame p q (linearWrites sp)) (df : c[22] = ⟨1, 0⟩)
    (slot : dst.toNat + 33 ≤ 112) (retLow : ret.toNat < 2^32)
    (exactShift : (2:Int)^count j * result =
      (Core.model z (roundsBefore j)).f * u.toInt + (Core.model z (roundsBefore j)).g * v.toInt)
    (fits : result.natAbs < 2^256) :
    ∃ out, CalleeExec .l108890 c q out ∧
      CalleeResult c q (base sp - 8) (base sp + dst) ret 208 33 out ∧
      signedAt out.store (base sp + dst) result := by
  have stackFrame := state.frame.trans frame (linearWithinStack h.low h.high)
  have win := h.stack.of_frame stackFrame
  have fr : CalleeFrame c q (base sp - 8) (base sp + dst) ret 208 33 :=
    shiftFrame h stackFrame (Or.inl rfl) (by decide) (by omega)
      call.rsp call.rdi df call.returnAddr retLow
  apply Core.linearShift fr ?_ call.shift (count_spec hj).1 (count_spec hj).2.1 exactShift fits
  refine ⟨?_, ?_, call.uWord, call.vWord⟩
  · rw [call.left]
    exact shiftSource win h.low h.high (k := 8) (srcOff := 120) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega)
      (signedAt_of_frame state.fValue frame (sourceOutsideLinear h.low h.high (by decide) (by decide)))
  · rw [call.right]
    exact shiftSource win h.low h.high (k := 8) (srcOff := 168) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega)
      (signedAt_of_frame state.gValue frame (sourceOutsideLinear h.low h.high (by decide) (by decide)))

private theorem keptWord {c : Registers} {m : Ram} {sp dst ret : Word}
    {out : Output Value Ram Reg.count} (post : CalleeResult c m sp dst ret 208 33 out)
    {i : Fin Reg.count} {val : Word} (member : i.val ∈ [3, 5, 12, 13, 14, 15])
    (eq : c[i] = ⟨64, val⟩) : out.values[i] = ⟨64, val⟩ :=
  (post.kept i member (congrArg Value.width eq)).trans eq

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

theorem linearRows (h : Entry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram}
    {s : Words} (rows : Rows c q sp s) (kept : Controls b c)
    (frame : RamWriteFrame p q (setupWrites sp))
    (shift : memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j))
    (rem : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j))
    (rep : (SafeGcd.Batch.matrix s).Represents ((2:Int)^count j)
      (Core.model z (roundsBefore j)).f (Core.model z (roundsBefore j)).g (Core.model z (roundsBefore (j+1)))) :
    ∃ c' q', Reaches .l108f97 c q .l109036 c' q' ∧ LinearRows b p sp z j s c' q' := by
  have lo := h.low
  have hi := h.high
  have linearFrame : RamWriteFrame p q (linearWrites sp) :=
    (RamWriteFrame.refl _ _).trans frame (setupWithinLinear lo hi)
  have stack := h.stack.of_frame state.frame
  have win : Writable Extracted.programImage p (base sp - 8) 368 :=
    stack.sub (by unfold base; bv_omega) (by unfold base; bv_omega)
  have ctrl : c[22] = ⟨1, 0⟩ :=
    (kept 22 (by decide)).trans ((state.kept 22 (by decide)).trans h.df)
  obtain ⟨c₁, q₁, call₁, args₁, v₁, delta₁, r₁, shift₁, u₁, kept₁, prep₁, qword₁⟩ :=
    firstRowCall hj rows lo hi (win.of_frame frame) shift
  have pre₁ := linearFrame.trans prep₁ (callsWithinLinear lo hi)
  have exactF : (2:Int)^count j * (Core.model z (roundsBefore (j+1))).f =
      (Core.model z (roundsBefore j)).f * s.u.toInt + (Core.model z (roundsBefore j)).g * s.v.toInt := by
    rw [Int.mul_comm _ s.u.toInt, Int.mul_comm _ s.v.toInt]
    exact rep.1.symm
  have fits := modelFits z (roundsBefore (j+1))
  obtain ⟨out₁, exec₁, post₁, f⟩ := runRowShift h hj state args₁ pre₁
    ((kept₁ 22 (by decide)).trans ctrl) (by decide) (by decide) exactF fits.1
  have frame₁ := pre₁.trans post₁.frame (calleeWithinLinear lo hi (by decide))
  have postRsp₁ : out₁.values[4] = ⟨64, base sp⟩ := by
    rw [post₁.rsp, BitVec.sub_add_cancel]
  have qword₁' : memLoad out₁.store (base sp + 8) 64 = s.q :=
    (post₁.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans qword₁
  obtain ⟨c₂, q₂, call₂, args₂, v₂, delta₂, dst₂, shift₂, u₂, kept₂, prep₂, qword₂, rword₂⟩ :=
    secondRowCall (j := j) postRsp₁
      (keptWord post₁ (i := 5) (by decide) delta₁) (keptWord post₁ (i := 12) (by decide) r₁)
      (keptWord post₁ (i := 14) (by decide) shift₁) (keptWord post₁ (i := 15) (by decide) u₁)
      (keptWord post₁ (i := 3) (by decide) v₁) lo hi (win.of_frame frame₁) qword₁'
  have pre₂ := frame₁.trans prep₂ (callsWithinLinear lo hi)
  have df₂ : c₂[22] = ⟨1, 0⟩ := (kept₂ 22 (by decide)).trans
    ((post₁.controls 22 (by decide)).trans ((kept₁ 22 (by decide)).trans ctrl))
  have exactG : (2:Int)^count j * (Core.model z (roundsBefore (j+1))).g =
      (Core.model z (roundsBefore j)).f * s.q.toInt + (Core.model z (roundsBefore j)).g * s.r.toInt := by
    rw [Int.mul_comm _ s.q.toInt, Int.mul_comm _ s.r.toInt]
    exact rep.2.symm
  obtain ⟨out₂, exec₂, post₂, g⟩ := runRowShift h hj state args₂ pre₂ df₂
    (by decide) (by decide) exactG fits.2
  have frame₂ := pre₂.trans post₂.frame (calleeWithinLinear lo hi (by decide))
  have head : Reaches .l108f97 c q .l108fe2 out₁.values out₁.store :=
    Sample.reachesAfterSampleCall call₁ exec₁ post₁.returned []
  have tail : Reaches .l108fe2 out₁.values out₁.store .l109036 out₂.values out₂.store :=
    Sample.reachesAfterSampleCall call₂ exec₂ post₂.returned []
  refine ⟨out₂.values, out₂.store, head.trans tail, ?_⟩
  refine ⟨?_, keptWord post₂ (i := 5) (by decide) delta₂, keptWord post₂ (i := 12) (by decide) dst₂,
    keptWord post₂ (i := 14) (by decide) shift₂, keptWord post₂ (i := 15) (by decide) u₂,
    keptWord post₂ (i := 3) (by decide) v₂, ?_, ?_, ?_, ?_, g, ?_, frame₂⟩
  · rw [post₂.rsp, BitVec.sub_add_cancel]
  · exact (post₂.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans qword₂
  · exact (post₂.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans rword₂
  · have outsideCounter : Outside (callWrites sp) (base sp + 352) 8 :=
      outsideRowCall lo hi (by decide) (by decide)
    have from₁ : memLoad out₁.store (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j) :=
      (post₁.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans
        ((prep₁.memLoad_eq outsideCounter).trans rem)
    exact (post₂.frame.memLoad_eq (outsideShift lo hi (by decide) (by decide) (by decide))).trans
      ((prep₂.memLoad_eq outsideCounter).trans from₁)
  · have before := signedAt_of_frame f prep₂ (outsideRowCall lo hi (by decide) (by decide))
    exact signedAt_of_frame before post₂.frame (outsideShift lo hi (by decide) (by decide) (by decide))
  · intro i hx
    exact (post₂.controls i hx).trans ((kept₂ i hx).trans
      ((post₁.controls i hx).trans ((kept₁ i hx).trans (kept i hx))))

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
