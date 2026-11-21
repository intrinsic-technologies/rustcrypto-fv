import K256.Proofs.Ecdh.Affine.Inverse.Zero.State
import K256.Proofs.Ecdh.Affine.Inverse.Contract
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

namespace K256.Proofs.Ecdh.Affine.Inverse.Zero

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator K256.Proofs.Generate.Generator.Affine
open K256.Proofs.Generate.Generator.Affine.Invert K256.Proofs.Generate.Generator.Affine.Invert.Core
open K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
open SafeGcd.Batch (Words)

open Lean Elab Command in
local elab "open_invert_batch " path:ident " (" decls:ident+ ")" : command => do
  let ns := `K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
  for decl in decls do
    let name := mkPrivateNameCore (ns ++ path.getId) (ns ++ decl.getId)
    modifyScope fun scope => { scope with openDecls := .explicit decl.getId name :: scope.openDecls }

open_invert_batch Prepare (loadInputs initializeRows)
open_invert_batch Update.Linear (RowCall firstRowCall secondRowCall linearWithinStack
  sourceOutsideLinear setupWithinLinear callsWithinLinear calleeWithinLinear keptWord
  outsideShift outsideRowCall callWrites)
open_invert_batch Update.Modular (ModularCall firstModularCall secondModularCall copyWrites pushWrites)
open_invert_batch Update.Copy (copyBlock)

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

private theorem initialWordsLowZero {entry b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus}
    {n : Nat} {d e : Int} (state : ZeroLoopState entry m sp z n b p d e) (hn : n ≤ 591) :
    SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state (initialWords b p sp)) (Core.model z n) := by
  refine ⟨?_, ?_, ?_⟩
  · change (b[5].get 64).toInt = _
    rw [state.delta]
    change (BitVec.ofInt 64 (Core.model z n).delta).toInt = _
    have h := deltaBound n ⟨1, modulus, z.val⟩
    change (Core.model z n).delta.natAbs ≤ 1+2*n at h
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (120 : Word) + 32 = 152 from by decide +kernel] using
      lowWord_congruent state.fValue
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (168 : Word) + 32 = 200 from by decide +kernel] using
      lowWord_congruent state.gValue

private theorem prepareZero (h : ZeroEntry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) :
    ∃ c q s, Reaches .l1091e4 b p .l1092a0 c q ∧ Controls b c ∧
      RamWriteFrame p q (setupWrites sp) ∧ Inner c q sp s (count j) ∧
      memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j) ∧
      memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j) ∧
      SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state s) (Core.model z (roundsBefore j)) ∧
      SafeGcd.Batch.matrix s = SafeGcd.Matrix.identity := by
  have lo := h.low
  have hi := h.high
  have window : Writable Extracted.programImage p (base sp) 360 :=
    (h.stack.of_frame state.frame).sub (by unfold base; bv_omega) (by unfold base; bv_omega)
  obtain ⟨c, q, head, rsp, delta, f, signF, g, counter, kept, frame, signG, shift, remaining⟩ :=
    loadInputs hj state.rsp state.remaining window
  have delta' : c[5] = ⟨64, (initialWords b p sp).delta⟩ := by
    rw [delta]
    change b[5] = ⟨64, b[5].get 64⟩
    rw [state.delta]
    simp only [Value.get, BitVec.setWidth_eq]
  obtain ⟨out, tail, kept', inner⟩ :=
    initializeRows (window.of_frame frame) rsp delta' f signF g signG counter
  refine ⟨out, _, initialWords b p sp, ?_, fun i hi => (kept' i hi).trans (kept i hi),
    ?_, inner, ?_, ?_, initialWordsLowZero state (Nat.min_le_right _ _), rfl⟩
  · refine .step (b := ⟨⟨.l109246, c, q⟩, []⟩) ?_ (.step ?_ (.refl _))
    · change program.step _ _ = _
      simp only [Program.step, head, Transfer.next]
    · change program.step _ _ = _
      simp only [Program.step, tail, Transfer.next]
  · simp only [setupWrites, work, List.singleton_append] at frame ⊢
    have bounds := window.readable.low
    slot_state region
  · segment_words [shift]
  · segment_words [remaining]

private theorem shiftFrameZero {a c : Registers} {m p : Ram} {sp k off ret : Word} {z : Fin modulus}
    {w : Vector Word 4} {depth : Nat} (h : ZeroEntry a m sp z w)
    (frame : RamWriteFrame m p [⟨(sp - 736).toNat, 736⟩])
    (push : k = 8 ∨ k = 24) (room : k.toNat + depth ≤ 328) (slot : off.toNat + 33 ≤ 408)
    (rsp : c[4] = ⟨64, base sp - k⟩) (rdi : c[7] = ⟨64, base sp + off⟩)
    (df : c[22] = ⟨1, 0⟩) (returnAddr : memLoad p (base sp - k) 64 = ret)
    (retLow : ret.toNat < 2^32) :
    CalleeFrame c p (base sp - k) (base sp + off) ret depth 33 := by
  have win := h.stack.of_frame frame
  have lo := h.low
  have hi := h.high
  have align := h.aligned
  have img := Core.stackImage h.stack frame h.image
  refine ⟨rsp, rdi, df, img, ?_, ?_, win.readable.sub ?_ ?_, returnAddr, retLow,
    win.sub ?_ ?_, win.sub ?_ ?_, Or.inr ?_⟩
  all_goals rcases push with rfl|rfl <;> unfold base <;> bv_omega

private theorem runRowShiftZero {a b c : Registers} {m p q : Ram} {sp dst ret u v : Word}
    {z : Fin modulus} {w : Vector Word 4} {j : Nat} {d e result : Int}
    (h : ZeroEntry a m sp z w) (hj : j < 10)
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) (call : RowCall c q sp dst ret u v j)
    (frame : RamWriteFrame p q (linearWrites sp)) (df : c[22] = ⟨1, 0⟩)
    (slot : dst.toNat + 33 ≤ 112) (retLow : ret.toNat < 2^32)
    (exactShift : (2:Int)^count j * result =
      (Core.model z (roundsBefore j)).f * u.toInt + (Core.model z (roundsBefore j)).g * v.toInt)
    (fits : result.natAbs < 2^256) :
    ∃ out, CalleeExec .l108890 c q out ∧
      CalleeResult c q (base sp - 8) (base sp + dst) ret 208 33 out ∧
      signedAt out.store (base sp + dst) result := by
  obtain ⟨rsp, rdi, left, right, uWord, vWord, shift, returnAddr⟩ := call
  have stackFrame := state.frame.trans frame (linearWithinStack h.low h.high)
  have win := h.stack.of_frame stackFrame
  have fr : CalleeFrame c q (base sp - 8) (base sp + dst) ret 208 33 :=
    shiftFrameZero h stackFrame (Or.inl rfl) (by decide) (by omega)
      rsp rdi df returnAddr retLow
  apply Core.linearShift fr ?_ shift (count_spec hj).1 (count_spec hj).2.1 exactShift fits
  refine ⟨?_, ?_, uWord, vWord⟩
  · rw [left]
    exact shiftSource win h.low h.high (k := 8) (srcOff := 120) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega)
      (signedAt_of_frame state.fValue frame (sourceOutsideLinear h.low h.high (by decide) (by decide)))
  · rw [right]
    exact shiftSource win h.low h.high (k := 8) (srcOff := 168) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega)
      (signedAt_of_frame state.gValue frame (sourceOutsideLinear h.low h.high (by decide) (by decide)))

private theorem linearRowsZero (h : ZeroEntry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram}
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
  obtain ⟨out₁, exec₁, post₁, f⟩ := runRowShiftZero h hj state args₁ pre₁
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
  obtain ⟨out₂, exec₂, post₂, g⟩ := runRowShiftZero h hj state args₂ pre₂ df₂
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

private theorem runModularCallZero {c : Registers} {q : Ram} {ret dst u v : Word} {k : Nat} {d e : Int}
    (h : ZeroEntry a m sp z w) (full : RamWriteFrame m q [⟨(sp - 736).toNat,736⟩])
    (call : ModularCall c q (base sp) dst ret u v k) (df : c[22] = ⟨1,0⟩)
    (slot : dst.toNat ≤ 56) (retLow : ret.toNat < 2^32)
    (sd : signedAt q (base sp + 208) d) (se : signedAt q (base sp + 248) e)
    (pos : 0 < k) (small : k ≤ 62) (bound : (d*u.toInt + e*v.toInt).natAbs < 2^k * modulus) :
    ∃ out r, CalleeExec .l108980 c q out ∧
      CalleeResult c q (base sp - 24) (base sp + dst) ret 304 33 out ∧
      signedAt out.store (base sp + dst) r ∧ r.natAbs < modulus ∧
      ((2:Int)^k * r) % modulus = (d*u.toInt + e*v.toInt) % modulus := by
  have lo := h.low
  have hi := h.high
  obtain ⟨rsp, dstReg, left, right, uReg, vReg, shift, returned, ptr, inverse⟩ := call
  have win := h.stack.of_frame full
  have fr := shiftFrameZero (depth := 304) h full (Or.inr rfl) (by decide) (by omega)
    rsp dstReg df returned retLow
  refine Core.modularShift fr ⟨?_, ?_, uReg, vReg⟩ shift pos small
    (win.readable.sub ?_ ?_) ?_ (Or.inr ?_) ?_ ?_ bound
  · rw [left]
    exact shiftSource win lo hi (by decide) (by decide) (by change dst.toNat + 33 ≤ 208; omega) sd
  · rw [right]
    exact shiftSource win lo hi (by decide) (by decide) (by change dst.toNat + 33 ≤ 248; omega) se
  all_goals first | (rw [show base sp - 24 + 8 = base sp - 16 by bv_omega]; exact ptr)
                  | (rw [show base sp - 24 + 16 = base sp - 8 by bv_omega]; exact inverse)
                  | (unfold base; bv_omega)

local macro "slot_out" : tactic => `(tactic|
  (simp only [Outside, linearWrites, modularWrites, copyWrites, pushWrites, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    base, Nat.reduceDiv]
   bv_omega))

local macro "slot_within" : tactic => `(tactic|
  (intro r hr
   simp only [linearWrites, modularWrites, copyWrites, pushWrites, List.cons_append,
     List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
   repeat' (rcases hr with (rfl | hr))
   all_goals try subst r
   all_goals
     simp only [modularWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left,
       exists_eq_or_imp, base]
     bv_omega))

private theorem modularRowsZero (h : ZeroEntry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram} {s : Words}
    (rows : LinearRows b p sp z j s c q)
    (bound : (SafeGcd.Batch.matrix s).Bounded (2^count j)) :
    ∃ c' q' d' e', Reaches .l109036 c q .l10914e c' q' ∧ ModularRows b p sp z j s c' q' d' e' ∧
      d'.natAbs < modulus ∧ e'.natAbs < modulus ∧
      ((2:Int)^count j * d') % modulus = (d*s.u.toInt + e*s.v.toInt) % modulus ∧
      ((2:Int)^count j * e') % modulus = (d*s.q.toInt + e*s.r.toInt) % modulus := by
  have lo := h.low
  have hi := h.high
  obtain ⟨pos, small, _⟩ := count_spec hj
  have full0 := state.frame.trans rows.frame (by slot_within)
  have win := h.stack.of_frame full0
  obtain ⟨c₁,m₁,step₁,args₁,bp₁,second₁,shift₁,ptr₁,inv₁,ctrl₁,writes₁,copyF,copyG⟩ :=
    firstModularCall (by unfold base; bv_omega) (win.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
      rows.rsp rows.second rows.shift small rows.u rows.v
      ((rows.frame.memLoad_eq (by slot_out)).trans state.modulusPtr)
      ((rows.frame.memLoad_eq (by slot_out)).trans state.modulusInverse)
  have full₁ := full0.trans writes₁ (by slot_within)
  have d₀ := signedAt_of_frame state.dValue rows.frame (by slot_out)
  have e₀ := signedAt_of_frame state.eValue rows.frame (by slot_out)
  have d₁ := signedAt_of_frame d₀ writes₁ (by slot_out)
  have e₁ := signedAt_of_frame e₀ writes₁ (by slot_out)
  have df := ((rows.controls 22 (by decide)).trans (state.kept 22 (by decide))).trans h.df
  obtain ⟨out₁,r₁,run₁,res₁,value₁,bound₁,congr₁⟩ :=
    runModularCallZero h full₁ args₁ ((ctrl₁ 22 (by decide)).trans df) (by decide) (by decide)
      d₁ e₁ pos small (rowBound state.dBound state.eBound bound.1)
  have reach₁ := Sample.reachesAfterSampleCall step₁ run₁ res₁.returned []
  have fullMid := full₁.trans res₁.frame (by slot_within)
  have rspMid : out₁.values[4] = ⟨64, base sp - 16⟩ := by rw [res₁.rsp]; congr 1 <;> bv_omega
  have secMid := second₁.trans rows.second
  have bpMid := bp₁.trans rows.delta
  have preserved (i : Fin Reg.count) (mem : i.val ∈ [3,5,12,13,14,15]) {v : Word}
      (vEq : c₁[i] = ⟨64,v⟩) := (res₁.kept i mem (by rw [vEq])).trans vEq
  have winMid := h.stack.of_frame fullMid
  obtain ⟨c₂,m₂,step₂,args₂,bp₂,second₂,shift₂,scratch₂,ctrl₂,writes₂⟩ :=
    secondModularCall (by unfold base; bv_omega)
      (winMid.sub (by unfold base; bv_omega) (by unfold base; bv_omega)) rspMid
      (preserved 12 (by decide) secMid) (preserved 15 (by decide) shift₁) small
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans rows.qWord))
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans rows.rWord))
      (preserved 3 (by decide) ptr₁) (preserved 14 (by decide) inv₁)
  have full₂ := fullMid.trans writes₂ (by slot_within)
  have controlsMid : Controls b c₂ := fun i hi => (ctrl₂ i hi).trans ((res₁.controls i hi).trans
    ((ctrl₁ i hi).trans (rows.controls i hi)))
  obtain ⟨out₂,r₂,run₂,res₂,value₂,bound₂,congr₂⟩ := runModularCallZero h full₂ args₂
    (((controlsMid 22 (by decide)).trans (state.kept 22 (by decide))).trans h.df)
    (by decide) (by decide)
    (signedAt_of_frame (signedAt_of_frame d₁ res₁.frame (by slot_out)) writes₂ (by slot_out))
    (signedAt_of_frame (signedAt_of_frame e₁ res₁.frame (by slot_out)) writes₂ (by slot_out))
    pos small (rowBound state.dBound state.eBound bound.2)
  have reach₂ := Sample.reachesAfterSampleCall step₂ run₂ res₂.returned []
  have keep₂ (i : Fin Reg.count) (mem : i.val ∈ [3,5,12,13,14,15]) {v : Word}
      (vEq : c₂[i] = ⟨64,v⟩) := (res₂.kept i mem (by rw [vEq])).trans vEq
  refine ⟨_,_,_,_,reach₁.trans reach₂, ?_, bound₁,bound₂,congr₁,congr₂⟩
  refine ⟨?_,keep₂ 5 (by decide) (bp₂.trans (preserved 5 (by decide) bpMid)),
    keep₂ 12 (by decide) (second₂.trans (preserved 12 (by decide) secMid)),
    keep₂ 14 (by decide) scratch₂, keep₂ 15 (by decide) shift₂, ?_, ?_, ?_, ?_, value₂,
    fun i hi => (res₂.controls i hi).trans (controlsMid i hi), ?_⟩
  · rw [res₂.rsp]; congr 1 <;> bv_omega
  · exact (res₂.frame.memLoad_eq (by slot_out)).trans ((writes₂.memLoad_eq (by slot_out)).trans
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans rows.remaining)))
  · exact signedAt_of_frame (signedAt_of_frame (signedAt_of_frame
      (signedAt_of_copy rows.firstResult copyF) res₁.frame (by slot_out)) writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact signedAt_of_frame (signedAt_of_frame (signedAt_of_frame
      (signedAt_of_copy rows.secondResult copyG) res₁.frame (by slot_out)) writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact signedAt_of_frame (signedAt_of_frame value₁ writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact (((((RamWriteFrame.refl p (modularWrites sp)).trans rows.frame (by slot_within)).trans
      writes₁ (by slot_within)).trans res₁.frame (by slot_within)).trans writes₂ (by slot_within)).trans
      res₂.frame (by slot_within)

private theorem copyRowsZero (h : ZeroEntry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram} {s : Words}
    {d' e' : Int} (rows : ModularRows b p sp z j s c q d' e')
    (delta : s.delta.toInt = (Core.model z (roundsBefore (j+1))).delta)
    (db : d'.natAbs < modulus) (eb : e'.natAbs < modulus)
    (di : (d' * z.val) % modulus = (Core.model z (roundsBefore (j+1))).f % modulus)
    (ei : (e' * z.val) % modulus = (Core.model z (roundsBefore (j+1))).g % modulus) :
    ∃ c' q', Reaches .l10914e c q (batchLabel (j+1)) c' q' ∧
      ZeroLoopState a m sp z (roundsBefore (j+1)) c' q' d' e' := by
  have lo := h.low
  have hi := h.high
  have win := (h.stack.of_frame state.frame).of_frame rows.frame
  have shift : c[15].get 32 = BitVec.ofNat 32 (count j) := by
    rw [rows.shift]
    change (BitVec.ofNat 64 (count j)).setWidth 32 = BitVec.ofNat 32 (count j)
    exact BitVec.setWidth_ofNat_of_le (by decide) _
  obtain ⟨last, mem, reach, rsp, rbp, r14, remaining, controls, writes, first, second⟩ :=
    copyBlock hj (congrArg (Value.get 64) rows.rsp) (congrArg (Value.get 64) rows.second)
      shift rows.remaining (win.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
  let rs := modularWrites sp ++ [⟨(base sp + 208).toNat, 80⟩]
  have total : RamWriteFrame p mem rs := by
    refine ((RamWriteFrame.refl p rs).trans rows.frame ?_).trans writes ?_
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      exact ⟨r, List.mem_append_right _ hr, Nat.le_refl _, Nat.le_refl _⟩
  have stable (off : Word) (lb : 288 ≤ off.toNat) (ub : off.toNat + 8 ≤ 336) :
      memLoad mem (base sp + off) 64 =
        memLoad p (base sp + off) 64 := by
    apply total.memLoad_eq
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  refine ⟨last, mem, reach, rsp, ?_, remaining, r14.trans rows.scratch,
    fun i hi => ((controls i hi).trans (rows.controls i hi)).trans (state.kept i hi),
    ?_, state.frame.trans total ?_, ?_, ?_, signedAt_of_copy rows.firstResult first,
    signedAt_of_copy rows.secondResult second, db, eb, di, ei, ?_, ?_, ?_, ?_⟩
  · rw [rbp, rows.delta, ← delta, BitVec.ofInt_toInt]
  · intro i off hm
    apply (total.memLoad_eq ?_).trans (state.saved _ _ hm)
    have bound : 8 ≤ off ∧ off ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      omega
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  · intro r hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [rs, modularWrites, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp only [base] <;> constructor <;> bv_omega
  · apply signedAt_of_frame rows.fValue writes
    simp only [Outside, List.mem_singleton, forall_eq, base]
    bv_omega
  · apply signedAt_of_frame rows.gValue writes
    simp only [Outside, List.mem_singleton, forall_eq, base]
    bv_omega
  · rw [stable 312 (by decide) (by decide), stable 296 (by decide) (by decide),
      stable 288 (by decide) (by decide), stable 304 (by decide) (by decide)]
    exact state.originalZero
  · exact (stable 320 (by decide) (by decide)).trans state.outputPtr
  · apply (total.memLoad_eq ?_).trans state.modulusPtr
    simp only [rs, modularWrites, List.cons_append, List.nil_append, Outside, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, base, Nat.reduceDiv]
    bv_omega
  · exact (stable 328 (by decide) (by decide)).trans state.modulusInverse

private theorem updateZero (h : ZeroEntry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram}
    {s : Words} (rows : Rows c q sp s) (kept : Controls b c)
    (frame : RamWriteFrame p q (setupWrites sp))
    (shift : memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j))
    (rem : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j))
    (delta : s.delta.toInt = (Core.model z (roundsBefore (j+1))).delta)
    (rep : (SafeGcd.Batch.matrix s).Represents ((2:Int)^count j)
      (Core.model z (roundsBefore j)).f (Core.model z (roundsBefore j)).g (Core.model z (roundsBefore (j+1))))
    (bound : (SafeGcd.Batch.matrix s).Bounded (2^count j)) :
    ∃ c' q' d' e', Reaches .l108f97 c q (batchLabel (j+1)) c' q' ∧
      ZeroLoopState a m sp z (roundsBefore (j+1)) c' q' d' e' := by
  obtain ⟨cl, ml, el, linear⟩ := linearRowsZero h hj state rows kept frame shift rem rep
  obtain ⟨cm, mm, d', e', em, modular, db, eb, dc, ec⟩ := modularRowsZero h hj state linear bound
  obtain ⟨last, mem, tail, post⟩ := copyRowsZero h hj state modular delta db eb
    (rowInvariant state.dInvariant state.eInvariant rep.1 dc)
    (rowInvariant state.dInvariant state.eInvariant rep.2 ec)
  exact ⟨last, mem, d', e', (el.trans em).trans tail, post⟩

theorem batch (h : ZeroEntry a m sp z w) {j : Nat} (hj : j < 10) {b : Registers} {p : Ram} {d e : Int}
    (state : ZeroLoopState a m sp z (roundsBefore j) b p d e) :
    ∃ c q d' e', Reaches .l1091e4 b p (batchLabel (j + 1)) c q ∧
      ZeroLoopState a m sp z (roundsBefore (j + 1)) c q d' e' := by
  obtain ⟨c, q, s, prep, kept, setup, inner, shift, rem, lowBits, identity⟩ :=
    prepareZero h hj state
  have lo := h.low
  have hi := h.high
  obtain ⟨pos, limit, rounds⟩ := Batch.count_spec hj
  have writable := (h.stack.of_frame state.frame).of_frame setup
  obtain ⟨c', q', run, kept', frame, rows⟩ := Batch.runWords pos limit inner lo hi
    (writable.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
  have modelNext : SafeGcd.divsteps (Batch.count j) (Core.model z (roundsBefore j)) =
      Core.model z (roundsBefore (j+1)) := by
    rw [Core.model, ← SafeGcd.divsteps_add, rounds, Core.model]
  have delta : s.delta.toInt.natAbs + 2 * Batch.count j ≤ 1183 := by
    have hv := lowBits.1
    change s.delta.toInt = (Core.model z (roundsBefore j)).delta at hv
    rw [hv]
    have hd := Batch.deltaBound (roundsBefore j) ⟨1, modulus, z.val⟩
    change (Core.model z (roundsBefore j)).delta.natAbs ≤ 1 + 2 * roundsBefore j at hd
    have hn : roundsBefore (j+1) ≤ 591 := Nat.min_le_right _ _
    omega
  have odd : (Core.model z (roundsBefore j)).f % 2 = 1 :=
    SafeGcd.divsteps_odd _ (s := ⟨1, modulus, z.val⟩) (by decide +kernel : (modulus : Int) % 2 = 1)
  obtain ⟨rep, bound⟩ := SafeGcd.Batch.matrix_represents _ s _ delta limit lowBits identity odd
  have newDelta := (SafeGcd.Batch.matrix_correct _ s _ delta limit lowBits identity).2
  rw [modelNext] at rep newDelta
  have shiftEq : memLoad q' (base sp + 116) 32 = memLoad q (base sp + 116) 32 := by
    apply frame.memLoad_eq
    simp only [Batch.work, Outside, List.mem_singleton, forall_eq, base]
    exact ⟨by bv_omega, Or.inr (by bv_omega)⟩
  have remEq : memLoad q' (base sp + 352) 64 = memLoad q (base sp + 352) 64 := by
    apply frame.memLoad_eq
    simp only [Batch.work, Outside, List.mem_singleton, forall_eq, base]
    exact ⟨by bv_omega, Or.inr (by bv_omega)⟩
  have ⟨last, mem, d', e', tail, post⟩ := updateZero h hj state rows
    (fun i hi => (kept' i hi).trans (kept i hi))
    (setup.trans frame (fun r hr => ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩))
    (shiftEq.trans shift) (remEq.trans rem)
    newDelta rep bound
  exact ⟨last, mem, d', e', (prep.trans run).trans tail, post⟩

end K256.Proofs.Ecdh.Affine.Inverse.Zero
