import K256.Proofs.Signing.Composition.Attempt.Inverse.Batch.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Linear

namespace K256.Proofs.Signing.Composition.Attempt.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Common.Field
open Generate.Generator.Sample (reachesAfterSampleCall)
open Generate.Generator.Affine (Reaches)
open Generate.Generator.Affine.Invert
open Generate.Generator.Affine.Invert.Core (base signedAt roundsBefore CalleeFrame CalleeExec CalleeResult)
open Generate.Generator.Affine.Invert.Core.Batch (count count_spec Rows Controls setupWrites linearWrites signedAt_of_frame shiftSource)
open Verify.Core (Registers)
open Verify.Core.Scalars.Inverse (modelFits)
open SafeGcd.Batch (Words)

open_order_batch Update.Linear (callWrites RowCall firstRowCall secondRowCall setupWithinLinear
  callsWithinLinear calleeWithinLinear linearWithinStack sourceOutsideLinear outsideRowCall
  outsideShift keptWord)

private theorem runRowShift {a b c : Registers} {m p q : Ram} {sp dst ret u v : Word}
    {z : Nat} {j : Nat} {d e result : Int}
    (h : Entry a m sp z) (hj : j < 10)
    (state : LoopState a m sp z (roundsBefore j) b p d e) (call : RowCall c q sp dst ret u v j)
    (frame : RamWriteFrame p q (linearWrites sp)) (df : c[22] = ⟨1, 0⟩)
    (slot : dst.toNat + 33 ≤ 112) (retLow : ret.toNat < 2^32)
    (exactShift : (2:Int)^count j * result =
      (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).f * u.toInt +
        (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).g * v.toInt)
    (fits : result.natAbs < 2^256) :
    ∃ out, CalleeExec .l108890 c q out ∧
      CalleeResult c q (base sp - 8) (base sp + dst) ret 208 33 out ∧
      signedAt out.store (base sp + dst) result := by
  obtain ⟨rsp, rdi, left, right, uWord, vWord, shift, returnAddr⟩ := call
  have lo := h.depthBound
  have high := h.high
  have hi : sp.toNat + 129 ≤ 2^32 := by omega
  have stackFrame := state.frame.trans frame (linearWithinStack lo hi)
  have win := h.stack.of_frame stackFrame
  have fr : CalleeFrame c q (base sp - 8) (base sp + dst) ret 208 33 :=
    shiftFrame h stackFrame (Or.inl rfl) (by decide) (by omega)
      rsp rdi df returnAddr retLow
  apply Core.linearShift fr ?_ shift (count_spec hj).1 (count_spec hj).2.1 exactShift fits
  refine ⟨?_, ?_, uWord, vWord⟩
  · rw [left]
    exact shiftSource win lo hi (k := 8) (srcOff := 120) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega)
      (signedAt_of_frame state.fValue frame (sourceOutsideLinear lo hi (by decide) (by decide)))
  · rw [right]
    exact shiftSource win lo hi (k := 8) (srcOff := 168) (by decide) (by decide)
      (by simp only [BitVec.reduceToNat]; omega)
      (signedAt_of_frame state.gValue frame (sourceOutsideLinear lo hi (by decide) (by decide)))

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Nat}

theorem linearRows (h : Entry a m sp z) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram}
    {s : Words} (rows : Rows c q sp s) (kept : Controls b c)
    (frame : RamWriteFrame p q (setupWrites sp))
    (shift : memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j))
    (rem : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j))
    (rep : (SafeGcd.Batch.matrix s).Represents ((2:Int)^count j)
      (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).f (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).g (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1)))) :
    ∃ c' q', Reaches .l108f97 c q .l109036 c' q' ∧ LinearRows b p sp z j s c' q' := by
  have lo := h.depthBound
  have high := h.high
  have hi : sp.toNat + 129 ≤ 2^32 := by omega
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
  have exactF : (2:Int)^count j * (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).f =
      (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).f * s.u.toInt +
        (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).g * s.v.toInt := by
    rw [Int.mul_comm _ s.u.toInt, Int.mul_comm _ s.v.toInt]
    exact rep.1.symm
  have fits := modelFits h.bound (roundsBefore (j+1))
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
  have exactG : (2:Int)^count j * (Verify.Core.Scalars.Inverse.model z (roundsBefore (j+1))).g =
      (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).f * s.q.toInt +
        (Verify.Core.Scalars.Inverse.model z (roundsBefore j)).g * s.r.toInt := by
    rw [Int.mul_comm _ s.q.toInt, Int.mul_comm _ s.r.toInt]
    exact rep.2.symm
  obtain ⟨out₂, exec₂, post₂, g⟩ := runRowShift h hj state args₂ pre₂ df₂
    (by decide) (by decide) exactG fits.2
  have frame₂ := pre₂.trans post₂.frame (calleeWithinLinear lo hi (by decide))
  have head : Reaches .l108f97 c q .l108fe2 out₁.values out₁.store :=
    reachesAfterSampleCall call₁ exec₁ post₁.returned []
  have tail : Reaches .l108fe2 out₁.values out₁.store .l109036 out₂.values out₂.store :=
    reachesAfterSampleCall call₂ exec₂ post₂.returned []
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

end K256.Proofs.Signing.Composition.Attempt.Inverse.Batch
