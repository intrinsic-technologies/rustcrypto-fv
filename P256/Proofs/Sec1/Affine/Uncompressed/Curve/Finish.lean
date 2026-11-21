import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Compare
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.FlagsX
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.FlagsY
import P256.Proofs.Sec1.Affine.Compressed.Setup
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem choice_byte {s t u : RamState} {offset len : Nat}
    (h : AgreesExcept (ScalarFrame.choiceClobbers s 760) t u)
    (apart8 : OffsetsApart (-(768 : BitVec 64)) 8 (-BitVec.ofNat 64 offset) len)
    (apart1 : OffsetsApart (-(769 : BitVec 64)) 1 (-BitVec.ofNat 64 offset) len)
    (bound : 8+len < 2^64) {i : Nat} (hi : i < len) :
    u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc ha
  simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · obtain ⟨j,hj,he⟩ := ha
    apply OffsetsApart.ne apart8 (stackPtr s) hj hi bound
    simpa only [Nat.reduceAdd,BitVec.ofNat_eq_ofNat,BitVec.sub_eq_add_neg] using he.symm
  · obtain ⟨j,hj,he⟩ := ha
    apply OffsetsApart.ne apart1 (stackPtr s) hj hi (by omega)
    simpa only [Nat.reduceAdd,BitVec.ofNat_eq_ofNat,BitVec.sub_eq_add_neg] using he.symm

theorem finish_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Compared s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Validated s u bytes := by
  obtain ⟨a,run0,sa,ipa,va,fa⟩ := flagsX_execute pre state.toFrameState state.rip
  obtain ⟨b,run1,sb,ipb,vb,fb⟩ := Compressed.choice pre sa 0x10beb 0x8480
    (by decide) (by decide +kernel) (by decide +kernel) ipa
  have ma := fa.external (by simp [Component.Covers])
  have yb : b.external[stackPtr s-748]? =
      some (if yCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0) := by
    have h := choice_byte fb (offset := 748) (len := 1)
      (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)
      (by decide) (i := 0) (by decide)
    simp only [BitVec.add_zero] at h
    exact h.trans ((congrArg (fun m : Ram => m[_]?) ma).trans state.yValid)
  have xb : (b.regValue .rax).setWidth 8 =
      (t.regValue .rax).setWidth 8 &&& (t.regValue .r15).setWidth 8 := by
    rw [vb,va]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq]
    rfl
  obtain ⟨c,run2,sc,ipc,vc,fc⟩ := flagsY_execute pre sb ipb
  obtain ⟨u,run3,su,ipu,vu,fu⟩ := Compressed.choice pre sc 0x10bf7 0x8474
    (by decide) (by decide +kernel) (by decide +kernel) ipc
  have mc := fc.external (by simp [Component.Covers])
  have addr : stackPtr b+12 = stackPtr s-748 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sb.rsp (by decide) (by decide)
  have yWord : memLoad b.external (stackPtr b+12) 8 =
      if yCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0 := by
    rw [addr,P256.Proofs.Common.Memory.memLoad8_of_byte yb]
    split <;> rfl
  have final : (Operand.reg 0 : Operand 8).read u = if valid bytes then 1 else 0 := by
    change (u.regValue .rax).setWidth 8 = _
    rw [vu,vc]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq]
    change (((b.regValue .rax).setWidth 8) &&& memLoad b.external (stackPtr b+12) 8) = _
    rw [xb,state.result,state.xValid,yWord]
    have xWidth : ((if xCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0) : BitVec 64).setWidth 8 =
        if xCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0 := by split <;> rfl
    rw [xWidth]
    simpa only [beq_iff_eq] using valid_mask bytes
  refine ⟨2+6+2+6,u,((run0.trans run1).trans run2).trans run3,⟨su,ipu,?_,final,?_,?_⟩⟩
  · exact (fu.read (n := 64) (r := 3) (by simp [ScalarFrame.choiceClobbers])).trans
      ((fc.read (n := 64) (r := 3) (by simp)).trans
        ((fb.read (n := 64) (r := 3) (by simp [ScalarFrame.choiceClobbers])).trans
          ((fa.read (n := 64) (r := 3) (by simp)).trans state.output)))
  · apply state.xValue.of_bytes_eq
    intro i hi
    exact (choice_byte fu (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide) hi).trans
      ((congrArg (fun m : Ram => m[_]?) mc).trans
        ((choice_byte fb (by unfold OffsetsApart; decide +kernel)
          (by unfold OffsetsApart; decide +kernel) (by decide) hi).trans
          (congrArg (fun m : Ram => m[_]?) ma)))
  · apply state.yValue.of_bytes_eq
    intro i hi
    exact (choice_byte fu (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide) hi).trans
      ((congrArg (fun m : Ram => m[_]?) mc).trans
        ((choice_byte fb (by unfold OffsetsApart; decide +kernel)
          (by unfold OffsetsApart; decide +kernel) (by decide) hi).trans
          (congrArg (fun m : Ram => m[_]?) ma)))

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
