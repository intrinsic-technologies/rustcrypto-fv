import P256.Proofs.Sec1.Affine.Compact.Normalize.State
import P256.Proofs.Sec1.Affine.Compact.Copy.Transfer
import P256.Proofs.Sec1.Affine.Compact.Copy.Span
import P256.Proofs.Sec1.Affine.Compact.Flags.Store

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem prepare_decode [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Negated s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyDecode s u point := by
  obtain ⟨n,a,runA,frameA,ripA,_,effect⟩ := Copy.transfer_negateX pre state.toFrameState state.rip state.x
  have keepA {offset len : Nat} (ho : offset ≤ 760) (hl : 760-offset+len ≤ 2^64)
      (apart : 760-offset+len ≤ 168 ∨ 200 ≤ 760-offset) :
      ∀ i < len, a.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro i hi
    have h := Copy.negateX_preserves effect hl apart i hi
    simpa only [ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 760-offset)
      state.rsp (by decide) (by omega),Nat.sub_sub_self ho] using h
  obtain ⟨u,runU,frameU,ripU,_,agreesU⟩ := Flags.store_flag pre frameA .negative ripA
  change AgreesExcept [.mem (stackPtr s-528) 1,.rip] a u at agreesU
  have keepU {target len : Nat} := Copy.stack_bytes (target := target) (len := len)
    agreesU (by simp [Component.Covers])
  have total := effect.agrees.trans agreesU
  refine ⟨n+1,u,runA.trans runU,frameU,ripU,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (total.read (n := 64) (r := 3) (by simp [Copy.negateXEffect,Effect.components])).trans state.output
  · apply state.x.of_bytes_eq
    intro i hi
    exact (keepU (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans
      (keepA (by decide) (by decide) (Or.inr (by decide)) i hi)
  · apply state.y.of_bytes_eq
    intro i hi
    exact (keepU (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans
      (keepA (by decide) (by decide) (Or.inl (by decide)) i hi)
  · apply state.negative.of_bytes_eq
    intro i hi
    exact (keepU (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans
      (keepA (by decide) (by decide) (Or.inr (by decide)) i hi)
  · exact (total.read (n := 64) (r := 12) (by simp [Copy.negateXEffect,Effect.components])).trans state.r12
  · exact (total.read (n := 64) (r := 15) (by simp [Copy.negateXEffect,Effect.components])).trans state.r15
  · exact (total.read (n := 64) (r := 13) (by simp [Copy.negateXEffect,Effect.components])).trans state.zero
  · exact (congrArg (BitVec.setWidth 8) (total.read (n := 64) (r := 5)
      (by simp [Copy.negateXEffect,Effect.components]))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) (total.read (n := 64) (r := 14)
      (by simp [Copy.negateXEffect,Effect.components]))).trans state.infinity
  · apply Eq.trans _ state.mask
    apply memLoad_congr
    intro i hi
    have ha := keepA (offset := 748) (len := 1) (by decide) (by decide) (Or.inl (by decide)) i hi
    have hu := keepU (target := 748) (len := 1) (by unfold OffsetsApart; decide +kernel) (by decide) i hi
    change (u.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0
    simpa only [BitVec.ofNat_eq_ofNat] using congrArg (fun value : Option UInt8 => value.getD 0) (hu.trans ha)

end P256.Proofs.Sec1.Affine.Compact.Normalize
