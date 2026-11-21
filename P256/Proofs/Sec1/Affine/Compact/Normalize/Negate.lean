import P256.Proofs.Sec1.Affine.Compact.Normalize.State
import P256.Proofs.Sec1.Affine.Compact.Normalize.Arguments
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame FieldCall

def negativeLayout : StackCallLayout 3360 32 32 24 :=
  ⟨768,416,560,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem negate [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Original s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Negated s u point := by
  obtain ⟨n,v,runV,readyV,_,effect⟩ := negative_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10358 negativeBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [negativeEffect,Effect.components,Component.Covers])
  have frame := state.toFrameState.after_registers readyV effect.agrees
    (by simp [negativeEffect,Effect.components,Component.Covers]) (by simp [negativeEffect,Effect.components])
  have values := effect.writes
  change v.regValue .r15 = stackPtr t + 200 ∧ v.regValue .rsi = stackPtr t + 344 ∧
    v.regValue .rdi = stackPtr t + 200 at values
  obtain ⟨m,u,runU,frameU,ripU,negative,saved,kept,_⟩ := unary_call
    (resultAt := fun u address => Field.MontgomeryAt u address
      ((Spec.Operations.domain.p-Select.yCoordinate point) % Spec.Operations.domain.p))
    pre.toCalleePre frame negativeLayout rfl (by decide) 0x1036b 0x3460 (by decide)
    (by decide +kernel) (by decide) (by decide) (inProgram_of_textOffset 0x137d0 (by decide))
    (fun v hp hx => Projective.Multiply.Machine.Lookup.Negate.negate_correct hp hx)
    effect.rip
    (values.2.1.trans (scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide)))
    (values.2.2.trans (scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide)))
    (state.negativeInput.of_bytes_eq (fun i hi => by rw [memory]; rfl))
  have keep : ∀ offset len : Nat, offset ≤ 760 → len ≤ offset + 8 →
      (offset+32 ≤ 560 ∨ 560+len ≤ offset) →
      ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro offset len ho hl ha i hi
    exact (kept offset len ho hl ha i hi).trans (by rw [memory])
  refine ⟨n+m,u,runV.trans runU,frameU,ripU,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [negativeEffect,Effect.components])).trans state.output)
  · exact state.x.of_bytes_eq (keep 480 32 (by decide) (by decide) (Or.inl (by decide)))
  · exact state.y.of_bytes_eq (keep 632 32 (by decide) (by decide) (Or.inr (by decide)))
  · have bound := state.negativeInput.1
    have model : Spec.Points.negElement (Select.yCoordinate point) =
        (Spec.Operations.domain.p-Select.yCoordinate point) % Spec.Operations.domain.p := by
      simp only [Spec.Points.negElement,Curve.fieldSub,Nat.zero_mod,Nat.zero_add,Nat.mod_eq_of_lt bound]
    rwa [model]
  · exact (saved .r12 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 12) (by simp [negativeEffect,Effect.components])).trans state.r12)
  · exact (saved .r15 (by simp)).trans
      (values.1.trans (scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide)))
  · exact (saved .r13 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 13) (by simp [negativeEffect,Effect.components])).trans state.zero)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [negativeEffect,Effect.components])))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) ((saved .r14 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 14) (by simp [negativeEffect,Effect.components])))).trans state.infinity
  · apply Eq.trans _ state.mask
    apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0
    simpa only [BitVec.ofNat_eq_ofNat] using congrArg (fun value : Option UInt8 => value.getD 0)
      (keep 748 1 (by decide) (by decide) (Or.inr (by decide)) i hi)

end P256.Proofs.Sec1.Affine.Compact.Normalize
