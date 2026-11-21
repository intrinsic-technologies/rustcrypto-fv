import P256.Proofs.Sec1.Affine.Compressed.Finish.Result
import P256.Proofs.Sec1.Affine.Compact.Finish.Flags
import P256.Proofs.Sec1.Affine.Compact.Finish.PayloadRun
import P256.Proofs.Sec1.Affine.Compact.Finish.Footer
import P256.Proofs.Sec1.Affine.Compact.Finish.State
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame

theorem selected_result [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Selected s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (mapped point) := by
  obtain ⟨n,a,runA,readyA,_,effectA⟩ := flags boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x105aa flagsBytes (by decide) (by decide +kernel))
    ⟨state.rip,stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide),
      stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide)⟩
  have agreesA : AgreesExcept [.reg 0,.flags,.rip] t a := effectA.agrees
  have frameA := state.toFrameState.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have memoryA := agreesA.external (by simp [Component.Covers])
  have outputA := (agreesA.read (n := 64) (r := 3) (by simp)).trans state.output
  obtain ⟨m,b,runB,frameB,ripB,agreesB,copied⟩ := Payload.run pre frameA effectA.rip outputA
  have outputB : b.regValue .rbx = s.regValue .rdi :=
    (agreesB.read (n := 64) (r := 3) (by simp [Payload.components])).trans outputA
  obtain ⟨u,runU,frameU,ripU,kept,infinity,validity⟩ := Footer.run pre frameB ripB outputB
  have rax : (b.regValue .rax).setWidth 8 = infinityValue t := by
    have register : b.regValue .rax = a.regValue .rax :=
      agreesB.read (n := 64) (r := 0) (by simp [Payload.components])
    rw [register]
    have h := congrArg (BitVec.setWidth 8) effectA.writes
    change (a.regValue .rax).setWidth 8 = _ at h
    simpa only [flagsEffect,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] using h
  have rbp : (b.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0 :=
    (congrArg (BitVec.setWidth 8) ((agreesB.read (n := 64) (r := 5) (by simp [Payload.components])).trans
      (agreesA.read (n := 64) (r := 5) (by simp)))).trans state.choice
  rw [rax] at infinity
  rw [rbp] at validity
  have outputReadable := output_writable pre.toCalleePre (by decide) frameU.allocated
  refine ⟨n+m+3,u,(runA.trans runB).trans runU,frameU,ripU,?_⟩
  cases point with
  | none =>
    change u.external[s.regValue .rdi+72]? = some 0
    apply Compressed.Finish.byte_of_load (outputReadable.add 72 (len := 1) (by decide)).toMemReadable
    exact validity
  | some p =>
    have decoded : AffineAt t (stackPtr s-744) ((mapped (some p)).getD .infinity) := state.decoded.1
    refine ⟨decoded.of_bytes_eq ?_, Compressed.Finish.byte_of_load
      (outputReadable.add 72 (len := 1) (by decide)).toMemReadable validity⟩
    intro i hi
    by_cases small : i < 64
    · exact (kept i small).trans ((copied i small).trans
        ((by rw [memoryA] : a.external[stackPtr s-664+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-664+BitVec.ofNat 64 i]?).trans (state.selected rfl i small)))
    · have index : i = 64 := by omega
      subst i
      have address : stackPtr t+80 = stackPtr s-744+64 := by
        rw [state.rsp]
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      have maskAddress : stackPtr t+12=stackPtr s-748 :=
        scalar_stack_address state.rsp (by decide) (by decide)
      have flag : infinityValue t = memLoad t.external (stackPtr s-744+64) 8 := by
        unfold infinityValue
        rw [maskAddress,state.mask,address]
        change (_ ^^^ 1) &&& (-1 : BitVec 8) ^^^ 1 = _
        change (_ ^^^ 1) &&& BitVec.allOnes 8 ^^^ 1 = _
        rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      rw [flag] at infinity
      cases p with
      | infinity =>
        have byte := state.decoded.1.2.2
        rw [P256.Proofs.Common.Memory.memLoad8_of_byte byte] at infinity
        exact (Compressed.Finish.byte_of_load (outputReadable.add 64 (len := 1) (by decide)).toMemReadable infinity).trans byte.symm
      | affine x y =>
        have byte := state.decoded.1.2.2
        rw [P256.Proofs.Common.Memory.memLoad8_of_byte byte] at infinity
        exact (Compressed.Finish.byte_of_load (outputReadable.add 64 (len := 1) (by decide)).toMemReadable infinity).trans byte.symm

end P256.Proofs.Sec1.Affine.Compact.Finish
