import P256.Proofs.Sec1.Affine.Compact.Normalize.State
import P256.Proofs.Sec1.Affine.Compact.Copy.Point
import P256.Proofs.Sec1.Affine.Compact.Flags.Store
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem prepare_original [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Flags.Flagged s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Original s u point := by
  obtain ⟨n,a,runA,frameA,ripA,_,yA,agreesA⟩ :=
    Copy.copy_point pre state.toFrameState state.rip state.x state.y
  have keepA {target len : Nat} := Copy.stack_bytes (target := target) (len := len) agreesA (by simp [Component.Covers])
  have xA : Field.MontgomeryAt a (stackPtr s-480) (Select.xCoordinate point) :=
    state.x.of_bytes_eq (keepA (by unfold OffsetsApart; decide +kernel) (by decide))
  have ySource : Field.MontgomeryAt a (stackPtr s-448) (Select.yCoordinate point) :=
    state.y.of_bytes_eq (keepA (by unfold OffsetsApart; decide +kernel) (by decide))
  obtain ⟨b,runB,readyB,effectB⟩ := (lea_r64_effect_step 0x110308 0x4c (by simp [RexWPrefix])
    4 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl).advances
    (readyToStep frameA.machine frameA.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameA.loaded) 0x10308 _ (by decide) (by decide +kernel))
    ripA (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10310 (by decide)))
  have agreesB : AgreesExcept [.reg 12,.rip] a b := effectB.agrees
  have frameB := frameA.after_registers readyB agreesB (by simp [Component.Covers]) (by simp)
  have memoryB := agreesB.external (by simp [Component.Covers])
  have r12B : b.regValue .r12 = stackPtr s-632 := by
    have h : b.regValue .r12 = stackPtr a+128 := effectB.writes
    exact h.trans (ScalarFrame.scalar_stack_address (frameOffset := 760) frameA.rsp (by decide) (by decide))
  obtain ⟨c,runC,frameC,ripC,_,agreesC⟩ := Flags.store_flag pre frameB .original effectB.rip
  change AgreesExcept [.mem (stackPtr s-600) 1,.rip] b c at agreesC
  have keepC {target len : Nat} := Copy.stack_bytes (target := target) (len := len) agreesC (by simp [Component.Covers])
  have sourceC : Field.MontgomeryAt c (stackPtr s-448) (Select.yCoordinate point) := by
    apply ySource.of_bytes_eq
    intro i hi
    exact (keepC (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans (by simp only [memoryB, BitVec.ofNat_eq_ofNat])
  obtain ⟨m,u,runU,frameU,ripU,negative,effectU⟩ := Copy.transfer_negateY pre frameC ripC sourceC
  have agreesU : AgreesExcept [.mem (stackPtr s-416) 32,.reg 0,.reg 1,.rip] c u := by
    have h : AgreesExcept [.mem (stackPtr c+344) 32,.reg 0,.reg 1,.rip] c u := by
      apply Copy.stack_span effectU.agrees
      · intro d hd hn
        simp only [Copy.negateYEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
          Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro address count hc
        simp only [Copy.negateYEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
          Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
          Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at hc
        rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨344,rfl,by decide,by decide⟩
        · exact ⟨352,rfl,by decide,by decide⟩
        · exact ⟨360,rfl,by decide,by decide⟩
        · exact ⟨368,rfl,by decide,by decide⟩
    simpa only [ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 344) frameC.rsp
      (by decide) (by decide),Nat.reduceSub,BitVec.ofNat_eq_ofNat] using h
  have keepU {target len : Nat} := Copy.stack_bytes (target := target) (len := len) agreesU (by simp [Component.Covers])
  have rest := (agreesB.trans agreesC).trans agreesU
  have total := agreesA.trans rest
  refine ⟨n+1+1+m,u,((runA.trans runB).trans runC).trans runU,frameU,ripU,?_,?_,?_,negative,?_,?_,?_,?_,?_⟩
  · exact (total.read (n := 64) (r := 3) (by simp)).trans state.output
  · apply xA.of_bytes_eq
    intro i hi
    exact (keepU (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans
      ((keepC (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans (by simp only [memoryB, BitVec.ofNat_eq_ofNat]))
  · apply yA.of_bytes_eq
    intro i hi
    exact (keepU (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans
      ((keepC (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans (by simp only [memoryB, BitVec.ofNat_eq_ofNat]))
  · exact ((agreesC.trans agreesU).read (n := 64) (r := 12) (by simp)).trans r12B
  · exact (total.read (n := 64) (r := 13) (by simp)).trans state.zero
  · exact (congrArg (BitVec.setWidth 8) (total.read (n := 64) (r := 5) (by simp))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) (total.read (n := 64) (r := 14) (by simp))).trans state.infinity
  · apply Eq.trans _ state.mask
    apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0
    have ha := keepA (target := 748) (len := 1) (by unfold OffsetsApart; decide +kernel) (by decide) i hi
    have hb : b.external[stackPtr s-BitVec.ofNat 64 748+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 748+BitVec.ofNat 64 i]? := by
      simpa only [memoryB] using ha
    have hc := keepC (target := 748) (len := 1) (by unfold OffsetsApart; decide +kernel) (by decide) i hi
    have hu := keepU (target := 748) (len := 1) (by unfold OffsetsApart; decide +kernel) (by decide) i hi
    simpa only [BitVec.ofNat_eq_ofNat] using congrArg (fun value : Option UInt8 => value.getD 0)
      (hu.trans (hc.trans hb))

end P256.Proofs.Sec1.Affine.Compact.Normalize
