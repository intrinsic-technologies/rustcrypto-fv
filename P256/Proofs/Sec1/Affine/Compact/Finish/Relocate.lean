import P256.Proofs.Sec1.Affine.Compact.Finish.State
import P256.Proofs.Sec1.Affine.Compact.Finish.Transfer
import P256.Proofs.Sec1.Affine.Compact.Finish.RelocateSetup
import P256.Proofs.Sec1.Affine.Compact.Finish.Validity
import P256.Proofs.Sec1.Affine.Compact.Finish.Memory
import P256.Proofs.Sec1.Affine.Compressed.Finish.Copy

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame

theorem x_preserves {s t u : RamState} {offset len : Nat}
    (rsp : stackPtr t = stackPtr s - 760) (effect : (xEffect t).Holds t u)
    (bound : offset ≤ 760) (length : len ≤ offset+8)
    (apart : offset+32 ≤ 120 ∨ 120+len ≤ offset) :
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  have h := Uncompressed.Output.bytes_of_offsets (offset := 760-offset) (len := len)
    effect.agrees (by omega) (by
      intro address count member
      simp only [xEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
        Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
        Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨640,rfl,by decide,by omega⟩
      · exact ⟨648,rfl,by decide,by omega⟩
      · exact ⟨656,rfl,by decide,by omega⟩
      · exact ⟨664,rfl,by decide,by omega⟩)
  have addr := scalar_stack_address (frameOffset := 760) (offset := 760-offset) rsp
    (by decide) (by omega)
  simpa only [addr,Nat.sub_sub_self bound] using h

theorem relocate [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Prepared s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Relocated s u point := by
  obtain ⟨n,a,runA,frameA,ripA,xA,effectA⟩ := transfer_x pre state.toFrameState state.rip state.x
  have yA := state.y.of_bytes_eq (x_preserves state.rsp effectA (offset := 88) (len := 32)
    (by decide) (by decide) (Or.inl (by decide)))
  have maskA := (load_preserve (x_preserves state.rsp effectA (offset := 748) (len := 1)
    (by decide) (by decide) (Or.inr (by decide)))).trans state.mask
  obtain ⟨b,runB,frameB,ripB,flagB,agreesB⟩ := Flags.store_flag pre frameA .minimum ripA
  have keepB (offset len : Nat) (h : OffsetsApart (-56) 1 (-BitVec.ofNat 64 offset) len) (small : 1+len<2^64) :=
    preserve (s := s) (offset := offset) (len := len) agreesB (by
      intro address count member
      simp only [Flags.StoreSite.offset,Nat.reduceSub,
        List.mem_cons,List.not_mem_nil,or_false,Component.mem.injEq,reduceCtorEq] at member
      obtain ⟨rfl,rfl⟩ := member
      exact ⟨-56,by simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat],h,small⟩)
  have xB := xA.of_bytes_eq (keepB 120 32 (by unfold OffsetsApart; decide +kernel) (by decide))
  have yB := yA.of_bytes_eq (keepB 88 32 (by unfold OffsetsApart; decide +kernel) (by decide))
  have maskB := (load_preserve (keepB 748 1 (by unfold OffsetsApart; decide +kernel) (by decide))).trans maskA
  have flag : memLoad b.external (stackPtr s-56) 8 = Flags.infinityFlag point := by
    exact flagB.trans ((congrArg (BitVec.setWidth 8)
      (effectA.agrees.read (n := 64) (r := 14) (by simp [xEffect,Effect.components]))).trans state.infinity)
  have represented : point.isSome = true → AffineAt b (stackPtr s-120)
      ((mapped point).getD .infinity) := by
    intro valid
    have address32 : stackPtr s-120+32=stackPtr s-88 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    have address64 : stackPtr s-120+64=stackPtr s-56 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    have byte {v : UInt8} := Compressed.Finish.byte_of_load (byte := v)
      (readable_of_grow (stack_sub_readable pre.stack (offset := 56) (len := 1)
        (by decide) (by decide)) frameB.allocated)
    cases point with
    | none => simp at valid
    | some p =>
      cases p with
      | infinity =>
        change Field.MontgomeryAt b (stackPtr s-120) 0 ∧
          Field.MontgomeryAt b (stackPtr s-120+32) 0 ∧ b.external[stackPtr s-120+64]?=some 1
        rw [address32,address64]
        exact ⟨xB,by simpa [Select.yCoordinate,Spec.Points.compactY] using yB,byte flag⟩
      | affine x y =>
        change Field.MontgomeryAt b (stackPtr s-120) x ∧
          Field.MontgomeryAt b (stackPtr s-120+32) (Spec.Points.compactY y) ∧
            b.external[stackPtr s-120+64]?=some 0
        rw [address32,address64]
        exact ⟨xB,yB,byte flag⟩
  obtain ⟨m,c,runC,readyC,_,effectC⟩ := relocate_setup boundary pre.outerBoundary b
    (readyToStep frameB.machine frameB.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameB.loaded) 0x10548 relocateBytes
      (by decide) (by decide +kernel)) ripB
  have agreesC : AgreesExcept [.reg 2,.reg 6,.reg 1,.reg 7,.rip] b c := effectC.agrees
  have frameC := frameB.after_registers readyC agreesC (by simp [Component.Covers]) (by simp)
  have memoryC := agreesC.external (by simp [Component.Covers])
  have values := effectC.writes
  change c.regValue .rdx=stackPtr b+16 ∧ c.regValue .rsi=stackPtr b+640 ∧
    c.regValue .rcx=9 ∧ c.regValue .rdi=stackPtr b+16 at values
  obtain ⟨d,runD,frameD,ripD,agreesD,copied⟩ := Compressed.Finish.stack_copy pre frameC
    (count := 9) (source := 120) (destination := 744) (codeOffset := 0x1055d)
    (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
    (by decide) (by decide +kernel) effectC.rip
    (values.2.1.trans (scalar_stack_address frameB.rsp (by decide) (by decide)))
    (values.2.2.2.trans (scalar_stack_address frameB.rsp (by decide) (by decide))) values.2.2.1
  have agrees := ((effectA.agrees.trans agreesB).trans agreesC).trans agreesD
  have choiceD : (d.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0 := by
    exact (congrArg (BitVec.setWidth 8) (agrees.read (n := 64) (r := 5)
      (by simp [xEffect,Effect.components,Compressed.Finish.copyComponents]))).trans state.choice
  obtain ⟨u,runU,frameU,ripU,validity,agreesU⟩ := store_validity pre frameD ripD
  have all := agrees.trans agreesU
  have keepU := preserve (s := s) agreesU (offset := 744) (len := 65) (by
    intro address count member
    simp only [Nat.reduceSub,List.mem_cons,List.not_mem_nil,
      or_false,Component.mem.injEq,reduceCtorEq] at member
    obtain ⟨rfl,rfl⟩ := member
    exact ⟨-672,by simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat],by unfold OffsetsApart; decide +kernel,by decide⟩)
  refine ⟨n+1+m+9+1,u,(((runA.trans runB).trans runC).trans runD).trans runU,
    frameU,ripU,?_,?_,?_,?_,?_⟩
  · exact (all.read (n := 64) (r := 3) (by simp [xEffect,Effect.components,Compressed.Finish.copyComponents])).trans state.output
  · have address : stackPtr s-744+72=stackPtr s-672 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    have readable := readable_of_grow (stack_sub_readable pre.stack (offset := 672) (len := 1)
      (by decide) (by decide)) frameU.allocated
    cases point with
    | none =>
      change u.external[stackPtr s-744+72]? = some 0
      rw [address]
      exact Compressed.Finish.byte_of_load readable (validity.trans choiceD)
    | some p =>
      refine ⟨(represented rfl).of_bytes_eq ?_,?_⟩
      · intro i hi
        exact (keepU i hi).trans ((copied i (by omega)).trans (by rw [memoryC]; rfl))
      · rw [address]
        exact Compressed.Finish.byte_of_load readable (validity.trans choiceD)
  · exact (agreesU.read (n := 64) (r := 2) (by simp)).trans
      ((agreesD.read (n := 64) (r := 2) (by simp [Compressed.Finish.copyComponents])).trans
        (values.1.trans (scalar_stack_address frameB.rsp (by decide) (by decide))))
  · exact (congrArg (BitVec.setWidth 8) (agreesU.read (n := 64) (r := 5) (by simp))).trans choiceD
  · apply Eq.trans (load_preserve (preserve (s := s) (agreesD.trans agreesU) (offset := 748) (len := 1) ?_))
      (by rw [memoryC]; exact maskB)
    intro address count member
    simp only [Compressed.Finish.copyComponents,Nat.reduceSub,BitVec.ofNat_eq_ofNat,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or,Component.mem.injEq,reduceCtorEq,Nat.reduceMul] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨-744,by simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat],by unfold OffsetsApart; decide +kernel,by decide⟩
    · exact ⟨-672,by simp only [BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat],by unfold OffsetsApart; decide +kernel,by decide⟩

end P256.Proofs.Sec1.Affine.Compact.Finish
