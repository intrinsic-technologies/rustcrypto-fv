import P256.Proofs.Sec1.Affine.Uncompressed.Output.Prefix
import P256.Proofs.Sec1.Affine.Uncompressed.Output.FlagStore
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Flags
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Constants
import P256.Proofs.Sec1.Affine.Uncompressed.Output.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Copied s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Prepared s u bytes := by
  have hp : FlagStorePre t := by
    refine ⟨state.rip,?_,?_⟩
    · intro off member
      have hb : off = 80 ∨ off = 88 := by simpa using member
      have h := ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state.toFrameState
        (offset := off) (len := 1) (by decide) (by omega) (by decide)
      exact ⟨h.low, h.mem, h.tables⟩
    · intro off member pc len bound
      have hb : off = 80 ∨ off = 88 := by simpa using member
      exact ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state.toFrameState
        (by decide) (by omega) bound
  obtain ⟨n,a,runA,readyA,_,effectA⟩ := flag_store boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10c64 flagStoreBytes
      (by decide) (by decide +kernel)) hp
  have writes : Curve.StackWrites t (flagStoreEffect t).components := by
    constructor
    · intro address count member
      simp only [flagStoreEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨80,rfl,by decide⟩
      · exact ⟨88,rfl,by decide⟩
    all_goals simp [flagStoreEffect,Effect.components]
  have frameA := Curve.after_stack pre state.toFrameState readyA effectA.agrees writes
  have kept (off : Nat) (member : off = 16 ∨ off = 48) :=
    bytes_of_offsets (base := stackPtr t) effectA.agrees (offset := off) (len := 32) (by omega) (by
      intro address count mem
      simp only [flagStoreEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at mem
      rcases mem with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨80,rfl,by decide,Or.inr (by omega)⟩
      · exact ⟨88,rfl,by decide,Or.inr (by omega)⟩)
  have hx := kept 16 (.inl rfl)
  have hy := kept 48 (.inr rfl)
  rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)] at hx hy
  have xa := state.x.of_bytes_eq hx
  have ya := state.y.of_bytes_eq hy
  obtain ⟨m,b,runB,readyB,_,effectB⟩ := flags_setup boundary pre.outerBoundary a
    (readyToStep frameA.machine frameA.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameA.loaded) 0x10c6d flagsBytes
      (by decide) (by decide +kernel)) effectA.rip
  have frameB := frameA.after_registers readyB effectB.agrees
    (by simp [flagsEffect,Effect.components,Component.Covers]) (by simp [flagsEffect,Effect.components])
  have memoryB := effectB.agrees.external (by simp [flagsEffect,Effect.components,Component.Covers])
  have values := effectB.writes
  simp only [flagsEffect,Write.AllHold] at values
  have destination : stackPtr a+168 = stackPtr s-592 :=
    ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide)
  obtain ⟨u,runC,frameC,ripC,zero,effectC⟩ := copy_constants pre frameB effectB.rip values.2.2.2.2.2.2
    (values.2.2.2.2.2.1.trans destination) values.2.2.2.2.1
  have cb : stackPtr b+168 = stackPtr s-592 :=
    ScalarFrame.scalar_stack_address frameB.rsp (by decide) (by decide)
  have keptC (off : Nat) (member : off = 16 ∨ off = 48) :=
    bytes_of_offsets (base := stackPtr b) effectC (offset := off) (len := 32) (by omega) (by
      intro address count mem
      simp only [constantComponents,List.mem_cons,List.not_mem_nil,or_false,
        Component.mem.injEq,reduceCtorEq,false_or] at mem
      rcases mem with ⟨haddr,hcount⟩
      subst address
      subst count
      exact ⟨168,cb.symm,by decide,Or.inr (by omega)⟩)
  have hxC := keptC 16 (.inl rfl)
  have hyC := keptC 48 (.inr rfl)
  rw [ScalarFrame.scalar_stack_address frameB.rsp (by decide) (by decide)] at hxC hyC
  have total := (effectA.agrees.trans effectB.agrees).trans effectC
  have al : (Operand.reg 0 : Operand 8).read a = if valid bytes then 1 else 0 :=
    (effectA.agrees.read (n := 8) (r := 0) (by simp [flagStoreEffect,Effect.components])).trans state.result
  refine ⟨n+m+9,u,(runA.trans runB).trans runC,frameC,ripC,?_,?_,?_,zero.1,?_,?_,?_,?_,?_⟩
  · exact (total.read (n := 64) (r := 3)
      (by simp [flagStoreEffect,flagsEffect,constantComponents,Effect.components])).trans state.output
  · exact xa.of_bytes_eq (fun i hi => (hxC i hi).trans (by rw [memoryB]))
  · exact ya.of_bytes_eq (fun i hi => (hyC i hi).trans (by rw [memoryB]))
  · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using zero.2.1
  · exact (effectC.read (n := 64) (r := 0) (by simp [constantComponents])).trans
      (values.2.2.2.1.trans destination)
  · exact (effectC.read (n := 64) (r := 14) (by simp [constantComponents])).trans
      (values.2.2.1.trans (ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide)))
  · change ((Operand.reg 5 : Operand 64).read u).setWidth 8 = _
    rw [effectC.read (n := 64) (r := 5) (by simp [constantComponents]),values.1,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),al]
    cases valid bytes <;> rfl
  · change ((Operand.reg 15 : Operand 64).read u).setWidth 8 = _
    rw [effectC.read (n := 64) (r := 15) (by simp [constantComponents]),values.2.1,
      P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,al]

end P256.Proofs.Sec1.Affine.Uncompressed.Output
