import P256.Proofs.Sec1.Affine.Uncompressed.Output.Transfer
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Mask
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Finish

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem transfer_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Masked s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Transferred s u bytes := by
  obtain ⟨n,a,runA,frameA,ripA,ya,effectA,memoryA⟩ :=
    transfer_y pre state.toFrameState state.rip state.output state.y
  have xa := state.x.of_bytes_eq
    (output_stack_bytes pre memoryA (offset := 664) (len := 32) (by decide) (by decide))
  have outputA : a.regValue .rbx = s.regValue .rdi :=
    (effectA.agrees.read (n := 64) (r := 3)
      (by simp [outputYEffect,Effect.components])).trans state.output
  obtain ⟨m,u,runB,frameB,ripB,xu,effectB,_⟩ := transfer_x pre frameA ripA outputA xa
  have keptY := bytes_of_offsets (base := a.regValue .rbx) effectB.agrees
    (offset := 32) (len := 32) (by decide) (by
      intro address count member
      simp only [outputXEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,false_or,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨0,rfl,by decide,Or.inl (by decide)⟩
      · exact ⟨8,rfl,by decide,Or.inl (by decide)⟩
      · exact ⟨16,rfl,by decide,Or.inl (by decide)⟩
      · exact ⟨24,rfl,by decide,Or.inl (by decide)⟩)
  rw [outputA] at keptY
  have total := effectA.agrees.trans effectB.agrees
  refine ⟨n+m,u,runA.trans runB,frameB,ripB,?_,?_,ya.of_bytes_eq keptY,?_,?_⟩
  · exact (total.read (n := 64) (r := 3)
      (by simp [outputXEffect,outputYEffect,Effect.components])).trans state.output
  · simpa using xu
  · exact (congrArg (BitVec.setWidth 8) (total.read (n := 64) (r := 5)
      (by simp [outputXEffect,outputYEffect,Effect.components]))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) (total.read (n := 64) (r := 15)
      (by simp [outputXEffect,outputYEffect,Effect.components]))).trans state.infinity

end P256.Proofs.Sec1.Affine.Uncompressed.Output
