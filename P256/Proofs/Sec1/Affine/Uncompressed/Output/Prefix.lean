import P256.Proofs.Sec1.Affine.Uncompressed.Output.Copy

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Copied [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110c64
  output : t.regValue .rbx = s.regValue .rdi
  result : (Operand.reg 0 : Operand 8).read t = if valid bytes then 1 else 0
  x : Field.MontgomeryAt t (stackPtr s - 744) (canonical (xCoordinate bytes))
  y : Field.MontgomeryAt t (stackPtr s - 712) (canonical (yCoordinate bytes))

theorem copy_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Validated s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Copied s u bytes := by
  obtain ⟨n,a,runA,frameA,ripA,ya,effectA⟩ := copy_y pre state.toFrameState state.rip state.yValue
  have keptX := bytes_of_offsets (base := stackPtr t) effectA.agrees (offset := 512) (len := 32) (by decide) (by
    intro address count member
    simp only [copyYEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
    rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨48,rfl,by decide,Or.inl (by decide)⟩
    · exact ⟨56,rfl,by decide,Or.inl (by decide)⟩
    · exact ⟨64,rfl,by decide,Or.inl (by decide)⟩
    · exact ⟨72,rfl,by decide,Or.inl (by decide)⟩)
  rw [ScalarFrame.scalar_stack_address state.rsp (offset := 512) (by decide) (by decide)] at keptX
  have xa := state.xValue.of_bytes_eq keptX
  obtain ⟨m,u,runB,frameB,ripB,xu,effectB⟩ := copy_x pre frameA ripA xa
  have keptY := bytes_of_offsets (base := stackPtr a) effectB.agrees (offset := 48) (len := 32) (by decide) (by
    intro address count member
    simp only [copyXEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
    rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨16,rfl,by decide,Or.inl (by decide)⟩
    · exact ⟨24,rfl,by decide,Or.inl (by decide)⟩
    · exact ⟨32,rfl,by decide,Or.inl (by decide)⟩
    · exact ⟨40,rfl,by decide,Or.inl (by decide)⟩)
  rw [ScalarFrame.scalar_stack_address frameA.rsp (offset := 48) (by decide) (by decide)] at keptY
  have total := effectA.agrees.trans effectB.agrees
  refine ⟨n+m,u,runA.trans runB,frameB,ripB,?_,?_,xu,ya.of_bytes_eq keptY⟩
  · exact (total.read (n := 64) (r := 3)
      (by simp [copyYEffect,copyXEffect,Effect.components])).trans state.output
  · exact (total.read (n := 8) (r := 0)
      (by simp [copyYEffect,copyXEffect,Effect.components])).trans state.result

end P256.Proofs.Sec1.Affine.Uncompressed.Output
