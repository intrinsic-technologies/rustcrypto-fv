import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_stack_apart [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    {off len stackOff stackLen : Nat} (hn : off+len ≤ 80) (hs : stackOff+stackLen ≤ 760) :
    RangeApart (s.regValue .rdi+BitVec.ofNat 64 off) len
      (stackPtr t+BitVec.ofNat 64 stackOff) stackLen := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by omega)]
  intro i hi j hj he
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ _
    (ScalarFrame.stack_contains pre.toCalleePre (offset := 760-stackOff) (len := stackLen) (by omega) (by omega) ⟨j,hj,rfl⟩)
  rw [← he,BitVec.add_assoc,← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show off+i < 80 by omega)

theorem output_stack_bytes [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 80])
    {offset len : Nat} (ho : offset ≤ 3360) (hl : len ≤ offset+8) :
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame
  intro region member covered
  have he : region = registerRegion s .rdi 80 := by simpa using member
  subst region
  exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ covered
    (ScalarFrame.stack_contains pre.toCalleePre ho hl ⟨i,hi,rfl⟩)

theorem after_output [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {cs : List Component} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 80])
    (sp : .reg 4 ∉ cs) (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Frame s u := by
  apply state.after_effect pre.toCalleePre (by decide) ready agrees ?_ sp hdf hmxcsr hfcw
  intro c hc a ha
  obtain ⟨r,hr,hin⟩ := writes c hc a ha
  have he : r = registerRegion s .rdi 80 := by simpa using hr
  subst r
  exact ⟨_,by simp,hin⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Output
