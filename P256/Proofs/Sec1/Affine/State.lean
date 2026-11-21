import P256.Proofs.Sec1.Affine.Prologue
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Routed [Bindings] (s t : RamState) (tag : UInt8) : Prop extends Frame s t where
  output : t.regValue .rbx = s.regValue .rdi
  input : t.regValue .rsi = s.regValue .rsi
  xPointer : t.regValue .r14 = s.regValue .rsi + 1
  tagRegister : t.regValue .rax = tag.toBitVec.setWidth 64

theorem input_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 80, Stack.region s 3360]) :
    EncodedPointAt t (s.regValue .rsi) bytes := by
  refine ⟨pre.input.1, ?_⟩
  intro i hi
  rw [frame_read frame (region := registerRegion s .rsi 65) ?_ ?_]
  · exact pre.input.2 i hi
  · intro other member
    have h : other = registerRegion s .rdi 80 ∨ other = Stack.region s 3360 := by
      simpa using member
    rcases h with rfl | rfl
    · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide)
    · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)
  · exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t) :
    MemReadable t (s.regValue .rsi) 65 :=
  readable_of_grow
    (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _))
    state.allocated

end P256.Proofs.Sec1.Affine
