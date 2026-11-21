import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.State
import P256.Proofs.Program.Input
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

open P256.Proofs.Program (readable_of_grow CalleePre inProgram_of_textOffset memoryRegion_contains_add memoryRegion_memReadable )

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : FrameState s t) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 40 :=
  P256.Proofs.Program.ScalarFrame.output_writable pre (by decide) state.allocated

theorem output_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) {offset len : Nat}
    (bound : offset + len ≤ 118431) : RangeApart (s.regValue .rdi) 40
      (Extracted.textAddress + BitVec.ofNat 64 offset) len :=
  P256.Proofs.Program.ScalarFrame.output_code pre bound

theorem output_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ 40)
    (covered : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion s .rdi 40).Contains a.toNat :=
  P256.Proofs.Program.ScalarFrame.output_contains pre bound covered

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish
