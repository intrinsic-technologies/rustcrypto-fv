import P256.Proofs.Program.Frame
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {entry : BitVec 64} {inputBytes outputBytes stackReserve : Nat}

variable {inputRegister : Syntax.Reg}

theorem input_bytes_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) (frame : MemoryWriteFrame s t #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve])
    (bytes : (registerRegion s inputRegister inputBytes).HasBytes s.external input) :
    (registerRegion s inputRegister inputBytes).HasBytes t.external input := by
  apply frame_hasBytes frame ?_ pre.inputBounded bytes
  intro region hr
  have cases : region = registerRegion s .rdi outputBytes ∨ region = Stack.region s stackReserve := by
    simpa using hr
  rcases cases with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide)
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)

theorem FrameState.input_bytes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : BitVec 64}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (state : FrameState s t outputBytes stackReserve offset)
    (bytes : (registerRegion s inputRegister inputBytes).HasBytes s.external input) :
    (registerRegion s inputRegister inputBytes).HasBytes t.external input :=
  input_bytes_of_frame pre state.frame bytes

end P256.Proofs.Program.ScalarFrame
