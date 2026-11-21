import P256.Proofs.Projective.Multiply.Machine.Radix.State
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem State.scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {d : Nat} {offset : BitVec 64}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t offset)
    (scalar : Nat256At s (s.regValue .rsi) d) : Nat256At t (s.regValue .rsi) d := by
  refine ⟨scalar.1,?_⟩
  intro i hi
  rw [frame_read (state.frame pre) (region := registerRegion s .rsi 32) ?_ ?_]
  · exact scalar.2 i hi
  · intro region hr
    have hm : region = registerRegion s .rdi 65 ∨ region = Stack.region s 136 := by simpa using hr
    rcases hm with rfl|rfl
    · exact pre.separation 0 1 (by decide)
    · exact pre.separation 0 2 (by decide)
  · exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (len := 32)
      (Nat.le_refl _) hi

end P256.Proofs.Projective.Multiply.Machine.Radix
