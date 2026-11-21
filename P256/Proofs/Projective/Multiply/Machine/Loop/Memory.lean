import P256.Proofs.Projective.Multiply.Machine.Loop.Interface
import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem table_at [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {offset : BitVec 64}
    (pre : CalleePre s boundary 0x103250 768 96 1400)
    (state : FrameState s t 96 1400 offset)
    (input : Lookup.TableAt s (s.regValue .rsi) table) :
    Lookup.TableAt t (s.regValue .rsi) table := by
  intro i
  apply (input i).of_bytes_eq
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  apply frame_read state.frame (region := registerRegion s .rsi 768) ?_
    (memoryRegion_contains_add pre.inputBounded (len := 768)
      (Nat.le_refl _) (Nat.le_refl _) (show 96*i.val+j < 768 by omega))
  intro region member
  have cases : region = registerRegion s .rdi 96 ∨ region = Stack.region s 1400 := by
    simpa using member
  rcases cases with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide)
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)

end P256.Proofs.Projective.Multiply.Machine.Loop
