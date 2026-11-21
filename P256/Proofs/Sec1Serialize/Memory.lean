import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem input_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) {i : Nat} (hi : i < 72) :
    t.external[s.regValue .rsi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
  apply frame_read state.frame (region := registerRegion s .rsi 72) ?_
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  intro region member
  have cases : region = registerRegion s .rdi 65 ∨ region = Stack.region s 328 := by
    simpa using member
  rcases cases with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide)
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)

theorem affine_at_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Standards.SECG.ECC.Curve.Point}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312)
    (input : Sec1.AffineAt s (s.regValue .rsi) point) :
    Sec1.AffineAt t (s.regValue .rsi) point := by
  cases point <;>
    refine ⟨input.1.of_bytes_eq (fun i hi => input_byte pre state (by omega)),
      input.2.1.of_bytes_eq ?_, (input_byte pre state (i := 64) (by decide)).trans input.2.2⟩
  all_goals
    intro i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
      input_byte pre state (i := 32+i) (by omega)

end P256.Proofs.Sec1Serialize
