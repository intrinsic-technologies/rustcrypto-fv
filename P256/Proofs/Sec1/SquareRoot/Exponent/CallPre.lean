import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery
import P256.Proofs.Sec1.SquareRoot.Parameters
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_montgomery_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x outputOffset : Nat} (ctx : ExponentPre s boundary x)
    (frame : ScalarFrame.FrameState s t 32 1584 1424)
    (pre : Field.BinaryFieldPre t boundary 0x1145e0 160)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (outputBound : outputOffset ≤ 1416) (outputEnd : 32 ≤ outputOffset)
    (modulus : t.regValue .rcx = s.regValue .rsi + 32)
    (inverse : t.regValue .r8 = 1) : MontgomeryPre t boundary := by
  have inputBound : (s.regValue .rsi).toNat + 144 < 2^32 := ctx.inputBounded
  have modulusNat : (t.regValue .rcx).toNat = (s.regValue .rsi).toNat + 32 := by
    rw [modulus, BitVec.toNat_add]
    change ((s.regValue .rsi).toNat + 32) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have subregion : ∀ a, (registerRegion t .rcx 32).Contains a →
      (registerRegion s .rsi 144).Contains a := by
    intro a ha
    change (t.regValue .rcx).toNat ≤ a ∧ a < (t.regValue .rcx).toNat + 32 at ha
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 144
    rw [modulusNat] at ha
    constructor <;> omega
  have bounds := stack_bounds ctx.stack
  have outputNat : (t.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [output]
    exact stack_sub_toNat ctx.stack (by omega)
  have stackNat : (stackPtr t).toNat = (stackPtr s).toNat - 1424 := by
    rw [frame.rsp]
    exact stack_sub_toNat ctx.stack (by decide)
  refine ⟨pre, ?_, ?_, ?_, ?_, ?_, inverse⟩
  · change (t.regValue .rcx).toNat + 32 < 2^32
    rw [modulusNat]
    omega
  · intro a ha
    apply Option.isSome_iff_exists.mp (frame.allocated a _)
    exact Option.isSome_iff_exists.mpr (ctx.inputAllocated a (subregion _ ha))
  · intro a ha hb
    apply ctx.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (subregion _ ha)
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at hb
    rw [outputNat] at hb
    change (stackPtr s).toNat - 1584 ≤ a ∧ a < (Stack.region s 1584).start + (Stack.region s 1584).size
    rw [stack_region_end]
    constructor <;> omega
  · intro a ha hb
    apply ctx.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (subregion _ ha)
    change (stackPtr t).toNat - 160 ≤ a ∧ a < (Stack.region t 160).start + (Stack.region t 160).size at hb
    rw [stack_region_end, stackNat] at hb
    change (stackPtr s).toNat - 1584 ≤ a ∧ a < (Stack.region s 1584).start + (Stack.region s 1584).size
    rw [stack_region_end]
    constructor <;> omega
  · have value := parameters_modulus ctx.residue.2
    rw [modulus]
    refine ⟨value.1, ?_⟩
    intro i hi
    apply Eq.trans _ (value.2 i hi)
    apply frame_read frame.frame _
      (memoryRegion_contains_add ctx.inputBounded (len := 32)
        (by rw [BitVec.toNat_add]; change (s.regValue .rsi).toNat ≤ ((s.regValue .rsi).toNat + 32) % 2^64
            rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [BitVec.toNat_add]; change ((s.regValue .rsi).toNat + 32) % 2^64 + 32 ≤ _
            rw [Nat.mod_eq_of_lt (by omega)]; change _ ≤ (s.regValue .rsi).toNat + 144; omega) hi)
    intro region hr
    have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 1584 := by simpa using hr
    rcases cases with rfl | rfl
    · exact ctx.separation (0 : Fin 3) (1 : Fin 3) (by decide)
    · exact ctx.separation (0 : Fin 3) (2 : Fin 3) (by decide)

end P256.Proofs.Sec1.SquareRoot
