import P256.Proofs.Signing.Core.Iteration.ReadBeCall

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem call_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (state : ScalarFrame.FrameState s t 65 4584 2288)
    (rip : t.RIP = 0x119090) (source : t.regValue .rdi = s.regValue .rdx)
    (destination : t.regValue .rdx = frameBase s + 1328)
    (count : t.regValue .rsi = 32) (limbs : t.regValue .rcx = 4)
    (bits : t.regValue .r8 = 256) (ret : InProgram (returnBoundary t).rip) :
    ReadBe.Pre t boundary := by
  have hb := stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 2288 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (t.regValue .rdx).toNat = (stackPtr s).toNat - 2280 + 1328 := by
    rw [destination]
    exact NextNonce.base_nat pre (offset := 1328) (by decide)
  have region : registerRegion t .rdi 32 = registerRegion s .rdx 32 := by
    simp only [registerRegion,source]
  apply ReadBeCall.readBe_pre pre state rip destination count limbs bits ret
  · rw [region]
    exact pre.digestBounded
  · rw [region]
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.digestAllocated a ha)))
  · rw [region]
    intro a ha hout
    apply pre.digestStack a ha
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat+32 at hout
    rw [dst] at hout
    change (stackPtr s).toNat-4584 ≤ a ∧ a < (Stack.region s 4584).start+(Stack.region s 4584).size
    rw [stack_region_end]
    constructor <;> omega
  · rw [region]
    intro a ha hout
    apply pre.digestStack a ha
    change (stackPtr t).toNat-128 ≤ a ∧ a < (Stack.region t 128).start+(Stack.region t 128).size at hout
    rw [stack_region_end] at hout
    change (stackPtr t).toNat-128 ≤ a ∧ a < (stackPtr t).toNat+8 at hout
    rw [sp] at hout
    change (stackPtr s).toNat-4584 ≤ a ∧ a < (Stack.region s 4584).start+(Stack.region s 4584).size
    rw [stack_region_end]
    constructor <;> omega

end P256.Proofs.Signing.Core.Iteration.Digest
