import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Access
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Tail

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open ProjectiveRadix

theorem tail_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t) (hi : i < 65)
    (rip : t.RIP = 0x10ba5e)
    (addr : halfAddress t 8 = stackPtr s - 112 + BitVec.ofNat 64 i) : TailPre t := by
  refine ⟨rip, ?_, ?_⟩
  · rw [addr]
    exact digit_writable pre state hi
  · rw [addr, ← digit_address state i]
    exact state.stack_code (frameOffset := 120) pre (by decide) (by omega) (codeOffset := 0xba5e) (by decide)

theorem tail_agrees {s t u : RamState} {i : Nat}
    (addr : halfAddress t 8 = stackPtr s - 112 + BitVec.ofNat 64 i)
    (effect : (tailEffect t).Holds t u) :
    AgreesExcept (byteComponents (stackPtr s-112) i) t u := by
  apply effect.agrees.mono
  simp only [BitVec.ofNat_eq_ofNat] at addr
  simp [tailEffect, Effect.components, byteComponents, addr]

theorem progress_tail {s t u : RamState} {d i : Nat}
    (state : Progress (stackPtr s-112) t d i 0) (hi : i < 65)
    (addr : halfAddress t 8 = stackPtr s - 112 + BitVec.ofNat 64 i)
    (effect : (tailEffect t).Holds t u) : Progress (stackPtr s-112) u d i 0 := by
  have agrees := tail_agrees addr effect
  refine ⟨?_, ?_, ?_⟩
  · exact (effect.agrees.read (n := 8) (r := 0) (by simp [tailEffect, Effect.components])).trans state.accumulator
  · intro j hj
    exact (byte_unchanged hi (by omega) (by omega) agrees).trans (state.centered j hj)
  · intro j hj hj65
    exact (byte_unchanged hi hj65 (by omega) agrees).trans (state.untouched j hj hj65)

theorem progress_branch {s t u : RamState} {d i : Nat}
    (state : Progress (stackPtr s-112) t d i 0)
    (agrees : AgreesExcept [.rip] t u) : Progress (stackPtr s-112) u d i 0 := by
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨(agrees.read (n := 8) (r := 0) (by simp)).trans state.accumulator, ?_, ?_⟩
  · intro j hj
    change memLoad u.external _ 8 = _
    rw [memory]
    exact state.centered j hj
  · intro j hj hj65
    change memLoad u.external _ 8 = _
    rw [memory]
    exact state.untouched j hj hj65

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
