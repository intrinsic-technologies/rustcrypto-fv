import P256.Proofs.Sec1.SquareRoot.Compare
import P256.Proofs.Sec1.SquareRoot.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compareWord_eq_zero {s : RamState} {x y : Nat}
    (hx : MontgomeryAt s (stackPtr s + 192) x)
    (hy : MontgomeryAt s (stackPtr s + 48) y) : compareWord s = 0 ↔ x=y := by
  rw [← montgomery_limbs_eq_iff hx hy]
  change compareWord s = 0 ↔ ∀ j < 4,
    (Operand.mem (((Operand.reg 4 : Operand 64).read s + 192) + BitVec.ofNat 64 (8*j)) : Operand 64).read s =
      (Operand.mem (((Operand.reg 4 : Operand 64).read s + 48) + BitVec.ofNat 64 (8*j)) : Operand 64).read s
  have h : compareWord s = 0 ↔
      (Operand.mem ((Operand.reg 4 : Operand 64).read s + 192) : Operand 64).read s =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64).read s ∧
      (Operand.mem ((Operand.reg 4 : Operand 64).read s + 200) : Operand 64).read s =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64).read s ∧
      (Operand.mem ((Operand.reg 4 : Operand 64).read s + 208) : Operand 64).read s =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64).read s ∧
      (Operand.mem ((Operand.reg 4 : Operand 64).read s + 216) : Operand 64).read s =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s + 72) : Operand 64).read s :=
    four_limb_xor_or_eq_zero _ _ _ _ _ _ _ _
  rw [h]
  constructor
  · rintro ⟨h0,h1,h2,h3⟩ j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose] using h0
    · simpa (config := {decide := true}) only [x86_compose] using h1
    · simpa (config := {decide := true}) only [x86_compose] using h2
    · simpa (config := {decide := true}) only [x86_compose] using h3
  · intro h
    exact ⟨by simpa (config := {decide := true}) only [x86_compose] using h 0 (by decide),
      by simpa (config := {decide := true}) only [x86_compose] using h 1 (by decide),
      by simpa (config := {decide := true}) only [x86_compose] using h 2 (by decide),
      by simpa (config := {decide := true}) only [x86_compose] using h 3 (by decide)⟩

end P256.Proofs.Sec1.SquareRoot
