import P256.Proofs.Sec1.SquareRoot.Exponent.Position
import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.SquareRoot.ExponentMultiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CallState [Bindings] (s t : RamState) (x n d y : Nat) : Prop
    extends ExponentPosition s t x n where
  rip : t.RIP = 0x1158c5
  left : t.regValue .rsi = exponentFrameBase s + 0x30
  right : t.regValue .rdx = exponentFrameBase s + 0x338 + BitVec.ofNat 64 (32*d)
  output : t.regValue .rdi = exponentFrameBase s + 0x10
  modulus : t.regValue .rcx = s.regValue .rsi + 32
  negativeInverse : t.regValue .r8 = 1
  accumulator : MontgomeryAt t (exponentFrameBase s + 0x30) y

def volatileComponents : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .flags, .rip]

theorem position_of_registers [Bindings] {s t u : RamState} {x n : Nat}
    (h : ExponentPosition s t x n) (hr : ReadyToStep u)
    (ha : AgreesExcept volatileComponents t u) : ExponentPosition s u x n := by
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (ha.external (by simp [volatileComponents, Component.Covers]))
  exact ⟨h.frame.of_registers hr ha (by decide) (by simp [volatileComponents, Component.Covers]),
    h.constants.of_memory he,
    (ha.read (n := 64) (r := 5) (by decide)).trans h.word,
    exponentWordAt_of_memory he h.savedWord,
    (ha.read (n := 64) (r := 14) (by decide)).trans h.window,
    (ha.read (n := 64) (r := 3) (by decide)).trans h.firstWord,
    (ha.read (n := 64) (r := 13) (by decide)).trans h.firstWindow,
    (ha.read (n := 64) (r := 15) (by decide)).trans h.parameterPointer,
    (ha.read (n := 64) (r := 11) (by decide)).trans h.modulus0,
    (ha.read (n := 64) (r := 12) (by decide)).trans h.inverse⟩

end P256.Proofs.Sec1.SquareRoot.ExponentMultiply
