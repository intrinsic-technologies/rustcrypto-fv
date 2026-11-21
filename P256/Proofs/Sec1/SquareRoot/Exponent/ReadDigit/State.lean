import P256.Proofs.Sec1.SquareRoot.Exponent.Position

import P256.Proofs.Sec1.SquareRoot.Exponent.Frame
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def digitReadComponents : List Component := [.reg 0, .reg 1, .reg 2, .flags, .rip]

theorem ExponentPosition.of_digit_registers [Bindings] {s t u : RamState} {x n : Nat}
    (h : ExponentPosition s t x n) (hr : ReadyToStep u)
    (ha : AgreesExcept digitReadComponents t u) : ExponentPosition s u x n := by
  have he (a : BitVec 64) : u.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (ha.external (by simp [digitReadComponents, Component.Covers]))
  exact ⟨h.frame.of_registers hr ha (by decide) (by simp [digitReadComponents, Component.Covers]),
    h.constants.of_memory he,
    (ha.read (n := 64) (r := 5) (by decide)).trans h.word,
    exponentWordAt_of_memory he h.savedWord,
    (ha.read (n := 64) (r := 14) (by decide)).trans h.window,
    (ha.read (n := 64) (r := 3) (by decide)).trans h.firstWord,
    (ha.read (n := 64) (r := 13) (by decide)).trans h.firstWindow,
    (ha.read (n := 64) (r := 15) (by decide)).trans h.parameterPointer,
    (ha.read (n := 64) (r := 11) (by decide)).trans h.modulus0,
    (ha.read (n := 64) (r := 12) (by decide)).trans h.inverse⟩

theorem digitReadComponents_trans {s t u : RamState}
    (h : AgreesExcept digitReadComponents s t) (h' : AgreesExcept digitReadComponents t u) :
    AgreesExcept digitReadComponents s u :=
  (h.trans h').mono (fun _ hc => (List.mem_append.mp hc).elim id id)

theorem ExponentConstants.load_exponent_word {s t : RamState} {x n : Nat}
    (h : ExponentConstants s t x) (hn : n < 64) :
    memLoad t.external (exponentFrameBase s + 0x538 + BitVec.ofNat 64 (8 * (n / 16))) 64 =
      BitVec.ofNat 64 (sqrtExponent / 2 ^ (64 * (n / 16))) :=
  h.exponent.memLoad_limb _ (by omega)

theorem ExponentFrame.stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x offset len : Nat} (ctx : ExponentPre s boundary x) (h : ExponentFrame s t)
    (bound : offset + len ≤ 1416) :
    MemReadable t (exponentFrameBase s + BitVec.ofNat 64 offset) len := by
  have hr := ScalarFrame.stack_readable ctx.toCalleePre h.scalarFrame (by decide) bound
  change MemReadable t (t.regValue .rsp + BitVec.ofNat 64 offset) len at hr
  rw [h.rsp] at hr
  exact hr

end P256.Proofs.Sec1.SquareRoot
