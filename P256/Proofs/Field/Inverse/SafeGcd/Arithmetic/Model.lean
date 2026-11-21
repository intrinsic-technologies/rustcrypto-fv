import Std.Tactic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd

structure DivState where
  delta : Int
  f : Int
  g : Int
  deriving DecidableEq

def divstep (s : DivState) : DivState :=
  if s.g % 2 = 0 then ⟨s.delta + 2, s.f, s.g / 2⟩
  else if 0 < s.delta then ⟨2 - s.delta, s.g, (s.g - s.f) / 2⟩
  else ⟨s.delta + 2, s.f, (s.g + s.f) / 2⟩

def divsteps : Nat → DivState → DivState
  | 0, s => s
  | n + 1, s => divsteps n (divstep s)

end P256.Proofs.Field.Inverse.SafeGcd
