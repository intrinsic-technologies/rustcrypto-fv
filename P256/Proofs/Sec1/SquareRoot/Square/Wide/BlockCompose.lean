import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Common

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide


open X86 X86.Machine X86.UserProcess X86Proofs

theorem memory_read_eq {s t : RamState} {e : Effect} (h : e.Holds s t) (a : BitVec 64)
    (apart : ∀ b n, Component.mem b n ∈ e.components → RangeApart b n a 8) :
    (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply h.agrees.memory
  intro c hc hv
  cases c with
  | mem b n =>
    obtain ⟨j, hj, he⟩ := hv
    exact apart b n hc j hj i hi he.symm
  | _ => exact hv

end P256.Proofs.Sec1.SquareRoot.Square.Wide
