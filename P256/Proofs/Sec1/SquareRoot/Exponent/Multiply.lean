import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.Setup
import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.Call
import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.Copy

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_multiply [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x n y d : Nat} (ctx : ExponentPre s boundary x)
    (hp : ExponentPosition s t x n) (hip : t.RIP = 0x1158a2)
    (hd : d < 16)
    (hdigit : (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 d)
    (hacc : MontgomeryAt t (exponentFrameBase s + 0x30) y) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentPosition s u x n ∧
      u.RIP = 0x1154c0 ∧ MontgomeryAt u (exponentFrameBase s + 0x30)
        (y * (x ^ d % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := by
  obtain ⟨v, hav, hv⟩ := ExponentMultiply.setup ctx hp hip hd hdigit hacc
  obtain ⟨w, fuel, haw, hpw, hipw, hmw⟩ := ExponentMultiply.multiply_call ctx hv hd
  obtain ⟨u, hau, hpu, hipu, hmu⟩ := ExponentMultiply.copy_result ctx hpw hipw hmw
  exact ⟨u, 7 + fuel + 9, (hav.trans haw).trans hau, hpu, hipu, hmu⟩

end P256.Proofs.Sec1.SquareRoot
