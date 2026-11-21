import P256.Proofs.Sec1.Interface
import P256.Proofs.Program.ScalarFrame.State

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open Standards.SECG.ECC

def encodedPoint : Curve.Point → ByteArray
  | .infinity => ⟨Array.replicate 65 0⟩
  | point@(.affine _ _) => Points.encode point

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (point : Curve.Point),
    CalleePre s boundary 0x110d70 72 65 328 →
    Sec1.AffineAt s (s.regValue .rsi) point → s.regValue .rdx = 0 →
    ∃ t, CalleeResult s t boundary 65 328 ∧ t.regValue .rax = s.regValue .rdi ∧
      (registerRegion s .rdi 65).HasBytes t.external (encodedPoint point)

end P256.Proofs.Sec1Serialize
