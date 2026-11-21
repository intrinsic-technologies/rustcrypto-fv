import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Projective.Multiply.Machine.Radix.Interface
import P256.Proofs.Projective.Multiply.Table

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open P256.Spec.Operations Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

def basePoint : Projective :=
  match domain.G with
  | .affine x y => ⟨x, y, 1⟩
  | .infinity => ⟨0, 1, 0⟩

structure Ready [Bindings] (s t : RamState) (boundary : ReturnBoundary) (d : Nat) : Prop extends
    ScalarFrame.FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10e94e
  output : t.regValue .rbx = s.regValue .rdi
  destination : t.regValue .rdi = stackPtr s - 1880
  source : t.regValue .rsi = stackPtr s - 912
  tableCount : t.regValue .rdx = 1
  digits : t.regValue .rcx = stackPtr s - 1784
  digitCount : t.regValue .r8 = 1
  table : Lookup.TableAt t (stackPtr s - 912) (Projective.table basePoint)
  digitBytes : Bytes t.external (stackPtr s - 1784) 65
    (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i))

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (d : Nat),
    CalleePre s boundary 0x10e6f0 32 65 3352 →
    SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d →
    ∃ t, Ready s t boundary d

end P256.Proofs.Projective.Multiply.Machine.Basepoint
