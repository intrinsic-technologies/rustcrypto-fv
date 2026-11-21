import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec P256.Spec.Program.Routines Program
open Standards.SECG.ECC
open SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def messageRegion (s : RamState) (message : ByteArray) : MemoryRegion :=
  ⟨(memLoad s.external (s.regValue .rdx) 64).toNat, message.size⟩

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends CalleePre s boundary 0x10d570 72 24 9992 where
  count : s.regValue .rcx = 1
  descriptorBounded : (registerRegion s .rdx 16).Bounded
  descriptorAllocated : (registerRegion s .rdx 16).Allocated s.external
  descriptorStack : (registerRegion s .rdx 16).Disjoint (Stack.region s 9992)
  messageLength : memLoad s.external (s.regValue .rdx + 8) 64 = BitVec.ofNat 64 message.size
  messageBounded : (messageRegion s message).Bounded
  messageAllocated : (messageRegion s message).Allocated s.external
  messageStack : (messageRegion s message).Disjoint (Stack.region s 9992)
  messageBytes : (messageRegion s message).HasBytes s.external message
  signatureBounded : (registerRegion s .r8 64).Bounded
  signatureAllocated : (registerRegion s .r8 64).Allocated s.external
  signatureStack : (registerRegion s .r8 64).Disjoint (Stack.region s 9992)

structure InputAt (s : RamState) (key : Curve.Point) (r scalarS : Nat) : Prop where
  key : Sec1.AffineAt s (s.regValue .rsi) key
  r : Nat256At s (s.regValue .r8) r
  scalarS : Nat256At s (s.regValue .r8 + 32) scalarS

def Correct : Prop :=
  ∀ [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {key : Curve.Point} {r scalarS : Nat},
    Pre s boundary message → InputAt s key r scalarS →
    Curve.onCurve Operations.domain key = true → key ≠ .infinity →
    0 < r → r < Operations.domain.n → 0 < scalarS → scalarS < Operations.domain.n →
    ∃ t, CalleeResult s t boundary 24 9992 ∧
      Core.ResultAt t (s.regValue .rdi)
        (Ecdsa.verifies key (Operations.hash message) (r, scalarS))

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 1176

abbrev Frame [Bindings] (s t : RamState) := ScalarFrame.FrameState s t 24 9992 1176

end P256.Proofs.Verifying.Message
