import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Verifying.Combination.Naf.Recoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop
    extends CalleePre s boundary 0x10f350 0 257 168 where
  outputLength : s.regValue .rsi = 257
  inputLength : s.regValue .rcx = 32
  inputBits : s.regValue .r8 = 256
  window : s.regValue .r9 = 5
  sourceBounded : (registerRegion s .rdx 32).Bounded
  sourceAllocated : (registerRegion s .rdx 32).Allocated s.external
  sourceOutput : (registerRegion s .rdx 32).Disjoint (registerRegion s .rdi 257)
  sourceStack : (registerRegion s .rdx 32).Disjoint (Stack.region s 168)

def DigitsAt (s : RamState) (address : BitVec 64) (ds : List Int) : Prop :=
  ∀ i < 257, memLoad s.external (address + BitVec.ofNat 64 i) 8 =
    BitVec.ofInt 8 ((ds[i]?).getD 0)

structure NafAt (s : RamState) (address : BitVec 64) (n : Nat) : Prop where
  length : memLoad s.external address 64 = BitVec.ofNat 64 (digits n).length
  digit : DigitsAt s (address + 8) (digits n)

def Correct : Prop :=
  ∀ [Bindings] (s : RamState) (boundary : ReturnBoundary) (n : Nat),
    Pre s boundary → Nat256At s (s.regValue .rdx) n →
      Bytes s.external (s.regValue .rdi) 257 (fun _ => 0) →
        ∃ t, CalleeResult s t boundary 257 168 ∧
          t.regValue .rax = BitVec.ofNat 64 (digits n).length ∧
          DigitsAt t (s.regValue .rdi) (digits n)

end P256.Proofs.Verifying.Combination.Naf
