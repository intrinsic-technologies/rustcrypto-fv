import P256.Proofs.Projective.Multiply.Lookup.Value
import P256.Proofs.Program.ScalarFrame.State

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open ProjectiveLookup

def TableAt (s : RamState) (address : BitVec 64) (table : Fin 8 → Projective) : Prop :=
  ∀ i : Fin 8, ProjectiveAt s (address + BitVec.ofNat 64 (96*i.val)) (table i)

abbrev FrameState [Bindings] (s t : RamState) (offset : BitVec 64 := 360) : Prop :=
  ScalarFrame.FrameState s t 96 496 offset

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (table : Fin 8 → Projective) (digit : BitVec 8),
    CalleePre s boundary 0x1044a0 768 96 496 →
    TableAt s (s.regValue .rsi) table →
    (s.regValue .rdx).setWidth 8 = digit →
    ∃ t, CalleeResult s t boundary 96 496 ∧
      ProjectiveAt t (s.regValue .rdi) (signedLookup table digit)

end P256.Proofs.Projective.Multiply.Machine.Lookup
