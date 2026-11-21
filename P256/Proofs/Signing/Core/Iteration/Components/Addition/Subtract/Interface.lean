import P256.Proofs.Signing.Core.Iteration.Components.Addition.State
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program (inProgram_of_textOffset)

structure BlockPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  input : ∀ offset ∈ [0, 8, 16, 24],
    MemReadable s (s.regValue .rcx + BitVec.ofNat 64 offset) 8
  writable : MemWritable s (stackPtr s) 8
  avoids : ∀ a, (Component.mem (stackPtr s) 8).Covers a → ¬ InProgram a

theorem BlockPre.apart {s : RamState} {p : BitVec 64} (h : BlockPre p s)
    (codeOffset codeLen : Nat) (hc : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply h.avoids _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset+j) (by omega)

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
