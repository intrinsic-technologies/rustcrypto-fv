import P256.Proofs.Program.Code
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem dec_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (decR64Effect p dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · simp [decR64Effect]
  · simp [decR64Effect, h.read_reg]
  · simp [decR64Effect]
  · cases i <;> simp_all [decR64Effect, decSpec, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [decR64Effect, Write.Full, Operand.Full]

structure BlockPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  input : ∀ offset ∈ [0, 8, 16, 24],
    MemReadable s (s.regValue .rsi + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ [8, 16, 24, 32],
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8
  avoids : ∀ offset len, offset + len ≤ 40 → ∀ a,
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a → ¬ InProgram a

theorem BlockPre.apart {s : RamState} {p : BitVec 64} (h : BlockPre p s)
    (offset len : Nat) (hs : offset + len ≤ 40)
    (codeOffset codeLen : Nat) (hc : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply h.avoids offset len hs _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset+j) (by omega)

end P256.Proofs.Verifying.Core.Reduce
