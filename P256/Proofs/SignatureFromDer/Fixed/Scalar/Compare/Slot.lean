import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program (inProgram_of_textOffset)

structure BorrowSlotPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (stackPtr s + 8) 8
  avoids : ∀ a, (Component.mem (stackPtr s + 8) 8).Covers a → ¬ InProgram a

theorem BorrowSlotPre.apart {p : BitVec 64} {s : RamState} (h : BorrowSlotPre p s)
    (offset len : Nat) (hc : offset + len ≤ 118431) :
    RangeApart (stackPtr s + 8) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply h.avoids _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

theorem BorrowSlotPre.avoids_code {p : BitVec 64} {s : RamState} (h : BorrowSlotPre p s)
    (offset : Nat) (bytes : List UInt8) (hc : offset + bytes.length ≤ 118431)
    {e : Effect}
    (hm : ∀ c ∈ e.components, ∀ a len, c = .mem a len → a = stackPtr s + 8 ∧ len = 8) :
    e.Avoids (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) := by
  apply Effect.avoids_codeRange
  intro c hc' a len he
  obtain ⟨rfl, rfl⟩ := hm c hc' a len he
  exact h.apart offset bytes.length hc

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare
