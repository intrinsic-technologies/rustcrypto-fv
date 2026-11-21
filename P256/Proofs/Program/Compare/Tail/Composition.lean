import P256.Proofs.Program.Compare.Tail.Support
import P256.Proofs.Program.Compare.Tail.Length
import P256.Proofs.Program.Compare.Ranges

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program.Compare.Ranges (memReadable_slice)

theorem maskedLength_congr {s t : RamState}
    (h : (Operand.reg 1 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s)
    (mask : BitVec 32) : maskedLength t mask = maskedLength s mask := by
  have hh := congrArg (BitVec.setWidth 32) h
  change (Operand.reg 1 : Operand 32).read t = (Operand.reg 1 : Operand 32).read s at hh
  simp only [maskedLength, hh]

theorem byteLength_congr {s t : RamState}
    (h : (Operand.reg 1 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s) :
    byteLength t = byteLength s := by
  have hh := congrArg (BitVec.setWidth 8) h
  change (Operand.reg 1 : Operand 8).read t = (Operand.reg 1 : Operand 8).read s at hh
  simp only [byteLength, hh]

theorem small_length_parts (s : RamState)
    (h : ((Operand.reg 1 : Operand 64).read s).toNat < 16) :
    (maskedLength s 24).toNat + (maskedLength s 4).toNat +
      (maskedLength s 2).toNat + byteLength s = ((Operand.reg 1 : Operand 64).read s).toNat ∧
    (maskedLength s 24 = 0 ∨ maskedLength s 24 = 8) ∧
    (maskedLength s 4 = 0 ∨ maskedLength s 4 = 4) ∧
    (maskedLength s 2 = 0 ∨ maskedLength s 2 = 2) := by
  obtain ⟨hsum, h8, h4, h2, _⟩ := small_length_split ((Operand.reg 1 : Operand 64).read s) h
  have hc (mask : BitVec 32) : (maskedLength s mask).toNat =
      (((Operand.reg 1 : Operand 64).read s).setWidth 32 &&& mask).toNat := by
    unfold maskedLength
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc, hc, hc]
    exact hsum
  · rcases h8 with h8 | h8
    · exact Or.inl (BitVec.eq_of_toNat_eq ((hc 24).trans h8))
    · exact Or.inr (BitVec.eq_of_toNat_eq ((hc 24).trans h8))
  · rcases h4 with h4 | h4
    · exact Or.inl (BitVec.eq_of_toNat_eq ((hc 4).trans h4))
    · exact Or.inr (BitVec.eq_of_toNat_eq ((hc 4).trans h4))
  · rcases h2 with h2 | h2
    · exact Or.inl (BitVec.eq_of_toNat_eq ((hc 2).trans h2))
    · exact Or.inr (BitVec.eq_of_toNat_eq ((hc 2).trans h2))

theorem PhaseSuccess.readable {s t : RamState} {count rest : Nat} {next : BitVec 64}
    (hp : PhaseSuccess s t count next) (hm : t.external = s.external)
    (hl : MemReadable s ((Operand.reg 6 : Operand 64).read s) (count + rest))
    (hr : MemReadable s ((Operand.reg 2 : Operand 64).read s) (count + rest)) :
    MemReadable t ((Operand.reg 6 : Operand 64).read t) rest ∧
      MemReadable t ((Operand.reg 2 : Operand 64).read t) rest := by
  constructor
  · rw [hp.left]
    exact (memReadable_slice hl count rest (by omega)).of_external_eq hm
  · rw [hp.right]
    exact (memReadable_slice hr count rest (by omega)).of_external_eq hm

theorem readable_prefix {s : RamState} {p : BitVec 64} {n count : Nat}
    (h : MemReadable s p n) (hc : count ≤ n) : MemReadable s p count :=
  ⟨by have := h.low; omega, fun i hi ↦ h.mem i (by omega)⟩

theorem frame_trans {s t u : RamState} (ha : AgreesExcept changes s t)
    (hb : AgreesExcept changes t u) : AgreesExcept changes s u :=
  (ha.trans hb).mono (by simp)

theorem frame_boundary {s t : RamState} {boundary : ReturnBoundary}
    (h : AgreesExcept changes s t) (hb : RegisterBoundary boundary s) :
    RegisterBoundary boundary t :=
  hb.of_stack_eq (h.read (n := 64) (by decide))

end P256.Proofs.Program.Compare.Tail
