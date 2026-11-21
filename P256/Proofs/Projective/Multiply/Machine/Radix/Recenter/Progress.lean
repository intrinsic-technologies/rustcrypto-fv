import P256.Proofs.Projective.Multiply.Machine.Radix.Interface
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Half
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Arithmetic

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective.Multiply.ProjectiveRadix

def rawDigit (d i : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (if i < 64 then nibble d i else 0)

def digitComponents (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .flags, .mem base 65, .rip]

def byteComponents (base : BitVec 64) (i : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .flags,
    .mem (base + BitVec.ofNat 64 i) 1, .rip]

theorem byte_agrees {base : BitVec 64} {t u : RamState} {i : Nat} (hi : i < 65)
    (h : AgreesExcept (byteComponents base i) t u) : AgreesExcept (digitComponents base) t u := by
  apply h.widen
  · intro c hc hm
    simp only [byteComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [digitComponents, Component.isMem]
  · intro a c hc covered
    simp only [byteComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,he⟩ := covered
    have hj0 : j = 0 := by omega
    subst j
    refine ⟨.mem base 65, by simp [digitComponents], i, hi, ?_⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he

theorem byte_unchanged {base : BitVec 64} {t u : RamState} {i j : Nat} (hi : i < 65) (hj : j < 65)
    (ne : j ≠ i) (h : AgreesExcept (byteComponents base i) t u) :
    (Operand.mem (base + BitVec.ofNat 64 j) : Operand 8).read u =
      (Operand.mem (base + BitVec.ofNat 64 j) : Operand 8).read t := by
  apply memLoad_congr
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simp only [BitVec.add_zero]
  change (u.external[base + BitVec.ofNat 64 j]?).getD 0 =
    (t.external[base + BitVec.ofNat 64 j]?).getD 0
  rw [h.byte]
  intro c hc covered
  simp only [byteComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨k,hk,he⟩ := covered
  have hk0 : k = 0 := by omega
  subst k
  simp only [BitVec.add_zero, BitVec.add_right_inj] at he
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2^64 by omega),
    Nat.mod_eq_of_lt (show i < 2^64 by omega)] at hn
  exact ne hn

structure Progress (base : BitVec 64) (t : RamState) (d i : Nat) (reg : BitVec 5) : Prop where
  accumulator : (Operand.reg reg : Operand 8).read t = rawDigit d i + BitVec.ofNat 8 (carry d i)
  centered : ∀ j, j < i → (Operand.mem (base + BitVec.ofNat 64 j) : Operand 8).read t = digitByte d j
  untouched : ∀ j, i < j → j < 65 →
    (Operand.mem (base + BitVec.ofNat 64 j) : Operand 8).read t = rawDigit d j

theorem half_agrees {base : BitVec 64} {t u : RamState} {p offset : BitVec 64} {src dst : BitVec 5} {i : Nat}
    (hs : src = 0 ∨ src = 2) (hd : dst = 0 ∨ dst = 2)
    (addr : halfAddress t offset = base + BitVec.ofNat 64 i)
    (effect : (halfEffect p src dst offset t).Holds t u) :
    AgreesExcept (byteComponents base i) t u := by
  apply effect.agrees.mono
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp [halfEffect, Effect.components, byteComponents, addr]

theorem progress_half {base : BitVec 64} {t u : RamState}
    {d i : Nat} {p offset : BitVec 64} {src dst : BitVec 5}
    (state : Progress base t d i src) (hi : i < 64)
    (hs : src = 0 ∨ src = 2) (hd : dst = 0 ∨ dst = 2)
    (addr : halfAddress t offset = base + BitVec.ofNat 64 i)
    (effect : (halfEffect p src dst offset t).Holds t u) :
    Progress base u d (i+1) dst := by
  have agrees := half_agrees hs hd addr effect
  have nextAddr : halfAddress t (offset+1) = base + BitVec.ofNat 64 (i+1) := by
    rw [BitVec.ofNat_add]
    change halfAddress t (offset+1) = (base) + (BitVec.ofNat 64 i + 1)
    rw [← BitVec.add_assoc, ← addr]
    simp only [halfAddress, BitVec.add_assoc]
  have value : ((Operand.reg src : Operand 64).read t).setWidth 8 =
      BitVec.ofNat 8 (nibble d i + carry d i) := by
    change (Operand.reg src : Operand 8).read t = _
    rw [state.accumulator]
    simp only [rawDigit, ite_eq_left hi, BitVec.ofNat_add]
  have low (a : BitVec 64) : ((a+8).setWidth 32 |>.setWidth 64 |>.setWidth 8) = a.setWidth 8 + 8 := by
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_add _ _ (by decide : 8 ≤ 64)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have hw := congrArg (BitVec.setWidth 8) effect.writes.2.1
    simp only [mergeGPR_low8, low, value, nextAddr] at hw
    rw [carry_byte, state.untouched (i+1) (by omega) (by omega)] at hw
    exact hw.trans (BitVec.add_comm _ _)
  · intro j hj
    by_cases he : j = i
    · subst j
      have hw := effect.writes.2.2.2
      simp only [mergeGPR_low8, low, value, addr] at hw
      exact hw.trans (center_byte d i hi)
    · exact (byte_unchanged (by omega) (by omega) he agrees).trans (state.centered j (by omega))
  · intro j hj hj65
    exact (byte_unchanged (by omega) hj65 (by omega) agrees).trans (state.untouched j (by omega) hj65)

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
