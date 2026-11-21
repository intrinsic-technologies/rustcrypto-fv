import X86Proofs.Program.Compose
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Paging
import X86Proofs.Step.Sse
import Prelude.Execution.Termination

namespace Hkdf.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs Prelude

structure Readable (mem : Ram) (a : BitVec 64) (len : Nat) : Prop where
  low : a.toNat + len ≤ 2 ^ 32
  present : ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome

structure Writable (code : CodeMap) (mem : Ram) (a : BitVec 64) (len : Nat) : Prop where
  readable : Readable mem a len
  tables : PageTableEntriesApart a.toNat len
  notCode : ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i

private theorem add_ofNat_sub {a b : BitVec 64} (hba : b.toNat ≤ a.toNat) (i : Nat)
    (hi : a.toNat + i < 2 ^ 64) :
    a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (a.toNat - b.toNat + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := a.toNat - b.toNat + i) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem Readable.sub {m : Ram} {a b : BitVec 64} {len n : Nat}
    (h : Readable m b len) (h₁ : b.toNat ≤ a.toNat)
    (h₂ : a.toNat + n ≤ b.toNat + len) : Readable m a n := by
  have hl := h.low
  refine ⟨by omega, fun i hi => ?_⟩
  rw [add_ofNat_sub h₁ i (by omega)]
  exact h.present _ (by omega)

theorem Writable.sub {code : CodeMap} {m : Ram} {a b : BitVec 64} {len n : Nat}
    (h : Writable code m b len) (h₁ : b.toNat ≤ a.toNat)
    (h₂ : a.toNat + n ≤ b.toNat + len) : Writable code m a n := by
  have hl := h.readable.low
  refine ⟨h.readable.sub h₁ h₂, h.tables.sub h₁ h₂, fun x hx i hi => ?_⟩
  rw [add_ofNat_sub h₁ i (by omega)]
  exact h.notCode x hx _ (by omega)

end Hkdf.Proofs.Refine
