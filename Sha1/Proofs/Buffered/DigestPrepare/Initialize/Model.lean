import Sha1.Proofs.Buffered.DigestPrepare.Initialize.Frame

namespace Sha1.Proofs.Buffered.DigestPrepare.Initialize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def effect (s : RamState) : Effect where
  rip := 0x100072
  writes :=
    [⟨(.mem (stackPtr s - 8) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 16) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 32) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
     ⟨(.reg 4 : Operand 64), stackPtr s - 312⟩,
     ⟨(.reg 3 : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.reg 15 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
     ⟨(.reg 6 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 64) : Operand 64), 0⟩,
     ⟨(.reg 14 : Operand 64), stackPtr s - 56⟩,
     ⟨(.mem (stackPtr s - 56) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.reg 0 : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.mem (stackPtr s - 48) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.mem (stackPtr s - 40) : Operand 32), 0xc3d2e1f0⟩,
     ⟨(.mem (stackPtr s - 65) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem effect_covers {s : RamState}
    (h : PrologueFrame 0x100010 Digest.minStackBytes s)
    {c : Component} (hc : c ∈ (effect s).components) {address : BitVec 64}
    (hcov : c.Covers address) :
    (⟨(Stack.region s Digest.minStackBytes).start, Digest.minStackBytes⟩ : MemoryRegion).Contains
      address.toNat := by
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim hcov
    | exact h.covers_in_stack 8 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 16 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 24 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 32 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 64 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 56 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 48 8 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 40 4 (by decide +kernel) (by decide) hcov
    | exact h.covers_in_stack 65 1 (by decide +kernel) (by decide) hcov

theorem effect_avoids {s : RamState}
    (h : PrologueFrame 0x100010 Digest.minStackBytes s) :
    (effect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  have ht := effect_covers h hc hcov
  have hl : 656 ≤ (stackPtr s).toNat := h.stack.2.2.1
  apply h.avoids x.1 _ (.inl ⟨x.2, hx⟩)
  change (stackPtr s).toNat - 656 ≤ _ ∧ _ < (stackPtr s).toNat - 656 + 656 at ht
  change (stackPtr s).toNat - 656 ≤ _ ∧ _ < (stackPtr s).toNat - 656 +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 656))
  omega

end Sha1.Proofs.Buffered.DigestPrepare.Initialize
