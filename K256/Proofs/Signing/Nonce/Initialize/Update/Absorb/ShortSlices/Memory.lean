import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Iteration
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def regions (fr : Activation) (second last : Bool) : List MemoryRegion :=
  [⟨(sp fr - 8).toNat, 8⟩, ⟨(destination fr second last).toNat, length last⟩,
    ⟨(context fr second + 127).toNat, 1⟩]

macro "short_address" : tactic => `(tactic|
  (simp only [destination, context, sp, source, offset, used, length, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub] at *
   omega))

theorem copiedFrame {fr : Activation} {input : Input} (env : Environment fr input)
    (second last : Bool) (m : Ram) :
    RamWriteFrame m (copied fr second last m) (regions fr second last) := by
  have dep := env.depth
  have lim := env.limit
  apply Sec1.Wrapper.Copy.memCopy_frame
  · apply (RamWriteFrame.refl m _).memStore
    refine ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, ?_⟩
    change (sp fr - 8).toNat + 8 ≤ 2^64
    short_address
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, ?_⟩
    cases second <;> cases last <;> short_address

theorem resultFrame {fr : Activation} {input : Input} (env : Environment fr input)
    (second last : Bool) (m : Ram) :
    RamWriteFrame m (result fr second last m) (regions fr second last) := by
  have dep := env.depth
  have lim := env.limit
  apply (copiedFrame env second last m).memStore
  refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Nat.le_refl _, Nat.le_refl _, ?_⟩
  change (context fr second + 127).toNat + 1 ≤ 2^64
  cases second <;> short_address

theorem resultLocal {fr : Activation} {input : Input} (env : Environment fr input)
    (second last : Bool) : LocalWrites fr (regions fr second last) := by
  have dep := env.depth
  have lim := env.limit
  intro r hr
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [env.low]
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> cases second <;> cases last <;> short_address

theorem outsideResult {fr : Activation}
    (second last : Bool) {p : BitVec 64} {n : Nat} (bound : p.toNat + n ≤ 2^64)
    (push : (sp fr - 8).toNat + 8 ≤ p.toNat)
    (copy : p.toNat + n ≤ (destination fr second last).toNat ∨
      (destination fr second last).toNat + length last ≤ p.toNat)
    (mark : p.toNat + n ≤ (context fr second + 127).toNat ∨
      (context fr second + 127).toNat + 1 ≤ p.toNat) :
    Outside (regions fr second last) p n := by
  refine ⟨bound, fun r hr => ?_⟩
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inr push
  · exact copy
  · exact mark

theorem slotOutside {fr : Activation} {input : Input} (env : Environment fr input)
    (second last : Bool) (off : BitVec 64) (small : off.toNat + 8 ≤ 160) :
    Outside (regions fr second last) (sp fr + off) 8 := by
  have dep := env.depth
  have lim := env.limit
  apply outsideResult <;> cases second <;> cases last <;> short_address

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
