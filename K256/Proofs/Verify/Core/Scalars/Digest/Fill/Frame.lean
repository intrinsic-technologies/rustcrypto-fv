import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Entry

namespace K256.Proofs.Verify.Core.DigestFill

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open CFG Lift Refine ParseSignature Standards.SECG.ECC

def writes (fr : Activation) : List MemoryRegion :=
  [⟨(localSp fr - 216).toNat,384⟩, buffer (localSp fr + 320) 4]

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
  (e : Entry fr a p digest r s)
include e

local macro "fill_bounds" : tactic => `(tactic|
  (have hlow := e.low
   have hroom := e.stackRoom
   simp only [localSp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

theorem totalWrites {m n t : Ram} {r9 : BitVec 64}
    (setupFrame : RamWriteFrame m n (setupWrites (localSp fr)))
    (calleeFrame : RamWriteFrame n t [(child fr n r9).region, buffer (localSp fr + 136) 32]) :
    RamWriteFrame m t (writes fr) := by
  refine ((RamWriteFrame.refl m (writes fr)).trans setupFrame ?setup).trans calleeFrame ?callee
  case setup =>
    intro reg hr
    simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change (localSp fr - 216).toNat ≤ _ ∧ _ ≤ (localSp fr - 216).toNat + 384
      fill_bounds
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
  case callee =>
    intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rcases hr with rfl | rfl
    · change (localSp fr - 216).toNat ≤ (localSp fr - 216).toNat ∧
        (localSp fr - 216).toNat + ((localSp fr - 8).toNat - (localSp fr - 216).toNat) ≤ (localSp fr - 216).toNat + 384
      fill_bounds
    · simp only [buffer]
      fill_bounds

theorem writesWithin : RegionsWithin (writes fr) [fr.region] := by
  intro reg hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hr
  have hl := e.low_toNat
  rcases hr with rfl | rfl <;> simp only [Activation.region, buffer] <;> fill_bounds

end K256.Proofs.Verify.Core.DigestFill
