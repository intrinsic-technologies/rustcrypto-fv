import K256.Proofs.Verify.Core.Scalars.Digest.Prepare
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Verify.Core.Memory

namespace K256.Proofs.Verify.Core.Digest

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine ParseSignature Standards.SECG.ECC

def activation (fr : Activation) (b : Registers) (m : Ram) : Activation :=
  { fr with
    original := stage m (localSp fr), rsp := localSp fr - 8, low := localSp fr - 105,
    ret := 0x10518b, rbx := fr.rdi, r12 := fr.rdx, r13 := fr.rcx, r14 := fr.rsi,
    r15 := fr.r8, rdi := localSp fr + 352, rsi := localSp fr + 8, rdx := b[2].get 64,
    rcx := b[1].get 64, r8 := b[8].get 64, r9 := b[9].get 64 }

def writes (fr : Activation) : List MemoryRegion :=
  [⟨(localSp fr - 105).toNat, 145⟩, buffer (localSp fr + 352) 32]

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
    (e : Entry fr a p digest r s)
include e

local macro "bounds" : tactic => `(tactic|
  (have hlow := e.low
   have hroom := e.stackRoom
   simp only [localSp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

theorem stageFrame (m : Ram) : RamWriteFrame m (stage m (localSp fr)) (writes fr) := by
  have slot (d : BitVec 64) (hd : d.toNat ≤ 32) : InRegions (writes fr) (localSp fr + d) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (localSp fr - 105).toNat ≤ _ ∧ _ + 8 ≤ (localSp fr - 105).toNat + 145 ∧ _
    bounds
  have push : InRegions (writes fr) (localSp fr - 8) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (localSp fr - 105).toNat ≤ _ ∧ _ + 8 ≤ (localSp fr - 105).toNat + 145 ∧ _
    bounds
  unfold stage
  apply RamWriteFrame.memStore _ _ push
  repeat' apply RamWriteFrame.memStore _ _ (slot _ (by decide))
  exact .refl _ _

theorem writesWithin : RegionsWithin (writes fr) [fr.region] := by
  intro reg hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hl := e.low_toNat
  rcases hr with rfl | rfl <;> simp only [Activation.region, buffer] <;> bounds

theorem calleeWithin (b : Registers) (m : Ram) :
    let child := activation fr b m
    RegionsWithin [child.region, buffer child.rdi 32] (writes fr) := by
  intro child reg hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self, Nat.le_refl _, ?_⟩
    change (localSp fr - 105).toNat + ((localSp fr - 8).toNat - (localSp fr - 105).toNat) ≤
      (localSp fr - 105).toNat + 145
    bounds
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩

omit e in
theorem apartWrites {addr : BitVec 64} {n : Nat} (upper : addr.toNat + n ≤ 2^64)
    (stack : (localSp fr - 105).toNat + 145 ≤ addr.toNat ∨ addr.toNat + n ≤ (localSp fr - 105).toNat)
    (out : (localSp fr + 352).toNat + 32 ≤ addr.toNat ∨ addr.toNat + n ≤ (localSp fr + 352).toNat) :
    Outside (writes fr) addr n := by
  refine ⟨upper, fun reg hr => ?_⟩
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact stack.symm
  · exact out.symm

end K256.Proofs.Verify.Core.Digest
