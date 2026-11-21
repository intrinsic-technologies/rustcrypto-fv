import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Verify.Core.Scalars.Products.Geometry

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)

abbrev writes (fr : Activation) : List MemoryRegion :=
  [⟨fr.low.toNat, (localSp fr).toNat - fr.low.toNat⟩, ⟨(localSp fr + 8).toNat, 120⟩]

abbrev workSp (fr : Activation) := localSp fr - 0x28e0

abbrev slot (fr : Activation) (k : Nat) := workSp fr + BitVec.ofNat 64 k

def savedGprs : Vector (Fin Reg.count) 6 := #v[3,12,13,14,15,5]

structure CallerFrame (fr : Activation) (entry current : Registers) (m n : Ram) : Prop where
  sp : current[4] = ⟨64, workSp fr⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → current[i].width = 64
  fixedRegs : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → current[i] = entry[i]
  dest : memLoad n (workSp fr) 64 = localSp fr + 8
  saved : ∀ i : Fin 6, (⟨64, memLoad n (slot fr (0x28a8 + 8*i.val)) 64⟩ : Value) = entry[savedGprs[i]]
  ret : memLoad n (slot fr 0x28d8) 64 = 0x10526c
  frame : RamWriteFrame m n (writes fr)

theorem slotNat {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
    (e : Entry fr a p digest r s) {k : Nat} (hk : k ≤ 0x28e0 + 488) :
    (slot fr k).toNat = fr.rsp.toNat - (0x28e0 + 488) + k := by
  have room := e.stackRoom
  have high := e.low
  have raw := ScalarProduct.belowNat e (off := 0x28e0 + 488) (by decide)
  change (fr.rsp - 10952#64).toNat = _ at raw
  simp only [slot, workSp, localSp, BitVec.sub_sub, BitVec.reduceAdd, BitVec.toNat_add,
    raw, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem frameBounds {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat} (e : Entry fr a p digest r s) :
    RegionsWithin (writes fr) [fr.region] ∧
    ∀ k len : Nat, 128 ≤ k → k + len ≤ 488 →
      Outside (writes fr) (localSp fr + BitVec.ofNat 64 k) len := by
  have room := e.stackRoom
  have low := e.low_toNat
  have hi := e.low
  have sp : (localSp fr).toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 488 ≤ fr.rsp.toNat; omega))
  have addr (k : Nat) (hk : k ≤ 488) :
      (localSp fr + BitVec.ofNat 64 k).toNat = (localSp fr).toNat + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
  have dst : (localSp fr + 8).toNat = (localSp fr).toNat + 8 := addr 8 (by decide)
  constructor
  · intro reg hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Activation.region] <;> omega
  · intro k len hlo hhi
    have ha := addr k (by omega)
    refine ⟨by omega, fun reg hr => Or.inr ?_⟩
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega

end K256.Proofs.Verify.Core.Lincomb
