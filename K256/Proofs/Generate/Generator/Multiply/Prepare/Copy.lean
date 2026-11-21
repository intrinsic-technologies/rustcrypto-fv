import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine

theorem copyGuard {code : CodeMap} {m : Ram} {src dst count pc : BitVec 64}
    {size len : Nat} (read : Readable m src (size * count.toNat))
    (write : StoreOk code m dst (size * count.toNat) pc len)
    (apart : src.toNat + size * count.toNat ≤ dst.toNat ∨ dst.toNat + size * count.toNat ≤ src.toNat) :
    RepMovsOk code m 0 src dst count size pc len :=
  ⟨rfl, read.low, write.low, read.present, write.present, apart, write.tables, write.apart, write.notCode⟩

macro "rep_copy_guard" " using " incl:term : tactic =>
  `(tactic| (
    try apply Or.inr
    apply copyGuard
    · first | assumption | slot_state region | (dsimp only [memCopy]; slot_state region)
    · first | slot_guard using $incl | (dsimp only [memCopy]; slot_guard using $incl)
    · first | assumption | (simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reduceMul]; omega)))

end K256.Proofs.Generate.Generator.Multiply.Prepare
