import K256.Proofs.Verify.Core.Scalars.Products.State
import K256.Proofs.Verify.Core.Memory
import K256.Proofs.Common.Field.PowMod

namespace K256.Proofs.Verify.Core.ScalarProduct

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)

abbrev slot (fr : Activation) (off : Nat) := localSp fr + BitVec.ofNat 64 off

def writes (fr : Activation) (dst : Nat) : List MemoryRegion :=
  [⟨(localSp fr - 8).toNat - 321,321⟩, ⟨(slot fr dst).toNat,32⟩]

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
    (e : Entry fr a p digest r s)

include e

theorem belowNat {off : Nat} (h : off ≤ 12456) :
    (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
  have fits : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  have room := e.stackRoom
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, fits]; omega), fits]

theorem slotNat {off : Nat} (h : off ≤ 488) :
    (slot fr off).toNat = fr.rsp.toNat - 488 + off := by
  have lo := e.stackRoom
  have hi := e.low
  have base := belowNat e (off := 488) (by decide)
  change (fr.rsp - 488).toNat = _ at base
  simp only [slot, localSp, BitVec.toNat_add, BitVec.toNat_ofNat, base]
  rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem pushNat : (localSp fr - 8).toNat = fr.rsp.toNat - 496 := by
  rw [localSp, BitVec.sub_sub]
  exact belowNat e (off := 496) (by decide)

theorem writeSlot {m : Ram} (whole : RamWriteFrame fr.original m [fr.region])
    {off len : Nat} (h : off + len ≤ 488) : Writable Extracted.programImage m (slot fr off) len := by
  have low := e.low_toNat
  have room := e.stackRoom
  have pos := slotNat e (off := off) (by omega)
  exact (e.stack.of_frame whole).sub (by omega) (by omega)

theorem writePush {m : Ram} (whole : RamWriteFrame fr.original m [fr.region]) :
    Writable Extracted.programImage m (localSp fr - 8) 8 := by
  have pos := pushNat e
  have low := e.low_toNat
  have room := e.stackRoom
  exact (e.stack.of_frame whole).sub (by omega) (by omega)

theorem outsideWrites {off len dst : Nat} (h : off + len ≤ 488) (hd : dst + 32 ≤ 488)
    (apart : off + len ≤ dst ∨ dst + 32 ≤ off) :
    Outside (writes fr dst) (slot fr off) len := by
  have low := e.low
  have room := e.stackRoom
  have src := slotNat e (off := off) (by omega)
  have dest := slotNat e (off := dst) (by omega)
  have push := pushNat e
  refine ⟨by omega, ?_⟩
  intro q hq
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · right
    change (localSp fr - 8).toNat - 321 + 321 ≤ _
    omega
  · change _ ≤ (slot fr dst).toNat ∨ (slot fr dst).toNat + 32 ≤ _
    omega

theorem writesWithin {dst : Nat} (h : dst + 32 ≤ 488) : RegionsWithin (writes fr dst) [fr.region] := by
  have room := e.stackRoom
  have bottom := e.low_toNat
  have dest := slotNat e (off := dst) (by omega)
  have push := pushNat e
  intro q hq
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  all_goals simp only [Activation.region]; omega

omit e in
theorem inverseBound (v : Nat) : Curve.inverse domain.n v < domain.n := by
  rw [Curve.inverse, Common.Field.PowMod.powMod_eq_pow_mod]
  exact Nat.mod_lt _ (by decide +kernel)

end K256.Proofs.Verify.Core.ScalarProduct
