import K256.Proofs.Generate.Generator.Multiply.Coordinates

namespace K256.Proofs.Verify.Wrapper

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine
  Generate.Generator.Multiply

theorem verificationCallOperands {mem : Ram} {sp : BitVec 64} {peer : Projective}
    {digest : ByteArray} {r s : Vector (BitVec 64) 4}
    (room : 8 ≤ sp.toNat) (low : sp.toNat + 416 ≤ 2^32)
    (key : peer.Stored mem (sp + 8))
    (digestAt : (⟨(sp + 128).toNat, 32⟩ : MemoryRegion).HasBytes mem digest)
    (rAt : WordsAt mem (sp + 352) 64 r) (sAt : WordsAt mem (sp + 384) 64 s) :
    let pushed := memStore mem (sp - 8) (0x1033c7 : BitVec 64)
    peer.Stored pushed (sp + 8) ∧
    (⟨(sp + 128).toNat, 32⟩ : MemoryRegion).HasBytes pushed digest ∧
    WordsAt pushed (sp + 352) 64 r ∧ WordsAt pushed (sp + 384) 64 s := by
  let slot := sp - 8
  let regions : List MemoryRegion := [⟨slot.toNat, 8⟩]
  have slotNat : slot.toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have write := (RamWriteFrame.refl mem regions).memStore (a := slot) (0x1033c7 : BitVec 64)
    (show InRegions regions slot 8 from
      ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by omega⟩)
  have apart (off : BitVec 64) (n : Nat) (fit : off.toNat + n ≤ 416) :
      Outside regions (sp + off) n := by
    have addr : (sp + off).toNat = sp.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, fun reg h => ?_⟩
    obtain rfl := List.mem_singleton.mp h
    exact Or.inr (by change slot.toNat + 8 ≤ _; omega)
  dsimp only
  refine ⟨key.of_frame write (apart 8 120 (by decide)), ⟨digestAt.1, ?_⟩,
    rAt.of_frame write (by decide) (apart 352 32 (by decide)),
    sAt.of_frame write (by decide) (apart 384 32 (by decide))⟩
  intro i
  refine (write.outside _ ?_).trans (digestAt.2 i)
  have size : digest.size = 32 := digestAt.1
  have bound := i.isLt
  have addr : (sp + 128).toNat = sp.toNat + 128 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change sp.toNat + 128 < 2^64; omega)]
    rfl
  change Outside regions (BitVec.ofNat 64 ((sp + 128).toNat + i.val)) 1
  have byte : (BitVec.ofNat 64 ((sp + 128).toNat + i.val)).toNat = sp.toNat + 128 + i.val := by
    rw [BitVec.toNat_ofNat, addr, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, fun reg h => ?_⟩
  obtain rfl := List.mem_singleton.mp h
  exact Or.inr (by change slot.toNat + 8 ≤ _; omega)

end K256.Proofs.Verify.Wrapper
