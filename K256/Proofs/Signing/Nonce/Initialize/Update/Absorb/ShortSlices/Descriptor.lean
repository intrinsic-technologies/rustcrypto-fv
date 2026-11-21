import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem descriptor {fr : Activation} {m : Ram} {secret reduced : ByteArray}
    (env : Environment fr (.seeded secret reduced))
    (written : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,64⟩]) (last : Bool) :
    let p := fr.rsi + BitVec.ofNat 64 (offset last)
    Readable m p 8 ∧ Readable m (p+8) 8 ∧ memLoad m p 64 = source fr last ∧
      memLoad m (p+8) 64 = BitVec.ofNat 64 (length last) ∧ Readable m (source fr last) (length last) := by
  obtain ⟨_, _, _, lim, rd, _, _, ptr, size, emptyPtr, zero, _, bytes⟩ := env.slicesAt written
  change fr.rsp.toNat + 352 < 2^32 at lim
  have reducedLen : reduced.size = 32 := bytes.1
  have bound : (MemoryRegion.mk (fr.rsp + 208).toNat 32).Bounded := by
    change (fr.rsp + 208).toNat + 32 < 2^32
    short_address
  have sourceRead := Readable.of_hasBytes bytes bound
  change Readable m (BitVec.ofNat 64 (fr.rsp+208).toNat) reduced.size at sourceRead
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,reducedLen] at sourceRead
  change Readable m fr.rsi 48 at rd
  dsimp only
  refine ⟨rd.of_offsets rfl (BitVec.add_zero _).symm (by cases last <;> decide),
    rd.of_offsets (BitVec.add_assoc ..) (BitVec.add_zero _).symm (by cases last <;> decide), ?_⟩
  cases last
  · exact ⟨ptr, (by simpa only [length, offset, Bool.false_eq_true, ite_false, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using size), sourceRead⟩
  · refine ⟨emptyPtr, ?_, ⟨by change 1 + 0 ≤ 2^32; decide, by intro i hi; exact (Nat.not_lt_zero _ hi).elim⟩⟩
    simpa only [length, offset, Bool.true_eq, ite_true, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using zero

theorem copiedStop {fr : Activation} {input : Input} {m : Ram} (env : Environment fr input)
    (second last : Bool) (slots : Slots fr m) :
    memLoad (copied fr second last m) (sp fr + 8) 64 = fr.rsi + 48 := by
  have writes := copiedFrame env second last m
  exact (writes.memLoad_eq (slotOutside env second last 8 (by decide))).trans slots.stop

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
