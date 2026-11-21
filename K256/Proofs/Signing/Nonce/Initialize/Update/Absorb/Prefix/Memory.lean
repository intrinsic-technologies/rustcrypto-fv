import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Buffer
import K256.Proofs.Signing.UpdateV.Prepare.Append.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.Hash

def taggedMemory (m : Ram) (p src : BitVec 64) (byte : UInt8) : Ram :=
  let copied := UpdateV.Append.stored m (p + 64) src
  let marked := memStore copied (p + 127) (32 : BitVec 8)
  let tagged := memStore marked (p + 96) byte.toBitVec
  memStore tagged (p + 127) (33 : BitVec 8)

local macro "prefix_apart" : tactic =>
  `(tactic| (try simp only [BitVec.add_assoc, BitVec.reduceAdd]
             first | apply RangeApart.of_offsets rfl rfl <;> decide
                   | apply RangeApart.of_offsets rfl (BitVec.add_zero _).symm <;> decide))

private theorem tagByte {m : Ram} {p : BitVec 64} (byte : UInt8) :
    (⟨p.toNat,1⟩ : MemoryRegion).HasBytes (memStore m p byte.toBitVec) ⟨#[byte]⟩ := by
  refine ⟨rfl, fun i => ?_⟩
  have zero : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
  have h := memStore_getElem?_self m p byte.toBitVec (by decide) 0 (by decide)
  simpa [zero, ByteArray.getElem_eq_getElem_data, storedByte] using h

set_option maxHeartbeats 800000 in
theorem taggedState {m : Ram} {p src : BitVec 64} {key value : ByteArray} (byte : UInt8)
    (ctx : UpdateV.HmacStateAt m p key ByteArray.empty)
    (bytes : (⟨src.toNat,32⟩ : MemoryRegion).HasBytes m value)
    (rd : Readable m (p+64) 32) :
    UpdateV.HmacStateAt (taggedMemory m p src byte) p key (value ++ ⟨#[byte]⟩) := by
  let extra : ByteArray := ⟨#[byte]⟩
  have n : value.size = 32 := bytes.1
  have total : (value ++ extra).size = 33 := by rw [ByteArray.size_append,n]; rfl
  change UpdateV.HmacStateAt _ _ _ (value ++ extra)
  have hash := ctx.hash
  rw [UpdateV.compressBlocks_keyPad_short _ _ _ _ (by decide)] at hash
  constructor
  · unfold taggedMemory UpdateV.Append.stored
    iterate 7 (apply Verify.Hash.Update.bytesStore <;> try prefix_apart)
    exact ctx.outer
  · rw [UpdateV.remainderBytes_keyPad_short _ _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
    apply appendBytes
    · rw [n]
      unfold taggedMemory
      iterate 3 (apply Verify.Hash.Update.bytesStore <;> try prefix_apart)
      exact UpdateV.Append.storedBytes bytes rd
    · rw [n]
      change (⟨(p+64+32).toNat,1⟩ : MemoryRegion).HasBytes _ ⟨#[byte]⟩
      rw [show p+64+32 = p+96 by bv_omega]
      unfold taggedMemory
      apply Verify.Hash.Update.bytesStore (tagByte byte) _ (by prefix_apart)
  · rw [total]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [UpdateV.compressBlocks_keyPad_short _ _ _ _ (by omega)]
    unfold taggedMemory UpdateV.Append.stored
    iterate 7 (apply Verify.Hash.Update.stateStore <;> try prefix_apart)
    exact hash
  · rw [total]
    unfold taggedMemory UpdateV.Append.stored
    iterate 7 rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by prefix_apart)]
    exact ctx.count

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix
