import K256.Proofs.Signing.UpdateV.Prepare.Append.Blocks
import K256.Proofs.Signing.UpdateV.Copy
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.Ecdh.Output.Memory

namespace K256.Proofs.Signing.UpdateV.Append

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.Hash

def marked (m : Ram) (sp src : BitVec 64) :=
  memStore (stored m (sp + 168) src) (sp + 231) (32 : BitVec 8)

def pushed (m : Ram) (sp src : BitVec 64) :=
  memStore (marked m sp src) (sp - 8) (0x104c21 : BitVec 64)

theorem storedBytes {m : Ram} {src dst : BitVec 64} {bytes : ByteArray}
    (input : (⟨src.toNat,32⟩ : MemoryRegion).HasBytes m bytes)
    (rd : Readable m dst 32) :
    (⟨dst.toNat,32⟩ : MemoryRegion).HasBytes (stored m dst src) bytes := by
  have move (k : BitVec 64) : src - 344 + (344 + k) = src + k := by bv_omega
  have x := Ecdh.Output.copyHasBytes (bytes := bytes) (sp := src - 344)
    (by simpa only [BitVec.sub_add_cancel] using input) rd
  simp only [Ecdh.Output.copyMemory, stored, BitVec.add_zero, BitVec.sub_add_cancel,
    show src - 344 + 368 = src + 24 from move 24,
    show src - 344 + 360 = src + 16 from move 16,
    show src - 344 + 352 = src + 8 from move 8] at x ⊢
  exact x

local macro "append_apart" : tactic =>
  `(tactic| (try simp only [BitVec.add_assoc, BitVec.reduceAdd]
             first | apply RangeApart.of_offsets rfl rfl <;> decide
                   | apply RangeApart.of_offsets (addr_sub _ _) rfl <;> decide))

set_option maxHeartbeats 800000 in
theorem pushedState {m : Ram} {sp src : BitVec 64} {key value : ByteArray}
    (state : HmacStateAt m (sp+104) key ByteArray.empty)
    (input : (⟨src.toNat,32⟩ : MemoryRegion).HasBytes m value)
    (rd : Readable m (sp+168) 32) :
    HmacStateAt (pushed m sp src) (sp+104) key value := by
  have n : value.size = 32 := input.1
  have short : value.size < 64 := by omega
  have h := state.hash
  rw [compressBlocks_keyPad_short _ _ _ _ (by decide)] at h
  constructor
  · unfold pushed marked stored
    iterate 6 (apply Update.bytesStore <;> try append_apart)
    exact state.outer
  · rw [Nat.mod_eq_of_lt short, n, remainderBytes_keyPad_short _ _ _ short]
    change (⟨(sp + 104 + 64).toNat, 32⟩ : MemoryRegion).HasBytes _ value
    rw [show sp+104+64=sp+168 by bv_omega]
    apply Update.bytesStore <;> try append_apart
    apply Update.bytesStore <;> try append_apart
    exact storedBytes input rd
  · rw [n]
    change memLoad (pushed m sp src) (sp+104+127) 8 = 32
    rw [show sp+104+127=sp+231 by bv_omega, pushed,
      memLoad_memStore_of_rangeApart _ _ _ _ _ (by append_apart)]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [compressBlocks_keyPad_short _ _ _ _ short]
    unfold pushed marked stored
    iterate 6 (apply Update.stateStore <;> try append_apart)
    exact h
  · have old := state.count
    rw [n]
    unfold pushed marked stored
    iterate 6 rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by append_apart)]
    exact old

end K256.Proofs.Signing.UpdateV.Append
