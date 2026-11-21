import K256.Proofs.Signing.Hash.Finish.Memory
import K256.Proofs.Verify.Hash.FinalBlocks.Bytes

namespace K256.Proofs.Signing.Hash.Finish

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine K256.Proofs.Verify.Hash

theorem stagedBytes (m : Ram) (sp high ret : Word) (block : ByteArray)
    (dst : Readable m (sp+256) 64)
    (bytes : (⟨(sp+160).toNat,64⟩ : MemoryRegion).HasBytes (FinalBlocks.stage m sp high ret) block) :
    (⟨(sp+256).toNat,64⟩ : MemoryRegion).HasBytes (stage m sp high ret) block := by
  refine ⟨bytes.1, fun i => ?_⟩
  have size : block.size = 64 := bytes.1
  have hi : i.val < 64 := size ▸ i.isLt
  let lane : Fin 8 := ⟨i.val / 8, by omega⟩
  have equal := (stage_word m sp high ret lane).trans (FinalBlocks.stage_word m sp high ret lane).symm
  have eqByte := congrArg (fun x : Word => storedByte x (i.val%8)) equal
  have address (p : Word) : wordAddr p 64 lane.val + BitVec.ofNat 64 (i.val%8) =
      p + BitVec.ofNat 64 i.val := by
    rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg _ (congrArg (BitVec.ofNat 64) (Nat.div_add_mod i.val 8))
  have rem : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [storedByte_memLoad _ _ _ rem, storedByte_memLoad _ _ _ rem,address,address] at eqByte
  have present : Readable (stage m sp high ret) (sp+256) 64 := by
    unfold stage
    repeat' apply Readable.memStore
    exact dst
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (present.present i.val hi)
  have src := bytes.2 i
  change (FinalBlocks.stage m sp high ret)[BitVec.ofNat 64 ((sp+160).toNat+i.val)]? = some block[i.val] at src
  rw [ofNat_toNat_add] at src
  change (stage m sp high ret)[BitVec.ofNat 64 ((sp+256).toNat+i.val)]? = _
  rw [ofNat_toNat_add,hv]
  simpa only [memByte, PhysicalMemory.read,hv,src,Option.getD_some] using congrArg some eqByte

end K256.Proofs.Signing.Hash.Finish
