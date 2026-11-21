import K256.Proofs.Verify.Hash.Update.Memory
import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.Hash.Padding.Tail
import K256.Proofs.Verify.LIR.Program

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.Wrapper Verify.LIR

abbrev segment (l : LIR.Label) (a : Vector Value 53) (m : Ram)
    (l' : LIR.Label) (a' : Vector Value 53) (m' : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨l,a,m⟩,[]⟩ ⟨⟨l',a',m'⟩,[]⟩

structure Updated (s : RamState) (input : ByteArray) (hash : Array UInt32)
    (a : Vector Value 53) (m : Ram) (b : Vector Value 53) (m' : Ram) : Prop where
  writes : RamWriteFrame m m' (footprint s)
  rsp : b[4] = ⟨64,localSp s⟩
  kept : ∀ i : Fin 53, i.val ∈ [5,13,22,39,50,51] → b[i] = a[i]
  r12width : b[12].width = 64
  state : Compression.StateAt m' (localSp s + 312) (compressBlocks hash input)
  bytes : (⟨(localSp s + 248).toNat,input.size % 64⟩ : MemoryRegion).HasBytes m' (remainderBytes input)
  len : memLoad m' (localSp s + 311) 8 = BitVec.ofNat 8 (input.size % 64)
  blocks : memLoad m' (localSp s + 344) 64 = BitVec.ofNat 64 (input.size / 64)

theorem stateStore {m : Ram} {p a : BitVec 64} {hash : Array UInt32}
    (state : Compression.StateAt m p hash) {k : Nat} (x : BitVec k)
    (apart : RangeApart a (k / 8) p 32) : Compression.StateAt (memStore m a x) p hash :=
  ⟨state.1, state.2.write_apart _ _ apart⟩

theorem bytesStore {m : Ram} {p a : BitVec 64} {len : Nat} {bytes : ByteArray}
    (hb : (⟨p.toNat,len⟩ : MemoryRegion).HasBytes m bytes) {k : Nat} (x : BitVec k)
    (hap : RangeApart a (k / 8) p len) :
    (⟨p.toNat,len⟩ : MemoryRegion).HasBytes (memStore m a x) bytes := by
  refine ⟨hb.1, fun i => ?_⟩
  have b := hb.2 i
  have hs : bytes.size = len := hb.1
  change (memStore m a x)[BitVec.ofNat 64 (p.toNat + i.val)]? = _
  rw [ofNat_toNat_add, memStore_getElem?_of_ne _ _ _ _ (fun j hj => hap j hj i.val (hs ▸ i.isLt))]
  simpa only [ofNat_toNat_add] using b

end K256.Proofs.Verify.Hash.Update
