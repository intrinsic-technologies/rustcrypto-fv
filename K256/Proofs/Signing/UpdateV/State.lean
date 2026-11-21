import K256.Proofs.Verify.LIR.Fn104970.Frame
import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.Hash.Padding.Compression
import K256.Proofs.Verify.Hash.Padding.Tail
import K256.Spec

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.RFC Standards.NIST.SHA2

def keyPad (key : ByteArray) (pad : UInt8) : ByteArray :=
  ⟨(Array.range 64).map fun i => key.data[i]?.getD 0 ^^^ pad⟩

theorem keyPad_size (key : ByteArray) (pad : UInt8) : (keyPad key pad).size = 64 := by
  simp only [keyPad, ByteArray.size, Array.size_map, Array.size_range]

theorem keyPad_getElem (key : ByteArray) (pad : UInt8) (i : Nat) (hi : i < 64) :
    (keyPad key pad)[i]'(by rw [keyPad_size]; exact hi) = key.data[i]?.getD 0 ^^^ pad := by
  simp only [keyPad, ByteArray.getElem_eq_getElem_data, Array.getElem_map, Array.getElem_range]

theorem compressBlocks_keyPad_short (hash : Array UInt32) (key input : ByteArray)
    (pad : UInt8) (short : input.size < 64) :
    compressBlocks hash (keyPad key pad ++ input) = compressBlocks hash (keyPad key pad) := by
  rw [compressBlocks_append _ _ _ (by rw [keyPad_size])]
  simp only [compressBlocks, Nat.div_eq_of_lt short, compressBlocksFrom]

theorem remainderBytes_keyPad_short (key input : ByteArray) (pad : UInt8) (short : input.size < 64) :
    remainderBytes (keyPad key pad ++ input) = input := by
  have start : 64 * ((keyPad key pad ++ input).size / 64) = (keyPad key pad).size := by
    rw [ByteArray.size_append, keyPad_size]
    omega
  rw [remainderBytes, start, ByteArray.size_append]
  exact ByteArray.extract_append_eq_right rfl rfl

theorem hash_keyPads {key input : ByteArray} (size : key.size ≤ 64) :
    SHA256.hashBytes (keyPad key 0x5c ++ SHA256.hashBytes (keyPad key 0x36 ++ input)) =
      HMAC.hmac SHA256.hashBytes 64 key input := by
  simp only [HMAC.hmac, Nat.not_lt_of_ge size, ite_false, keyPad]

structure HmacStateAt (m : Ram) (p : BitVec 64) (key input : ByteArray) : Prop where
  outer : (⟨p.toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key 0x5c)
  buffer : (⟨(p + 64).toNat, input.size % 64⟩ : MemoryRegion).HasBytes m
    (remainderBytes (keyPad key 0x36 ++ input))
  used : memLoad m (p + 127) 8 = BitVec.ofNat 8 (input.size % 64)
  hash : Compression.StateAt m (p + 128) (compressBlocks initialHash (keyPad key 0x36 ++ input))
  count : memLoad m (p + 160) 64 = BitVec.ofNat 64 (1 + input.size / 64)

structure Frame (label : Label) (fr : Activation) (a : Values Value Reg.count) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn104970.frameAt label fr)
  writes : RamWriteFrame fr.original m [fr.region]
  target : a[3] = ⟨64, fr.rdi + 32⟩
  widths : label = .l104c21 → ∀ i : Fin Reg.count, i.val ∈ [5, 12, 13] → a[i].width = 64

end K256.Proofs.Signing.UpdateV
