import Md5.Proofs.Buffered.FinalizeReset.Copy.Model
import Md5.Proofs.Buffered.FinalizeReset.Frame
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem length_le (kind : Kind) : kind.length ≤ 64 := by cases kind <;> decide

theorem agrees_reset {kind : Kind} {s t : RamState}
    (h : AgreesExcept (changes kind s) s t) :
    AgreesExcept (FinalizeReset.changes s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [FinalizeReset.changes, Component.isMem]
  · intro address c hc ha
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨.mem (stackPtr s + 8) 152, by simp [FinalizeReset.changes], ?_⟩
    exact Export.covers_shift (offset := 88) (by simpa [BitVec.add_assoc] using ha)
      (by have := length_le kind; omega)

theorem preserves_bytes {kind : Kind} {s t : RamState} {base : BitVec 64}
    {len : Nat} {bytes : Nat → UInt8} (h : AgreesExcept (changes kind s) s t)
    (hb : Bytes s.external base len bytes)
    (ha : RangeApart (stackPtr s + 96) kind.length base len) :
    Bytes t.external base len bytes := by
  apply hb.of_agreesExcept h
  intro i hi c hc hcov
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  obtain ⟨j, hj, he⟩ := hcov
  exact ha j hj i hi he.symm

theorem preserves_buffer {kind : Kind} {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : AgreesExcept (changes kind s) s t)
    (hb : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  have hb' := Block.bytes_of_hasBytes hb
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb'
  have hk := length_le kind
  have hx := preserves_bytes h hb' (RangeApart.offsets (stackPtr s) (a := 96) (b := 232)
    (by omega) (by simp [ByteArray.size]) (Or.inl (by omega)))
  simpa only [ByteArray.size, Vector.size_toArray] using Finalize.hasBytes_of_bytes hx

theorem lastBlock_hasBytes {s t : RamState} {message : ByteArray}
    (h : AgreesExcept (changes .finalBlock s) s t)
    (hcopy : ∀ i < 56, t.external[stackPtr s + 96 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 8 + BitVec.ofNat 64 i]?)
    (hsource : (⟨(stackPtr s + 8).toNat, 64⟩ : MemoryRegion).HasBytes
      s.external (Finalize.lastBlock message))
    (hlength : Bytes s.external (stackPtr s + 152) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8)))) :
    (⟨(stackPtr s + 96).toNat, 64⟩ : MemoryRegion).HasBytes
      t.external (Finalize.lastBlock message) := by
  have hs := Block.bytes_of_hasBytes hsource
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Finalize.size_lastBlock] at hs
  have hp : Bytes t.external (stackPtr s + 96) 56
      (fun i ↦ if message.size % 64 < 56 then (Finalize.firstBlock message)[i]! else 0) := by
    intro i hi
    rw [hcopy i hi, hs i (by omega)]
    simp only [getElem!_pos (Finalize.lastBlock message) i (by rw [Finalize.size_lastBlock]; omega),
      Finalize.getElem_lastBlock_prefix _ _ hi]
  have hl := preserves_bytes h hlength (RangeApart.offsets (stackPtr s)
    (by decide) (by decide) (Or.inl (by decide)))
  have hblock := Finalize.lastBlock_bytes message hp (by simpa [BitVec.add_assoc] using hl)
  have hb := Finalize.hasBytes_of_bytes (by rw [Finalize.size_lastBlock]; exact hblock)
  simpa only [Finalize.size_lastBlock] using hb

end Md5.Proofs.Buffered.FinalizeReset.Copy
