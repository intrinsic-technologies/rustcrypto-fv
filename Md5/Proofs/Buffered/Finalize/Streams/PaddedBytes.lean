import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Buffered.Update.Calls

namespace Md5.Proofs.Buffered.Finalize.Streams

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure PaddingBytesPre (message : ByteArray) (base : BitVec 64) (s : RamState) : Prop where
  tail : Bytes s.external base (message.size % 64) (fun i ↦ (tailBytes message)[i]!)
  marker : s.external[base + BitVec.ofNat 64 (message.size % 64)]? = some 128
  destination : rdi.read s = base + BitVec.ofNat 64 (message.size % 64 + 1)
  length : (MemoryRoutines.rdx.read s).toNat = 63 - message.size % 64
  zero : UInt8.ofBitVec ((rsi.read s).setWidth 8) = 0
  stack : RangeApart base (message.size % 64 + 1) (pushAddr s) 8

theorem memset_firstBlock_bytes [Bindings] {boundary : ReturnBoundary} {ret base : BitVec 64}
    {message : ByteArray} {s t : RamState} (h : MemsetSiteResult boundary ret s t)
    (hp : PaddingBytesPre message base s) :
    Bytes t.external base 64 (fun i ↦ (firstBlock message)[i]!) := by
  have hprefix (i : Nat) (hi : i < message.size % 64 + 1) :
      t.external[base + BitVec.ofNat 64 i]? = s.external[base + BitVec.ofNat 64 i]? := by
    apply h.agrees.byte
    intro c hc hcover
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    · obtain ⟨j, hj, he⟩ := hcover
      rw [hp.destination] at he
      rw [hp.length] at hj
      have ha : RangeApart base (message.size % 64 + 1)
          (base + BitVec.ofNat 64 (message.size % 64 + 1)) (63 - message.size % 64) := by
        simpa using RangeApart.offsets base (a := 0) (len := message.size % 64 + 1)
          (b := message.size % 64 + 1) (count := 63 - message.size % 64)
          (by omega) (by omega) (Or.inl (by omega))
      exact ha i hi j hj he
    · obtain ⟨j, hj, he⟩ := hcover
      exact hp.stack i hi j hj he
  apply firstBlock_bytes message
  · intro i hi
    exact (hprefix i (by omega)).trans (hp.tail i hi)
  · exact (hprefix _ (by omega)).trans hp.marker
  · intro i hlo hhi
    have hlen : i - (message.size % 64 + 1) < (MemoryRoutines.rdx.read s).toNat := by
      rw [hp.length]
      omega
    have hh := h.fill (i - (message.size % 64 + 1)) hlen
    rw [hp.destination, hp.zero, add_ofNat_add_ofNat,
      Nat.add_sub_cancel' (by omega)] at hh
    exact hh

end Md5.Proofs.Buffered.Finalize.Streams
