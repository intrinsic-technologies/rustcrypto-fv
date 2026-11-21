import Sha1.Proofs.Buffered.Update.Slices.FilledBlock

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short_absorbed [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u v t : RamState} (h : UpdatePre .updateFinalize boundary message input s)
    (hsize : input.size < 64 - message.size % 64)
    (hext : u.external = s.external) (hsp : stackPtr u = stackPtr s)
    (hdi : rdi.read u = UpdateKind.updateFinalize.context s + BitVec.ofNat 64 (message.size % 64))
    (hsi : rsi.read u = (Operand.reg 14 : Operand 64).read s)
    (hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 input.size)
    (hc : MemcpySiteResult boundary 0x101cc7 u v)
    (ha : AgreesExcept [.reg 3, .flags, .rip, .mem (UpdateKind.updateFinalize.context s + 63) 1] v t)
    (hp : (Operand.mem (UpdateKind.updateFinalize.context s + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size)) :
    Absorbed (UpdateKind.updateFinalize.context s) (message ++ input) t := by
  let base := UpdateKind.updateFinalize.context s
  obtain ⟨copied, hstate, hblocks⟩ :=
    buffer_after_copy h hext hsp hdi hsi hdx (Nat.le_refl _) (by omega) hc
  rw [ByteArray.extract_zero_size] at copied
  have preserveStore {i : Nat} (hi : i < 92) (hne : i ≠ 63) :
      t.external[base + BitVec.ofNat 64 i]? = v.external[base + BitVec.ofNat 64 i]? := by
    apply ha.byte
    intro c hm hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals try exact hx.elim
    obtain ⟨j, hj, he⟩ := hx
    change base + _ = base + 63 + _ at he
    rw [show j = 0 by omega, BitVec.add_zero] at he
    have heq := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp he)
    change i % 2^64 = 63 at heq
    omega
  have hcounts := Wrapper.Absorb.append_short_counts message input hsize
  have htail : tailBytes (message ++ input) = tailBytes message ++ input :=
    Wrapper.Absorb.remainderBytes_append_short _ _ hsize
  refine ⟨?_, ?_, by rw [size_tailBytes, hcounts.2]; exact hp, ?_⟩
  · have hs : absorbedStateBytes (message ++ input) = absorbedStateBytes message :=
      congrArg Wrapper.Hash.Serialize.stateBytes (absorbedHash_append_short _ _ hsize)
    rw [hs]
    refine ⟨hstate.1, fun i ↦ Eq.trans ?_ (hstate.2 i)⟩
    have hi : i.val < 20 := (absorbedStateBytes_size message) ▸ i.isLt
    change t.external[BitVec.ofNat 64 ((base + 72).toNat + i.val)]? =
      v.external[BitVec.ofNat 64 ((base + 72).toNat + i.val)]?
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
      using preserveStore (i := 72 + i.val) (by omega) (by omega)
  · rw [htail]
    refine ⟨copied.1, fun i ↦ Eq.trans ?_ (copied.2 i)⟩
    have hi := i.isLt
    simp only [ByteArray.size_append, size_tailBytes] at hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      preserveStore (i := i.val) (by omega) (by omega)
  · rw [hcounts.1, ← hblocks]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[base + 64 + BitVec.ofNat 64 i]? = v.external[base + 64 + BitVec.ofNat 64 i]?
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      preserveStore (i := 64 + i) (by omega) (by omega)

end Sha1.Proofs.Buffered.Update.Slices
