import AesGcm.Spec.Program

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 AesGcm.Spec.Program

theorem readBytes_of_hasBytes {region : MemoryRegion} {mem : Machine.Ram}
    {bytes : ByteArray} (h : region.HasBytes mem bytes) :
    (List.range region.size).foldlM (fun acc i =>
      match mem[BitVec.ofNat 64 (region.start + i)]? with
      | some byte => Except.ok (acc.push byte)
      | none => Except.error (Machine.Fault.unmappedMemory
          (BitVec.ofNat 64 (region.start + i)))) ByteArray.empty = .ok bytes := by
  have readPrefix (n : Nat) (hn : n ≤ bytes.size) :
      (List.range n).foldlM (fun acc i =>
        match mem[BitVec.ofNat 64 (region.start + i)]? with
        | some byte => Except.ok (acc.push byte)
        | none => Except.error (Machine.Fault.unmappedMemory
            (BitVec.ofNat 64 (region.start + i)))) ByteArray.empty =
        .ok (bytes.extract 0 n) := by
    induction n with
    | zero => simp only [List.range_zero, List.foldlM_nil, ByteArray.extract_same]; rfl
    | succ n ih =>
      have hn' : n < bytes.size := by omega
      have hb := h.2 ⟨n, hn'⟩
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, hb]
      change Except.ok ((bytes.extract 0 n).push bytes[n]) = _
      congr 1
      apply ByteArray.ext
      simp only [ByteArray.data_push, ByteArray.data_extract, ByteArray.getElem_eq_getElem_data,
        Array.push_extract_getElem hn', Nat.zero_min]
  have hs : bytes.size = region.size := h.1
  rw [← hs]
  simpa only [ByteArray.extract_zero_size] using readPrefix bytes.size (Nat.le_refl _)

theorem inplace_readOutput_of_hasBytes {initial final : Machine.RamState} {n : Nat}
    {bytes : ByteArray} (h : (InPlace.outputRegion initial n).HasBytes final.external bytes) :
    InPlace.readOutput initial final n = .ok bytes :=
  readBytes_of_hasBytes h

end AesGcm.Proofs.Machine.Runtime
