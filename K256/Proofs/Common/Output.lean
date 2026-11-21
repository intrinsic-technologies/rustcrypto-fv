import K256.Spec.Program

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86

theorem readRegion_of_hasBytes {s : Machine.RamState} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes s.external bytes) : readRegion s region = .ok bytes := by
  obtain ⟨len, contents⟩ := h
  change bytes.size = region.size at len
  let read (i : Nat) : Except Machine.Fault UInt8 :=
    match s.external[BitVec.ofNat 64 (region.start + i)]? with
    | some b => .ok b
    | none => .error (.unmappedMemory (BitVec.ofNat 64 (region.start + i)))
  have maps (xs : List Nat) (valid : ∀ i ∈ xs, i < bytes.size) :
      xs.mapM read = Except.ok (xs.map fun i => bytes[i]?.getD 0) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      have hi := valid i List.mem_cons_self
      have hr : read i = .ok (bytes[i]?.getD 0) := by
        simp only [read, contents ⟨i, hi⟩, getElem?_pos bytes i hi, Option.getD_some]
      rw [List.mapM_cons, hr, ih (fun j hj => valid j (.tail _ hj))]
      rfl
  have data : ((List.range region.size).map fun i => bytes[i]?.getD 0).toArray = bytes.data := by
    apply Array.ext
    · simp [len]
    · intro i _ hi
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact congrArg (fun x => Option.getD x 0) (getElem?_pos bytes i (by exact hi))
  change ((List.range region.size).mapM read).map _ = _
  rw [maps _ (fun _ hi => len ▸ List.mem_range.mp hi)]
  change Except.ok (ε := Machine.Fault) (ByteArray.mk _) = _
  rw [data]

end K256.Proofs.Common
