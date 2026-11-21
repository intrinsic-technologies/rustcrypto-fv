import Hkdf.Spec.Program
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Memory

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem readOutput_of_hasBytes {region : MemoryRegion} {memory : Ram} {bytes : ByteArray}
    (stored : region.HasBytes memory bytes) : readOutput region memory = .ok bytes := by
  let getByte (i : Nat) : Except Fault UInt8 :=
    match memory[BitVec.ofNat 64 (region.start+i)]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory (BitVec.ofNat 64 (region.start+i)))
  have each (i : Nat) (hi : i < bytes.size) : getByte i = .ok bytes[i] := by
    dsimp only [getByte]
    rw [stored.2 ⟨i, hi⟩]
  have mapped (xs : List Nat) (bound : ∀ i ∈ xs, i < bytes.size) :
      xs.mapM getByte = .ok (xs.map (fun i ↦ bytes[i]?.getD 0)) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      rw [List.mapM_cons, each i (bound i (by simp)), ih (fun j hj ↦ bound j (by simp [hj]))]
      simp only [List.map_cons, getElem?_pos bytes i (bound i (by simp)),
        Option.getD_some]
      rfl
  change ByteArray.mk <$> (Array.range region.size).mapM getByte = .ok bytes
  rw [Array.mapM_eq_mapM_toList, mapped _ (by
    intro i hi
    have bound : i < region.size := by simpa using hi
    have size := stored.1
    change bytes.size = region.size at size
    omega)]
  change Except.ok ⟨((Array.range region.size).toList.map
    (fun i ↦ bytes[i]?.getD 0)).toArray⟩ = .ok bytes
  congr 1
  apply ByteArray.ext
  apply Array.ext
  · simp only [List.size_toArray, List.length_map, Array.length_toList, Array.size_range]
    exact stored.1.symm
  · intro i hi hj
    simp only [List.getElem_toArray, List.getElem_map, Array.getElem_toList,
      Array.getElem_range]
    simp only [getElem?_pos bytes i hj, Option.getD_some]
    rfl

end Hkdf.Proofs.Common.Memory
