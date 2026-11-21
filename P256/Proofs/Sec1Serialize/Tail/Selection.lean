import P256.Proofs.Sec1Serialize.Tail.Selection.Load
import P256.Proofs.Sec1Serialize.Tail.Selection.Store
import P256.Proofs.Sec1Serialize.Tail.Selection.Advance

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem select_bytes [Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {bytes : ByteArray} {infinity : Bool}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : SelectionEntry s t boundary bytes infinity) :
    ∃ u, SelectionExit s u boundary (selectionBytes infinity bytes) := by
  have zeroSource : Bytes t.external (stackPtr s - 184) 65 (fun _ => 0) := by
    have h := Selection.bytes_of_hasBytes entry.zeroSource
    intro i hi
    simpa only [getElem!_pos (⟨Array.replicate 65 0⟩ : ByteArray) i
        (by simpa only [ByteArray.size, Array.size_replicate] using hi),
      BitVec.ofNat_eq_ofNat, ByteArray.getElem_eq_getElem_data, Array.getElem_replicate] using h i hi
  have initial : Selection.LoopState s t boundary (fun i => bytes[i]!) infinity 0 :=
    ⟨⟨entry.state, entry.execution⟩, entry.rip, entry.choice, entry.index,
      entry.destination, Selection.bytes_of_hasBytes entry.source, zeroSource,
      fun i hi => by omega⟩
  have loop : ∀ index, index ≤ 65 →
      ∃ u, Selection.LoopState s u boundary (fun i => bytes[i]!) infinity index := by
    intro index
    induction index with
    | zero => exact fun _ => ⟨t, initial⟩
    | succ index ih =>
      intro hindex
      obtain ⟨v, hv⟩ := ih (by omega)
      have hi : index < 65 := by omega
      obtain ⟨loaded, hloaded⟩ := Selection.load_byte pre hv hi
      obtain ⟨stored, hstored⟩ := Selection.store_selected pre hloaded hi
      exact Selection.advance_index pre hstored hi
  obtain ⟨u, hu⟩ := loop 65 (by decide)
  refine ⟨u, hu.stage.toFrameState, hu.stage.execution, hu.rip, hu.destination, ?_⟩
  apply Selection.hasBytes_of_bytes
  · cases infinity
    · exact entry.source.1
    · rfl
  · intro i hi
    have h := hu.selected i hi
    cases infinity
    · exact h
    · simpa only [selectionBytes, Bool.true_eq, ↓reduceIte,
        getElem!_pos (⟨Array.replicate 65 0⟩ : ByteArray) i
        (by simpa only [ByteArray.size, Array.size_replicate] using hi),
        ByteArray.getElem_eq_getElem_data,
        BitVec.ofNat_eq_ofNat, Array.getElem_replicate] using h

end P256.Proofs.Sec1Serialize
