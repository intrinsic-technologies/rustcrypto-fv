import P256.Proofs.Program.Compare.Interface
import P256.Proofs.Program.Compare.Instructions.Common

namespace P256.Proofs.Program.Compare
open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Spec.Program P256.Spec.Program.Routines

theorem text_program_mem_of_offset (i : Nat) (hi : i < Extracted.textBytes.size) :
    ∃ byte, (Extracted.textAddress + BitVec.ofNat 64 i, byte) ∈ Extracted.programSections.toCodeMap := by
  have hi' : i < Extracted.textBytes.toList.length := by
    simpa only [chunked_toList_length] using hi
  refine ⟨Extracted.textBytes.toList[i]'hi', ?_⟩
  simp only [Extracted.programSections, ImageSections.toCodeMap,
    ImageSection.toCodeMap, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
  exact .inl (mem_codeRange _ _ _
    (by simpa only [chunked_toList_length] using hi))

namespace AdvancesTriple
theorem const_local {e : Effect}
    (hfull : ∀ w ∈ e.writes, w.Full) : Effect.Local (fun _ : RamState => e) := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => hfull⟩
  · intro t t' ho; rfl
  · intro t t' ho; rfl
  · intro t t' ho; rfl
  · intro t t' ho i hi
    simp only [Effect.flag]
    cases e.flags with
    | none => simp [hi]
    | some fe => simp

end AdvancesTriple
end P256.Proofs.Program.Compare
