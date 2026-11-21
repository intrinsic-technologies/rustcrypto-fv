import Sha2.Proofs.Common.Machine.Prologue
import Sha2.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem prologue256_code (routine : Routine) (layout : Prologue.Layout)
    (member : (routine, layout) ∈
      [(sha224Reset, .six200), (sha256Reset, .six200), (sha224FinalizeIntoReset, .six312), (sha256FinalizeIntoReset, .six312), (sha224TraitFinalizeIntoReset, .six312), (sha256TraitFinalizeIntoReset, .six312)])
    {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange routine.entryAddress (Prologue.bytes layout)) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact programText_slice (programLoaded_codeIn loaded) 0xd30 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x2960 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x650 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x2260 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x14d0 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x3120 _
      (by decide +kernel) (by decide +kernel)

theorem prologue256_inside (routine : Routine) (layout : Prologue.Layout)
    (member : (routine, layout) ∈
      [(sha224Reset, .six200), (sha256Reset, .six200), (sha224FinalizeIntoReset, .six312), (sha256FinalizeIntoReset, .six312), (sha224TraitFinalizeIntoReset, .six312), (sha256TraitFinalizeIntoReset, .six312)]) :
    BlockInProgram routine.entryAddress (Prologue.bytes layout).length := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blockInProgram_of_textOffset 0xd30 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x2960 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x650 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x2260 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x14d0 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x3120 _ (by decide +kernel)

theorem prologue512_code (routine : Routine) (layout : Prologue.Layout)
    (member : (routine, layout) ∈
      [
      (sha384Reset, .six376),
      (sha384FinalizeIntoReset, .six584),
      (sha384TraitFinalizeIntoReset, .six600),
      (sha512Reset, .six376),
      (sha512FinalizeIntoReset, .six584),
      (sha512TraitFinalizeIntoReset, .six600),
      (sha512_224Reset, .six376),
      (sha512_224FinalizeIntoReset, .six584),
      (sha512_224TraitFinalizeIntoReset, .six600),
      (sha512_256Reset, .six376),
      (sha512_256FinalizeIntoReset, .six584),
      (sha512_256TraitFinalizeIntoReset, .six600)])
    {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange routine.entryAddress (Prologue.bytes layout)) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact programText_slice (programLoaded_codeIn loaded) 0x46f0 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x3f70 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x4fc0 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xa380 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x9bc0 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xac90 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x65c0 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x5e80 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x6e60 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x8420 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x7ce0 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x8cc0 _
      (by decide +kernel) (by decide +kernel)

theorem prologue512_inside (routine : Routine) (layout : Prologue.Layout)
    (member : (routine, layout) ∈
      [
      (sha384Reset, .six376),
      (sha384FinalizeIntoReset, .six584),
      (sha384TraitFinalizeIntoReset, .six600),
      (sha512Reset, .six376),
      (sha512FinalizeIntoReset, .six584),
      (sha512TraitFinalizeIntoReset, .six600),
      (sha512_224Reset, .six376),
      (sha512_224FinalizeIntoReset, .six584),
      (sha512_224TraitFinalizeIntoReset, .six600),
      (sha512_256Reset, .six376),
      (sha512_256FinalizeIntoReset, .six584),
      (sha512_256TraitFinalizeIntoReset, .six600)]) :
    BlockInProgram routine.entryAddress (Prologue.bytes layout).length := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blockInProgram_of_textOffset 0x46f0 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x3f70 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x4fc0 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0xa380 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x9bc0 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0xac90 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x65c0 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x5e80 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x6e60 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x8420 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x7ce0 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x8cc0 _ (by decide +kernel)

end Sha2.Proofs.Reset
