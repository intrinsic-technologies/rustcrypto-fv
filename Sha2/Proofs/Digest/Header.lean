import Sha2.Proofs.Common.SHA256.Blocks.Digest.Prepare
import Sha2.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Blocks.Digest

theorem header512_code (routine : Routine)
    (member : routine ∈ [sha384Digest, sha512Digest, sha512_224Digest, sha512_256Digest])
    {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (routine.entryAddress + 17) Header.bytes) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact programText_slice (programLoaded_codeIn loaded) 0x3891 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x94a1 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x57e1 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x7641 _
      (by decide +kernel) (by decide +kernel)

theorem header512_inside (routine : Routine)
    (member : routine ∈ [sha384Digest, sha512Digest, sha512_224Digest, sha512_256Digest]) :
    BlockInProgram (routine.entryAddress + 17) Header.bytes.length := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact blockInProgram_of_textOffset 0x3891 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x94a1 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x57e1 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x7641 _ (by decide +kernel)

end Sha2.Proofs.Digest
