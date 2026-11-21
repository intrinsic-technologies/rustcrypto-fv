import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Tail

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem lookup_length [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x106e55)
    (tag : s.regValue .rcx = 4) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ t.RIP = 0x106e5d ∧
      t.regValue .r15 = 65 ∧ AgreesExcept [.reg 15,.rip] s t := by
  have data : ∀ i : Fin 8, Extracted.programSections.fetchByte (0x2026a0+BitVec.ofNat 64 i.val) =
      some (storedByte (65 : BitVec 64) i.val) := by decide +kernel
  have bytes : Bytes s.external 0x2026a0 8 (storedByte (65 : BitVec 64)) :=
    fun i hi => loaded _ _ (data ⟨i,hi⟩)
  have addr : (AddrMode.abs (some 1) 3 0x202680).addr s 0x106e5d = 0x2026a0 := by
    change (s.regValue .rcx <<< 3)+0x202680 = _
    rw [tag]
    rfl
  obtain ⟨t,run,rt,effect⟩ := (mov_r64_m64_effect_step 0x106e55 0x4c
    (by simp [RexWPrefix]) 15 (.abs (some 1) 3 0x202680)
    (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6e55 _ (by decide) (by decide +kernel))
    ⟨rip,by change MemReadable s ((AddrMode.abs (some 1) 3 0x202680).addr s 0x106e5d) 8
            rw [addr]; exact bytes.readable (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6e5d (by decide)))
  refine ⟨t,run,rt,effect.rip,?_,effect.agrees⟩
  have h : t.regValue .r15 = memLoad s.external
      ((AddrMode.abs (some 1) 3 0x202680).addr s 0x106e5d) 64 := effect.writes
  rw [h,addr]
  exact bytes.memLoad (by decide) (by decide)

end P256.Proofs.Generate.Wrapper.Tail
