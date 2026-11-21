import P256.Proofs.Sec1.Decode.Header.Length
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1.Decode.Header (expectedLength)

theorem length_table_bytes (tag : BitVec 8) (valid : tag = 0 ∨ tag = 4) :
    ∀ i : Fin 8, Extracted.programSections.fetchByte
      ((tag.setWidth 64 <<< 3) + 0x202460 + BitVec.ofNat 64 i.val) =
        some (storedByte (expectedLength tag) i.val) := by
  rcases valid with rfl | rfl <;> decide +kernel

theorem length_table_readable {s : RamState} (loaded : ProgramLoaded s)
    (tag : BitVec 8) (valid : tag = 0 ∨ tag = 4) :
    MemReadable s ((tag.setWidth 64 <<< 3) + 0x202460) 8 := by
  constructor
  · rcases valid with rfl | rfl <;> decide +kernel
  · intro i hi
    rw [loaded _ _ (length_table_bytes tag valid ⟨i, hi⟩)]
    rfl

theorem length_table_value {s : RamState} (loaded : ProgramLoaded s)
    (tag : BitVec 8) (valid : tag = 0 ∨ tag = 4) :
    memLoad s.external ((tag.setWidth 64 <<< 3) + 0x202460) 64 = expectedLength tag := by
  apply Bytes.memLoad (n := 64) (v := expectedLength tag) ?_ (by decide) (by decide)
  intro i hi
  exact loaded _ _ (length_table_bytes tag valid ⟨i, hi⟩)

theorem length_lookup [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1018af)
    (tag : BitVec 8) (valid : tag = 0 ∨ tag = 4) (rcx : s.regValue .rcx = tag.setWidth 64) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ t.RIP = 0x1018b7 ∧
      t.regValue .r15 = expectedLength tag ∧ AgreesExcept [.reg 15, .rip] s t := by
  have address : (AddrMode.abs (some 1) 3 0x202460).addr s 0x1018b7 =
      (tag.setWidth 64 <<< 3) + 0x202460 := by
    change (s.regValue .rcx <<< 3) + 0x202460 = _
    rw [rcx]
  obtain ⟨t, run, final, effect⟩ := (mov_r64_m64_effect_step 0x1018af 0x4c
    (by simp [RexWPrefix]) 7 (.abs (some 1) 3 0x202460) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x18af _ (by decide) (by decide +kernel))
    ⟨rip, by
      change MemReadable s ((AddrMode.abs (some 1) 3 0x202460).addr s 0x1018b7) 8
      rw [address]
      exact length_table_readable loaded tag valid⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x18b7 (by decide)))
  refine ⟨t, run, final, effect.rip, ?_, effect.agrees⟩
  have value : t.regValue .r15 = memLoad s.external
      ((AddrMode.abs (some 1) 3 0x202460).addr s 0x1018b7) 64 := effect.writes
  rwa [address, length_table_value loaded tag valid] at value

end P256.Proofs.Sec1.Wrapper.Success.Tail
