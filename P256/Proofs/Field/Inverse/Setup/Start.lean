import P256.Proofs.Field.Inverse.Setup.Entry
import P256.Proofs.Program.PushSequenceFrame
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem inverse_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11409c ∧ stackPtr t = stackPtr s - 168 ∧
      t.regValue .rbx = s.regValue .rdi ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.external = entryMemory s ∧
      AgreesExcept (entryComponents s ++ [.reg 3, .rip]) s t ∧
      MemoryWriteFrame s t #v[Stack.region s 880] := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ := inverse_entry_steps pre
  obtain ⟨t, runT, readyT, effect⟩ :=
    (mov_r64_r64_effect_step 0x114099 0x48 0xfb (by simp [RexWPrefix]) rfl).advances readyU
      (programText_slice (programLoaded_codeIn loadedU) 0x14099 [0x48, 0x89, 0xfb]
        (by decide) (by decide +kernel)) ripU
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1409c (by decide)))
  have agT : AgreesExcept [.reg 3, .rip] u t := effect.agrees
  have ag := agreesU.trans agT
  have memoryT : t.external = u.external := agT.external (by simp [Component.Covers])
  refine ⟨t, runU.trans runT, readyT, ?_, effect.rip, ?_, ?_, ?_,
    memoryT.trans memoryU, ag, ?_⟩
  · intro a b hb
    rw [memoryT]
    exact loadedU a b hb
  · exact (agT.read (n := 64) (r := 4) (by simp)).trans rspU
  · exact effect.writes.trans (agreesU.read (n := 64) (r := 7)
      (by simp [entryComponents, pushSequenceFrame]))
  · exact ag.read (n := 64) (r := 6) (by simp [entryComponents, pushSequenceFrame])
  · apply pushSequence_frame pre.stack (sources := saveSources) (offset := 0) (by decide)
      (cs := [.reg 4, .flags, .rip] ++ [.reg 3, .rip])
    · simpa only [entryComponents, List.append_assoc] using ag
    · intro c hc a
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) | (rfl | rfl) <;> exact id

end P256.Proofs.Field.Inverse
