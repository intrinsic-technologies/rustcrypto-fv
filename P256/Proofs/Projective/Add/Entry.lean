import P256.Proofs.Projective.Add.Prologue
import P256.Proofs.Projective.Preserve
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Add

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

def entryBytes : List UInt8 := [0x49,0x89,0xf6,0x48,0x89,0xfb]

def entryEffect (s : RamState) : Effect :=
  { rip := 0x105207
    writes := [⟨(.reg 14 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 3 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩] }

theorem entry_moves [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105201) (codeRange 0x105201 entryBytes)
      (Effect.post entryEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x105201 0x49 0xf6 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x5204 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105204 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x105201 entryBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x5207 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [entryEffect]
  · x86_norm [entryEffect]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [entryEffect]
  · x86_norm [entryEffect]

structure EntryState [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop extends
    FrameState s t 96 920 632 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x105207
  left : t.regValue .rbx = s.regValue .rdi
  right : t.regValue .r14 = s.regValue .rsi
  memory : t.external = saveMemory s
  agrees : AgreesExcept (saveFrame s ++ [.flags, .reg 14, .reg 3]) s t

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) : ∃ t, EntryState s t boundary := by
  obtain ⟨u, runU, stateU, ripU, memoryU, agreesU⟩ := frame_entry pre
  obtain ⟨n, t, runT, readyT, _, effectT⟩ := entry_moves boundary pre.outerBoundary u
    (readyToStep stateU.machine stateU.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateU.loaded) 0x5201 entryBytes
      (by decide +kernel) (by decide +kernel)) ripU
  have stateT := stateU.after_registers readyT effectT.agrees
    (by simp [entryEffect, Effect.components, Component.Covers])
    (by simp [entryEffect, Effect.components])
  refine ⟨t, ⟨stateT, ⟨7+n, runU.trans runT⟩, effectT.rip, ?_, ?_, ?_, ?_⟩⟩
  · exact effectT.writes.2.trans (agreesU.read (n := 64) (r := 7) (by simp [saveFrame]))
  · exact effectT.writes.1.trans (agreesU.read (n := 64) (r := 6) (by simp [saveFrame]))
  · exact (effectT.agrees.external (by simp [entryEffect, Effect.components, Component.Covers])).trans
      memoryU
  · apply (agreesU.trans effectT.agrees).mono
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with h | h
    · simp only [List.mem_singleton] at h
      rcases h with h | rfl
      · exact List.mem_append.mpr (.inl h)
      · simp
    · simp only [entryEffect, Effect.components, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (rfl | rfl) | rfl <;> simp [saveFrame]

theorem EntryState.preserves_points [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : EntryState s t boundary) (leftAt : ProjectiveAt s (s.regValue .rdi) left)
    (rightAt : ProjectiveAt s (s.regValue .rsi) right) :
    ProjectiveAt t (s.regValue .rdi) left ∧ ProjectiveAt t (s.regValue .rsi) right := by
  have frame := save_frame pre (by decide) state.agrees
    (by simp [Component.Covers])
  constructor
  · apply leftAt.of_frame frame pre.outputBounded
    intro region member
    have same : region = Stack.region s 920 := by simpa using member
    subst region
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
  · apply rightAt.of_frame frame pre.inputBounded
    intro region member
    have same : region = Stack.region s 920 := by simpa using member
    subst region
    exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)

end P256.Proofs.Projective.Add
