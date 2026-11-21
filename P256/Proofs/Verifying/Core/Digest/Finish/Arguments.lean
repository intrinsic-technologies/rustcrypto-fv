import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Verifying.Core.Prepare.Pointers
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

def argumentBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0xc8,0x03,0,0,0x48,0x8d,0xb4,0x24,0x80,0,0,0]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x10dc73
    writes := [⟨(.reg 7 : Operand 64),rspOf s+968⟩,
      ⟨(.reg 6 : Operand 64),rspOf s+128⟩] }

theorem argument_block [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10dc63)
      (codeRange 0x10dc63 argumentBytes) (Effect.post argumentEffect) := by
  advance_begin (lea_r64_effect_step 0x10dc63 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 968)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0xdc6b (by decide))
  advance_then (lea_r64_effect_step 0x10dc6b 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dc63 argumentBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdc73 (by decide))
  advance_finish [argumentEffect]

theorem arguments [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dc63) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (argumentEffect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := argument_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdc63 argumentBytes
      (by decide) (by decide +kernel)) rip
  refine ⟨n,u,run,state.after_effect pre.toCalleePre (by decide) ready effect.agrees ?_
    (by simp [argumentEffect,Effect.components]),effect⟩
  intro c hc a ha
  simp only [argumentEffect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,List.cons_append,List.nil_append,List.mem_cons,
    List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl <;> exact ha.elim

end P256.Proofs.Verifying.Core.Digest.Finish
