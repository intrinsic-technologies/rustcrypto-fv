import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Store
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Sub.Generated.RM.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine

private theorem subtract_remaining [Bindings] {entry s : RamState} {length : Nat}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f934) :
    ∃ t, RunningFrame entry boundary length t ∧ stackPtr t = base entry ∧ t.RIP = 0x10f941 ∧
      t.regValue .rcx = slot s 8 - slot s 264 ∧ AgreesExcept [.reg 1, .flags, .rip] s t := by
  obtain ⟨u, runU, readyU, load⟩ := (mov_r64_m64_effect_step 0x10f934 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances
    (supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) 0xf934 [0x48,0x8b,0x4c,0x24,8]
      (by decide) (by decide +kernel))
    ⟨pc, by change MemReadable s (stackPtr s + 8) 8; rw [sp]
            exact read_stack ctx running (off := 8) (by decide) (by decide)⟩
    (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf939 (by decide)))
  have frameU : AgreesExcept [.reg 1, .rip] s u := load.agrees
  have ru := no_memory ctx running runU readyU frameU (by simp [Component.Covers]) (by simp)
  have spU : stackPtr u = base entry := (frameU.read (n := 64) (r := 4) (by simp)).trans sp
  obtain ⟨t, runT, readyT, sub⟩ := (sub_r64_m64_effect_step 0x10f939 0x48
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl).advances readyU
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf939 [0x48,0x2b,0x8c,0x24,8,1,0,0]
      (by decide) (by decide +kernel))
    ⟨load.rip, by change MemReadable u (stackPtr u + 264) 8; rw [spU]
                  exact read_stack ctx ru (off := 264) (by decide) (by decide)⟩
    (boundary_ne_program ctx.outside (inProgram_of_textOffset 0xf941 (by decide)))
  have frameT : AgreesExcept [.reg 1, .flags, .rip] u t := sub.agrees
  have remaining : t.regValue .rcx = u.regValue .rcx - slot u 264 := sub.writes
  have value : u.regValue .rcx = slot s 8 := load.writes
  have same : slot u 264 = slot s 264 := by
    change memLoad u.external (stackPtr u + 264) 64 = memLoad s.external (stackPtr s + 264) 64
    rw [sp, spU, frameU.external (by simp [Component.Covers])]
  exact ⟨t, no_memory ctx ru runT readyT frameT (by simp [Component.Covers]) (by simp),
    (frameT.read (n := 64) (r := 4) (by simp)).trans spU, sub.rip,
    by rw [remaining, value, same], (frameU.trans frameT).mono (by simp)⟩

private def cloneBytes : List UInt8 := [0xba,0x90,0,0,0,0x4c,0x89,0xff,0x4c,0x89,0xf6]

private def cloneEffect (s : RamState) : Effect :=
  { rip := 0x10f958
    writes := [⟨(.reg 2 : Operand 64), 144⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r14⟩] }

private theorem clone_args [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f94d)
      (codeRange 0x10f94d cloneBytes) (Effect.post cloneEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10f94d 0xba (by decide) 144)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf952 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f952 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f94d cloneBytes 5 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf955 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f955 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f94d cloneBytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf958 (by decide))⟩
  advance_finish [cloneEffect]

theorem finish [Bindings] {entry s : RamState} {length : Nat} {b : UInt8}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f934) (al : (s.regValue .rax).setWidth 8 = b.toBitVec) :
    ∃ t, RunningFrame entry boundary length t ∧ stackPtr t = base entry ∧ t.RIP = 0x10f958 ∧
      t.regValue .rdx = 144 ∧ t.regValue .rdi = s.regValue .r15 ∧ t.regValue .rsi = s.regValue .r14 ∧
      slot t 8 = slot s 8 - slot s 264 ∧ t.external[base entry + 335]? = some b ∧
      AgreesExcept [.reg 1, .reg 2, .reg 7, .reg 6, .flags,
        .mem (base entry + 8) 8, .mem (base entry + 335) 1, .rip] s t := by
  obtain ⟨u, ru, spU, pcU, rem, frameU⟩ := subtract_remaining ctx running sp pc
  have writeU : MemWritable u (base entry + 8) 8 := by
    rw [show base entry + 8 = stackPtr entry - 528 from base_add (off := 8) (by decide)]
    exact stack_writable8 ctx.stack ctx.stackAvoid ru.allocated (by decide) (by decide)
  obtain ⟨v, rv, _, pcV, word, frameV⟩ := store_stack ctx ru
    (codeOff := 0xf941) (codeSize := 5) (off := 8) (width := 64) pcU
    (show stackPtr u + 8 = _ by rw [spU]; rfl) (by decide) (by decide) writeU
    (mov_m64_r64_effect_step 0x10f941 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf941 [0x48,0x89,0x4c,0x24,8]
      (by decide) (by decide +kernel))
  have spV : stackPtr v = base entry := (frameV.read (n := 64) (r := 4) (by simp)).trans spU
  obtain ⟨w, rw', readyW, pcW, byteWrite, frameW⟩ := store_stack ctx rv
    (codeOff := 0xf946) (codeSize := 7) (off := 335) (width := 8) pcV
    (show stackPtr v + 335 = _ by rw [spV]; rfl) (by decide) (by decide)
    (write_byte ctx rv (by decide))
    (mov_m8_r8_effect_step 0x10f946 0 (by decide) (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl)
    (programText_slice (programLoaded_codeIn rv.loaded) 0xf946 [0x88,0x84,0x24,0x4f,1,0,0]
      (by decide) (by decide +kernel))
  have spW : stackPtr w = base entry := (frameW.read (n := 64) (r := 4) (by simp)).trans spV
  have alV : (v.regValue .rax).setWidth 8 = b.toBitVec :=
    (congrArg (BitVec.setWidth 8) ((frameU.trans frameV).read (n := 64) (r := 0) (by simp))).trans al
  have byte := byte_of_load (read_stack ctx rw' (off := 335) (by decide) (by decide))
    (byteWrite.trans alV)
  obtain ⟨fuel, t, runT, readyT, _, effect⟩ := clone_args boundary ctx.outside w readyW
    (programText_slice (programLoaded_codeIn rw'.loaded) 0xf94d cloneBytes (by decide) (by decide +kernel))
    pcW
  have frameT : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] w t := effect.agrees
  have spT : stackPtr t = base entry := (frameT.read (n := 64) (r := 4) (by simp)).trans spW
  have extT := frameT.external (by simp [Component.Covers])
  have beforeArgs := (frameU.trans frameV).trans frameW
  have values := effect.writes
  change t.regValue .rdx = 144 ∧ t.regValue .rdi = w.regValue .r15 ∧
    t.regValue .rsi = w.regValue .r14 at values
  refine ⟨t, no_memory ctx rw' runT readyT frameT (by simp [Component.Covers]) (by simp), spT,
    effect.rip, values.1, values.2.1.trans (beforeArgs.read (n := 64) (r := 15) (by simp)),
    values.2.2.trans (beforeArgs.read (n := 64) (r := 14) (by simp)), ?_, by rwa [extT],
    (beforeArgs.trans frameT).mono (by simp)⟩
  change memLoad t.external (stackPtr t + 8#64) 64 = _
  rw [spT, extT, word_unchanged frameW (by
    rw [show base entry + 335#64 - (base entry + 8#64) = 327 by bv_omega]
    unfold OffsetsApart
    decide +kernel) (by decide)]
  exact word.trans rem

end Hkdf.Proofs.NewExpand.Expand.Counter
