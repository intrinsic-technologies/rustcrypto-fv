import P256.Proofs.Nonce.Update.Absorb.Seeded.ShortTail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.CrossTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Encoding.Parser.LengthCheck

attribute [local x86_compose] cmpR64M64Effect
attribute [local x86_local] ShortTail.cmp_local

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a37d
  readable : MemReadable s (rspOf s + 80) 8

def bytes : List UInt8 := [0x49, 0x83, 0xc6, 0x10, 0x4c, 0x3b, 0x74, 0x24, 0x50]

def effect (s : RamState) : Effect :=
  { rip := 0x10a386
    writes := [⟨(.reg 14 : Operand 64),(Operand.reg 14 : Operand 64).read s + 16⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 14 : Operand 64).read s + 16)
      (memLoad s.external (rspOf s + 80) 64))) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a37d bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa37d bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a37d bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (addR64Imm8Effect 0x10a37d 14 16) from
    add_r64_imm8_effect_step 0x10a37d 0x49 0xc6 16 (by simp [RexWPrefix]) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa381 (by decide))
  advance_then (show StepEffect _ _ (cmpR64M64Effect 0x10a381 5 14 (fun s => rspOf s + 80)) from
    cmp_r64_m64_effect_step 0x10a381 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a37d bytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers,cmpR64M64Effect,Effect.components]) _, ?_⟩
    · x86_norm; exact hP.readable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa386 (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Absorb.Seeded.CrossTail
