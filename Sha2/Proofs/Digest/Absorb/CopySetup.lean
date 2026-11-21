import Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
import Sha2.Proofs.Wrapper512.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb.CopySetup

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512

def bytes (tail : Bool) : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0xd0,0,0,0] ++
    (if tail then [0x4c,0x89,0xfe] else []) ++ [0x4c,0x89,0xf2]

def effect (p : BitVec 64) (tail : Bool) (s : RamState) : Effect :=
  { rip := p + (if tail then 14 else 11)
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 208⟩] ++
      (if tail then [⟨(.reg 6 : Operand 64), s.regValue .r15⟩] else []) ++
      [⟨(.reg 2 : Operand 64), s.regValue .r14⟩] }

theorem code (v : Variant) (tail : Bool) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (if tail then 0x12f else 0xd0) .digest) (bytes tail)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset .digest + if tail then 0x12f else 0xd0)
  · cases tail <;> cases v <;> decide +kernel
  · cases tail <;> cases v <;> decide +kernel

theorem run [Bindings] (p : BitVec 64) (tail : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes tail).length) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (bytes tail))
      (Effect.post (effect p tail)) := by
  cases tail with
  | false =>
    advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 208)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 8 (by decide)))
    advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program outside (inside 11 (by decide)))
    advance_finish [effect]
  | true =>
    advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 208)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 8 (by decide)))
    advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xfe (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program outside (inside 11 (by decide)))
    advance_reloc_then (mov_r64_r64_effect_step (p + 11) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program outside (inside 14 (by decide)))
    advance_finish [effect]

end Sha2.Proofs.Digest.Absorb.CopySetup
