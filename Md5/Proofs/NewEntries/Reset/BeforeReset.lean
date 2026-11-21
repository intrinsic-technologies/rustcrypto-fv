import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs.Block

structure BeforeResetPre (s : RamState) : Prop where
  rip : s.RIP = 0x1014c7
  total : MemReadable s (stackPtr s + 8) 8

def beforeResetBytes : List UInt8 :=
  [0x48, 0x8b, 0x74, 0x24, 8,
   0x48, 0xba, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
   0x48, 0xbf, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]

def beforeResetEffect (s : RamState) : Effect where
  rip := 0x1014e0
  writes := [⟨(.reg 6 : Operand 64), (.mem (stackPtr s + 8) : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), 0x1032547698badcfe⟩,
    ⟨(.reg 7 : Operand 64), 0xefcdab8967452301⟩]

theorem before_reset [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary BeforeResetPre (codeRange 0x1014c7 beforeResetBytes)
      beforeResetEffect := by
  unfold beforeResetBytes
  md5_run_begin (mov_r64_m64_effect_step 0x1014c7 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide))
  case pre => intro s h; exact ⟨h.rip, h.total⟩
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14cc (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x1014cc 0x48 0xba
    (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x1014c7) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14d6 (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x1014d6 0x48 0xbf
    (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x1014c7) 15 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14e0 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [beforeResetEffect]
  · x86_norm [beforeResetEffect]
  · intro i; cases i <;> x86_norm [beforeResetEffect]
  · x86_norm [beforeResetEffect]

end Md5.Proofs.NewEntries.Reset
