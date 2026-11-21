import Sha1.Proofs.MemoryRoutines.Memset.Arithmetic
import Sha1.Proofs.MemoryRoutines.Memset.Register

namespace Sha1.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Compress.Machine
open Sha1.Proofs.MemoryRoutines.Memset.Register

def patternBytes : List UInt8 :=
  [0x49, 0x89, 0xd0, 0x48, 0x89, 0xfa, 0x40, 0x0f, 0xb6, 0xce, 0x48, 0xb8,
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x48, 0x0f, 0xaf, 0xc1]

def patternEffect (s : RamState) : Effect :=
  { rip := 0x1036f8
    writes := [⟨r8, rdx.read s⟩, ⟨rdx, rdi.read s⟩,
      ⟨rcx, ((rsi.read s).setWidth 8).setWidth 64⟩,
      ⟨rax, broadcast ((rsi.read s).setWidth 8)⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem pattern_prepare [Bindings] (boundary : ReturnBoundary) (hb : Outside boundary) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1036e0)
      (codeRange 0x1036e0 patternBytes) patternEffect := by
  unfold patternBytes
  md5_run_begin mov_r64_r64_effect_step 0x1036e0 0x49 0xd0
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact hb.ne (p := 0x1036e3) (by decide) (by decide)
  md5_run_then mov_r64_r64_effect_step 0x1036e3 0x48 0xfa
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1036e0) (all := patternBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x1036e6) (by decide) (by decide)
  md5_run_then movzx_ecx_sil_effect_step 0x1036e6
  case sub => exact codeRange_mem_of_drop (p := 0x1036e0) (all := patternBytes) 6 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x1036ea) (by decide) (by decide)
  md5_run_then mov_r64_imm64_effect_step 0x1036ea 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0x0101010101010101
  case sub => exact codeRange_mem_of_drop (p := 0x1036e0) (all := patternBytes) 10 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x1036f4) (by decide) (by decide)
  md5_run_then imul_rax_rcx_effect_step 0x1036f4
  case sub => exact codeRange_mem_of_drop (p := 0x1036e0) (all := patternBytes) 20 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x1036f8) (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [patternEffect]
  · x86_norm [patternEffect, broadcast, rdx, r8]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [patternEffect]
  · x86_norm [patternEffect, rdx, r8]

end Sha1.Proofs.MemoryRoutines.Memset
