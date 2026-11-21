import ChaCha20Poly1305.Proofs.MemoryRoutines.Memset.Arithmetic
import ChaCha20Poly1305.Proofs.MemoryRoutines.Memset.Register

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
open ChaCha20Poly1305.Proofs.MemoryRoutines.Memset.Register

def patternBytes : List UInt8 :=
  [0x49, 0x89, 0xd0, 0x48, 0x89, 0xfa, 0x40, 0x0f, 0xb6, 0xce, 0x48, 0xb8,
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x48, 0x0f, 0xaf, 0xc1]

def patternEffect (s : RamState) : Effect :=
  { rip := 0x102d88
    writes := [⟨r8, rdx.read s⟩, ⟨rdx, rdi.read s⟩,
      ⟨rcx, ((rsi.read s).setWidth 8).setWidth 64⟩,
      ⟨rax, broadcast ((rsi.read s).setWidth 8)⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem pattern_prepare [Bindings] (boundary : ReturnBoundary) (hb : Outside boundary) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x102d70)
      (codeRange 0x102d70 patternBytes) patternEffect := by
  unfold patternBytes
  routine_run_begin mov_r64_r64_effect_step 0x102d70 0x49 0xd0
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact hb.ne (p := 0x102d73) (by decide) (by decide)
  routine_run_then mov_r64_r64_effect_step 0x102d73 0x48 0xfa
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x102d70) (all := patternBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102d76) (by decide) (by decide)
  routine_run_then movzx_ecx_sil_effect_step 0x102d76
  case sub => exact codeRange_mem_of_drop (p := 0x102d70) (all := patternBytes) 6 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102d7a) (by decide) (by decide)
  routine_run_then mov_r64_imm64_effect_step 0x102d7a 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0x0101010101010101
  case sub => exact codeRange_mem_of_drop (p := 0x102d70) (all := patternBytes) 10 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102d84) (by decide) (by decide)
  routine_run_then imul_rax_rcx_effect_step 0x102d84
  case sub => exact codeRange_mem_of_drop (p := 0x102d70) (all := patternBytes) 20 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102d88) (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [patternEffect]
  · x86_norm [patternEffect, broadcast, rdx, r8]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [patternEffect]
  · x86_norm [patternEffect, rdx, r8]

end ChaCha20Poly1305.Proofs.MemoryRoutines.Memset
