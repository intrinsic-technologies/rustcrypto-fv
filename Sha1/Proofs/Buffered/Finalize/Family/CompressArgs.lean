import Sha1.Proofs.Buffered.Finalize.Steps

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

def argumentBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x08, 0x48, 0x8d, 0xb4, 0x24, 0x80, 0, 0, 0, 0xba, 1, 0, 0, 0]

def argumentEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 18
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 128⟩, ⟨(.reg 2 : Operand 64), 1⟩] }

set_option maxRecDepth 1024 in
theorem compression_args [Bindings] {boundary : ReturnBoundary} {s : RamState} {p : BitVec 64}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hp : p = 0x101e9d ∨ p = 0x101f69) (hip : s.RIP = p) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (argumentEffect p s).Holds s t := by
  have outside (n : Nat) (hn : n ≤ 18) : p + BitVec.ofNat 64 n ≠ boundary.rip := by
    obtain ⟨off, haddr, hbound⟩ : ∃ off : Nat,
        p = Extracted.textAddress + BitVec.ofNat 64 off ∧ off + 18 < Extracted.textBytes.size := by
      rcases hp with rfl | rfl
      · exact ⟨0x1e9d, by decide +kernel, by decide +kernel⟩
      · exact ⟨0x1f69, by decide +kernel, by decide +kernel⟩
    rw [haddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact text_address_ne_return hout (off + n) (by omega)
  have block : AdvancesBlock boundary (fun u ↦ u.RIP = p) (codeRange p argumentBytes)
      (argumentEffect p) := by
    unfold argumentBytes
    md5_run_begin lea_r64_effect_step p 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact outside 5 (by decide)
    md5_run_then lea_r64_effect_step (p + 5) 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d32 128)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; change p + 5 + 8 ≠ _; rw [BitVec.add_assoc]; exact outside 13 (by decide)
    md5_run_then mov_r32_imm32_effect_step (p + 13) 0xba (by decide) 1
    case boundary => intro _ _; change p + 13 + 5 ≠ _; rw [BitVec.add_assoc]; exact outside 18 (by decide)
    apply AdvancesBlock.block_end
    intro u t _ he
    apply he.weaken
    · x86_norm [argumentEffect, BitVec.add_assoc]
    · x86_norm [argumentEffect, stackPtr]
      exact ⟨rfl, rfl⟩
    · intro i; cases i <;> x86_norm [argumentEffect]
    · x86_norm [argumentEffect, stackPtr]
  have hbytes : CodeIn (codeRange p argumentBytes) s := by
    rcases hp with rfl | rfl
    · exact program_text_slice hc 0x1e9d 18 (by decide +kernel)
    · exact program_text_slice hc 0x1f69 18 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := block s hr hbytes hip
  exact ⟨n, t, ha, ht, he.codeIn (Effect.Avoids.of_noMem (by
    simp [argumentEffect, Effect.components, Component.Covers]) _) hc, he⟩

end Sha1.Proofs.Buffered.Finalize.Family
