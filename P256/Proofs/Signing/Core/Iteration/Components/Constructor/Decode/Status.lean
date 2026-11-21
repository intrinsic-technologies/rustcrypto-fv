import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Frame
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CompareMemory
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmpM32Imm8Effect_ZF cmp_m32_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem status [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (second : Bool) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = if second then 0x10994b else 0x1098c2)
    (read : MemReadable s (stackPtr s) 4) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if memLoad s.external (stackPtr s) 32 = 1 then 0x109a0d
        else if second then 0x109955 else 0x1098cc) ∧
      AgreesExcept [.flags, .rip] s t := by
  let offset : Nat := if second then 0x994b else 0x98c2
  let p : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 offset
  let disp : BitVec 32 := if second then 0xb8 else 0x141
  have hrip : s.RIP = p := by cases second <;> exact rip
  have code := programLoaded_codeIn loaded
  have instruction : CodeIn (codeRange p [0x83,0x3c,0x24,1]) s :=
    programText_slice code offset _ (by cases second <;> decide) (by cases second <;> decide +kernel)
  obtain ⟨u, run, readyU, effect⟩ :=
    (cmp_m32_imm8_effect_step p (.sib 4 none 0 .none)
      (by decide +kernel) rfl rfl 1).advances ready instruction ⟨hrip, by
      x86_norm
      change MemReadable s (stackPtr s + (0 : BitVec 64)) 4
      exact (BitVec.add_zero (stackPtr s)).symm ▸ read⟩ (by
        cases second
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x98c6 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x994f (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := effect.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) code
  have branch : CodeIn (codeRange (p + 4) (0x0f :: jccOpcode32 4 :: immBytes 32 disp)) u := by
    have h := programText_slice codeU (offset + 4) (0x0f :: jccOpcode32 4 :: immBytes 32 disp)
      (by cases second <;> decide) (by cases second <;> decide +kernel)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, p] using h
  have zf := cmpM32Imm8Effect_ZF (p := p) (len := 4)
    (am := .sib 4 none 0 .none) (imm := 1) effect
  have address (ip : BitVec 64) : (AddrMode.sib 4 none 0 .none).addr s ip = stackPtr s := by
    x86_norm
    simp only [BitVec.add_zero]
  rw [address] at zf
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    decide (memLoad s.external (stackPtr s) 32 = 1) at zf
  obtain ⟨t, step, readyT, effectT⟩ := jcc_rel32_effect_step (p + 4) 4 disp u readyU branch
    ⟨effect.rip, fun _ => by cases second <;> decide⟩
  have ip : t.RIP =
      (if memLoad s.external (stackPtr s) 32 = 1 then 0x109a0d
        else if second then 0x109955 else 0x1098cc) := by
    rw [effectT.rip]
    simp only [jccEffect, branchEffect, condHolds, zf]
    cases second <;> simp [p, offset, disp, branchTarget, Extracted.textAddress]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [ip]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9a0d (by decide))
    · cases second
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x98cc (by decide))
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9955 (by decide))
  refine ⟨t, run.trans advance, readyT, ip, ?_⟩
  exact (frame.trans effectT.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
