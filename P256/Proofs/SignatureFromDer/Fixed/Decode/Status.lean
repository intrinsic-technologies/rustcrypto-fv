import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
import P256.Proofs.Common.Instructions.CompareMemory
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmpM32Imm8Effect_ZF cmp_m32_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem status [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (second : Bool) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = if second then 0x109b7f else 0x109b11)
    (read : MemReadable s (stackPtr s + 8) 4) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if memLoad s.external (stackPtr s + 8) 32 = 1 then 0x109c57
        else if second then 0x109b8a else 0x109b1c) ∧
      AgreesExcept [.flags, .rip] s t := by
  let offset : Nat := if second then 0x9b7f else 0x9b11
  let p : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 offset
  let disp : BitVec 32 := if second then 0xcd else 0x13b
  have hrip : s.RIP = p := by cases second <;> exact rip
  have code := programLoaded_codeIn loaded
  have instruction : CodeIn (codeRange p [0x83,0x7c,0x24,8,1]) s :=
    programText_slice code offset _ (by cases second <;> decide) (by cases second <;> decide +kernel)
  obtain ⟨u, run, readyU, effect⟩ :=
    (cmp_m32_imm8_effect_step p (.sib 4 none 0 (.d8 8))
      (by simp [AddrMode.Valid]) rfl rfl 1).advances ready instruction ⟨hrip, read⟩ (by
        cases second
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x9b16 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x9b84 (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := effect.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) code
  have branch : CodeIn (codeRange (p + 5) (0xf :: jccOpcode32 4 :: immBytes 32 disp)) u := by
    have h := programText_slice codeU (offset + 5) (0xf :: jccOpcode32 4 :: immBytes 32 disp)
      (by cases second <;> decide) (by cases second <;> decide +kernel)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, p] using h
  have zf := cmpM32Imm8Effect_ZF (p := p) (len := 5)
    (am := .sib 4 none 0 (.d8 8)) (imm := 1) effect
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    decide (memLoad s.external (stackPtr s + 8) 32 = 1) at zf
  obtain ⟨t, step, readyT, effectT⟩ := jcc_rel32_effect_step (p + 5) 4 disp u readyU branch
    ⟨effect.rip, fun _ => by cases second <;> decide⟩
  have ip : t.RIP =
      (if memLoad s.external (stackPtr s + 8) 32 = 1 then 0x109c57
        else if second then 0x109b8a else 0x109b1c) := by
    rw [effectT.rip]
    simp only [jccEffect, branchEffect, condHolds, zf]
    cases second <;> simp [p, offset, disp, branchTarget, Extracted.textAddress]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [ip]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9c57 (by decide))
    · cases second
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9b1c (by decide))
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9b8a (by decide))
  refine ⟨t, run.trans advance, readyT, ip, ?_⟩
  exact (frame.trans effectT.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])

end P256.Proofs.SignatureFromDer.Fixed.Decode
