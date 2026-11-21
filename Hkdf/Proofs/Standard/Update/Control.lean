import Hkdf.Proofs.Standard.Memory
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem dispatch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x101601)
    (readable : MemReadable s (stackPtr s + 8) 8) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if memLoad s.external (stackPtr s + 8) 64 = 0 then 0x101724 else 0x10160d) ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, first, readyU, compared⟩ :=
    (cmp_m64_imm8_effect_step 0x101601 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0).advances ready
      (programText_slice code 0x1601 _ (by decide) (by decide +kernel))
      ⟨rip, by change MemReadable s (stackPtr s + 8) 8; exact readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x1607 (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := compared.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) code
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (memLoad s.external (stackPtr s + 8) 64 == 0) := by
    have h := compared.flag .ZF
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (cmpSpec (memLoad s.external
        (AddrMode.addr (.sib 4 none 0 (.d8 8)) s (0x101601 + 6)) 64) 0).ZF at h
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (cmpSpec (memLoad s.external (stackPtr s + 8) 64) 0).ZF at h
    simpa only [cmpSpec_ZF] using h
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step 0x101607 4 0x117 u readyU
    (programText_slice codeU 0x1607 _ (by decide) (by decide +kernel))
    ⟨compared.rip, fun _ ↦ by decide⟩
  have target : t.RIP =
      (if memLoad s.external (stackPtr s + 8) 64 = 0 then 0x101724 else 0x10160d) := by
    rw [jumped.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x101724 else 0x10160d) = _
    rw [zf]
    simp only [beq_iff_eq]
  have second : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1724 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x160d (by decide))
  refine ⟨t, first.trans second, readyT, target, ?_⟩
  exact (frame.trans jumped.agrees).mono (by simp [jccEffect, branchEffect_components])

theorem enter_loop [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10160d) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x101649 ∧
      t.regValue .r14 = 0 ∧ t.regValue .r12 = 0x10dd60 ∧
      AgreesExcept [.reg 14, .reg 12, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, first, readyU, zeroed⟩ :=
    (xor_r32_r32_rex_effect_step 0x10160d 0x45 0xf6
      (by simp [RexNoWPrefix]) rfl).advances ready
      (programText_slice code 0x160d _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1610 (by decide)))
  have frame1 : AgreesExcept [.reg 14, .flags, .rip] s u := zeroed.agrees
  have value : u.regValue .r14 = 0 := by
    have h := zeroed.writes
    change u.regValue .r14 =
      ((Operand.reg 14 : Operand 32).read s ^^^ (Operand.reg 14 : Operand 32).read s).setWidth 64 at h
    rw [BitVec.xor_self] at h
    exact h
  have codeU := frame1.codeIn (by simp [Component.Covers]) code
  obtain ⟨v, second, readyV, addressed⟩ :=
    (lea_r64_effect_step 0x101610 0x4c (by simp [RexWPrefix]) 4
      (.rip 0xc749) (by decide +kernel) rfl rfl).advances readyU
      (programText_slice codeU 0x1610 _ (by decide) (by decide +kernel)) zeroed.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1617 (by decide)))
  have frame2 : AgreesExcept [.reg 12, .rip] u v := addressed.agrees
  have copy : v.regValue .r12 = 0x10dd60 := addressed.writes
  have codeV := frame2.codeIn (by simp [Component.Covers]) codeU
  obtain ⟨t, third, readyT, jumped⟩ :=
    (jmp_rel8_effect_step 0x101617 0x30 (by decide)).advances readyV
      (programText_slice codeV 0x1617 _ (by decide) (by decide +kernel)) addressed.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1649 (by decide)))
  have frame3 : AgreesExcept [.rip] v t := jumped.agrees
  refine ⟨t, first.trans (second.trans third), readyT, jumped.rip, ?_, ?_, ?_⟩
  · exact ((frame2.trans frame3).read (n := 64) (r := 14) (by simp)).trans value
  · exact (frame3.read (n := 64) (r := 12) (by simp)).trans copy
  · exact ((frame1.trans frame2).trans frame3).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl) | (rfl | rfl)) | rfl <;> simp)

end Hkdf.Proofs.Standard.Update
