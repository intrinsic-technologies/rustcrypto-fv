import P256.Proofs.Program.Code
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10d700)
    (last : (Operand.reg 13 : Operand 64).read s + 16 = (Operand.reg 12 : Operand 64).read s)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x10d71d ∧
      (Operand.reg 13 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s ∧
      AgreesExcept [.reg 13, .flags, .rip] s t := by
  have next (offset : Nat) (bound : offset < 118431) :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  obtain ⟨s₁, a₁, r₁, e₁⟩ :=
    (add_r64_imm8_effect_step 0x10d700 0x49 0xc5 16 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0xd700
        [0x49,0x83,0xc5,0x10] (by decide) (by decide +kernel)) rip (next 0xd704 (by decide))
  have f₁ : AgreesExcept [.reg 13, .flags, .rip] s s₁ := e₁.agrees
  have c₁ := f₁.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded)
  obtain ⟨s₂, a₂, r₂, e₂⟩ :=
    (cmp_r64_r64_effect_step 0x10d704 0x4d 0xe5 (by simp [RexWPrefix]) rfl).advances
      r₁ (programText_slice c₁ 0xd704 [0x4d,0x39,0xe5] (by decide) (by decide +kernel))
      e₁.rip (next 0xd707 (by decide))
  have f₂ : AgreesExcept [.flags, .rip] s₁ s₂ := e₂.agrees
  have same : (Operand.reg 13 : Operand 64).read s₁ = (Operand.reg 12 : Operand 64).read s₁ := by
    have write := e₁.writes
    change (Operand.reg 13 : Operand 64).read s₁ = (Operand.reg 13 : Operand 64).read s + 16 at write
    rw [write, last, f₁.read (r := 12) (by simp)]
  have zf : (StatusFlags.ofRFLAGS s₂.RFLAGS).ZF = true := by
    have h := e₂.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s₂.RFLAGS).ZF =
      (((Operand.reg 13 : Operand 64).read s₁ - (Operand.reg 12 : Operand 64).read s₁) == 0) at h
    rw [same, BitVec.sub_self] at h
    exact h
  have c₂ := f₂.codeIn (by simp [Component.Covers]) c₁
  obtain ⟨s₃, a₃, r₃, e₃⟩ := jcc_rel32_effect_step 0x10d707 5 0xffffff32 s₂ r₂
    (programText_slice c₂ 0xd707 [0x0f,0x85,0x32,0xff,0xff,0xff] (by decide) (by decide +kernel))
    ⟨e₂.rip, fun _ => by decide⟩
  have pc₃ : s₃.RIP = 0x10d70d := by
    rw [e₃.rip]
    change (if !(StatusFlags.ofRFLAGS s₂.RFLAGS).ZF then (0x10d63f : BitVec 64) else 0x10d70d) = _
    rw [zf]
    rfl
  have run₃ : Advances boundary 1 s₂ s₃ :=
    Advances.of_step a₃ (.inl (by rw [pc₃]; exact next 0xd70d (by decide)))
  have f₃ : AgreesExcept [.rip] s₂ s₃ := e₃.agrees
  have c₃ := f₃.codeIn (by simp [Component.Covers]) c₂
  obtain ⟨t, a₄, r₄, e₄⟩ := (jmp_rel8_effect_step 0x10d70d 14 (by decide)).advances
    r₃ (programText_slice c₃ 0xd70d [0xeb,0x0e] (by decide) (by decide +kernel))
    pc₃ (next 0xd71d (by decide))
  have f₄ : AgreesExcept [.rip] s₃ t := e₄.agrees
  refine ⟨t, ((a₁.trans a₂).trans run₃).trans a₄, r₄, e₄.rip, ?_,
    (((f₁.trans f₂).trans f₃).trans f₄).mono (by simp)⟩
  rw [f₄.read (by simp), f₃.read (by simp), f₂.read (by simp), same,
    f₁.read (by simp)]

end P256.Proofs.Verifying.Message.Hash.Long.Tail.Finish
