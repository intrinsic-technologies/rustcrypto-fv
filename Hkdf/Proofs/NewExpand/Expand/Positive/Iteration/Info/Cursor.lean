import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RM.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Hkdf.Proofs.NewExpand.Expand.Info

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine

def cursorBytes : List UInt8 := [0x49, 0x83, 0xc5, 0x10, 0x4c, 0x3b, 0xac, 0x24, 0xb8, 1, 0, 0]

private theorem advanceCursor [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    {s : RamState} (ready : ReadyToStep s) (code : CodeIn (codeRange p cursorBytes) s)
    (pc : s.RIP = p) (readable : MemReadable s (rspOf s + 440) 8)
    (nextAdd : p + 4 ≠ boundary.rip) (nextCmp : p + 4 + 8 ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = (p + 12#64) ∧
      (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s + 16 ∧
      (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        ((Operand.reg 13 : Operand 64).read s + 16 ==
          (Operand.mem (rspOf s + 440) : Operand 64).read s) ∧
      AgreesExcept [.reg 13, .flags, .rip] s t ∧ t.external = s.external := by
  obtain ⟨s1, st1, r1, e1⟩ := add_r64_imm8_effect_step p 0x49 0xc5 16
    (by simp [RexWPrefix]) (by decide) (by decide) s ready
    (code.mono (by simpa only [BitVec.add_zero] using
      (codeRange_mem_of_drop (p := p) (all := cursorBytes)
        (bytes := 0x49 :: 0x83 :: 0xc5 :: immBytes 8 16) 0 (by decide +kernel)))) pc
  change (addR64Imm8Effect p 13 16 s).Holds s s1 at e1
  have ag1 : AgreesExcept [.reg 13, .flags, .rip] s s1 := e1.agrees
  have sp1 : rspOf s1 = rspOf s := ag1.read (by simp)
  have mem1 : s1.external = s.external := ag1.external (by simp [Component.Covers])
  have val1 : (Operand.reg 13 : Operand 64).read s1 =
      (Operand.reg 13 : Operand 64).read s + 16 := e1.writes
  have read1 : MemReadable s1 (rspOf s1 + 440) 8 := by
    rw [sp1]
    exact ⟨readable.low, fun i hi => ag1.grow _ (readable.mem i hi)⟩
  obtain ⟨t, st2, rt, e2⟩ := cmp_r64_m64_effect_step (p + 4) 0x4c
    (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 440)) (by decide) rfl rfl s1 r1
    ((code.of_external_eq mem1).mono
      (codeRange_mem_of_drop (p := p) 4 (by decide +kernel)))
    ⟨e1.rip, by simpa only [x86_compose] using read1⟩
  change (cmpR64M64Effect (p + 4) 13 (.sib 4 none 0 (.d32 440)) s1).Holds s1 t at e2
  have ag2 : AgreesExcept [.flags, .rip] s1 t := e2.agrees
  have zf := e2.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
    (((Operand.reg 13 : Operand 64).read s1 -
      (Operand.mem (rspOf s1 + 440) : Operand 64).read s1) == 0) at zf
  rw [val1, sp1] at zf
  have ag : AgreesExcept [.reg 13, .flags, .rip] s t := (ag1.trans ag2).mono (by simp)
  refine ⟨t, (Advances.of_step st1 (.inl (e1.rip ▸ nextAdd))).trans
    (Advances.of_step st2 (.inl (e2.rip ▸ nextCmp))), rt,
    ?_, (ag2.read (by simp)).trans val1, ?_, ag, ag.external (by simp [Component.Covers])⟩
  · have h : t.RIP = (p + 4 + 8 : BitVec 64) := e2.rip
    rw [BitVec.add_assoc] at h
    exact h
  · have mr : (Operand.mem (rspOf s + 440) : Operand 64).read s1 =
        (Operand.mem (rspOf s + 440) : Operand 64).read s := by
      change memLoad s1.external _ 64 = memLoad s.external _ 64
      rw [mem1]
    rw [mr] at zf
    have same : ∀ a b : BitVec 64, (a - b == 0) = (a == b) := by
      intro a b
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
      change a = (0#64) + b ↔ a = b
      rw [BitVec.zero_add]
    simpa only [same] using zf

theorem finishShort [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pc : s.RIP = 0x10f70f)
    (readable : MemReadable s (rspOf s + 440) 8) (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = (if (Operand.reg 13 : Operand 64).read s + 16 =
          (Operand.mem (rspOf s + 440) : Operand 64).read s then 0x10f8a0 else 0x10f721) ∧
      (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s + 16 ∧
      AgreesExcept [.reg 13, .flags, .rip] s t ∧ t.external = s.external := by
  have code : CodeIn (codeRange 0x10f70f cursorBytes) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf70f _ (by decide) (by decide +kernel)
  obtain ⟨u, adv, ru, pcu, value, zf, ag, mem⟩ := advanceCursor boundary 0x10f70f ready code pc readable
    (boundary_ne_program outer (inProgram_of_textOffset 0xf713 (by decide))) (boundary_ne_program outer (inProgram_of_textOffset 0xf71b (by decide)))
  have branch : CodeIn (codeRange 0x10f71b [0x0f, 0x84, 0x7f, 1, 0, 0]) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf71b _ (by decide) (by decide +kernel)
  obtain ⟨t, st, rt, e⟩ := jcc_rel32_effect_step 0x10f71b 4 0x17f u ru
    (branch.of_external_eq mem) ⟨pcu, by intro; decide⟩
  have ae : AgreesExcept [.rip] u t := e.agrees
  have all : AgreesExcept [.reg 13, .flags, .rip] s t := (ag.trans ae).mono (by simp)
  have target : t.RIP = if (Operand.reg 13 : Operand 64).read s + 16 =
      (Operand.mem (rspOf s + 440) : Operand 64).read s then 0x10f8a0 else 0x10f721 := by
    simpa [jccEffect, branchEffect, condHolds, branchTarget, zf] using e.rip
  exact ⟨t, adv.trans (Advances.of_step st (.inl (by
    rw [target]
    split
    · exact boundary_ne_program outer (inProgram_of_textOffset 0xf8a0 (by decide))
    · exact boundary_ne_program outer (inProgram_of_textOffset 0xf721 (by decide))))), rt, target,
    (ae.read (by simp)).trans value, all, all.external (by simp [Component.Covers])⟩

theorem finishCompressed [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pc : s.RIP = 0x10f7de)
    (readable : MemReadable s (rspOf s + 440) 8) (outer : ¬ InProgram boundary.rip) :
    ∃ n t, Advances boundary n s t ∧ ReadyToStep t ∧
      n = (if (Operand.reg 13 : Operand 64).read s + 16 =
          (Operand.mem (rspOf s + 440) : Operand 64).read s then 4 else 3) ∧
      t.RIP = (if (Operand.reg 13 : Operand 64).read s + 16 =
          (Operand.mem (rspOf s + 440) : Operand 64).read s then 0x10f8a0 else 0x10f721) ∧
      (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s + 16 ∧
      AgreesExcept [.reg 13, .flags, .rip] s t ∧ t.external = s.external := by
  have code : CodeIn (codeRange 0x10f7de cursorBytes) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf7de _ (by decide) (by decide +kernel)
  obtain ⟨u, adv, ru, pcu, value, zf, ag, mem⟩ := advanceCursor boundary 0x10f7de ready code pc readable
    (boundary_ne_program outer (inProgram_of_textOffset 0xf7e2 (by decide))) (boundary_ne_program outer (inProgram_of_textOffset 0xf7ea (by decide)))
  have branch : CodeIn (codeRange 0x10f7ea [0x0f, 0x85, 0x31, 0xff, 0xff, 0xff]) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf7ea _ (by decide) (by decide +kernel)
  obtain ⟨v, st, rv, e⟩ := jcc_rel32_effect_step 0x10f7ea 5 0xffffff31 u ru
    (branch.of_external_eq mem) ⟨pcu, by intro; decide⟩
  have ae : AgreesExcept [.rip] u v := e.agrees
  have all : AgreesExcept [.reg 13, .flags, .rip] s v := (ag.trans ae).mono (by simp)
  have pcv : v.RIP = if (Operand.reg 13 : Operand 64).read s + 16 =
      (Operand.mem (rspOf s + 440) : Operand 64).read s then 0x10f7f0 else 0x10f721 := by
    simpa [jccEffect, branchEffect, condHolds, branchTarget, zf] using e.rip
  have advv := adv.trans (Advances.of_step st (.inl (by
    rw [pcv]
    split
    · exact boundary_ne_program outer (inProgram_of_textOffset 0xf7f0 (by decide))
    · exact boundary_ne_program outer (inProgram_of_textOffset 0xf721 (by decide)))))
  by_cases eq : (Operand.reg 13 : Operand 64).read s + 16 =
      (Operand.mem (rspOf s + 440) : Operand 64).read s
  · have jump : CodeIn (codeRange 0x10f7f0 [0xe9, 0xab, 0, 0, 0]) s :=
      programText_slice (programLoaded_codeIn loaded) 0xf7f0 _ (by decide) (by decide +kernel)
    obtain ⟨t, stt, rt, et⟩ := jmp_rel32_effect_step 0x10f7f0 0xab (by decide) v rv
      (jump.of_external_eq (all.external (by simp [Component.Covers])))
      (by simpa only [ite_eq_left eq] using pcv)
    have agt : AgreesExcept [.rip] v t := et.agrees
    have alt : AgreesExcept [.reg 13, .flags, .rip] s t := (all.trans agt).mono (by simp)
    exact ⟨4, t, advv.trans (Advances.of_step stt (.inl (by rw [et.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf8a0 (by decide))))),
      rt, by simp only [ite_eq_left eq], by simpa only [ite_eq_left eq] using (show t.RIP = 0x10f8a0 from et.rip),
      (agt.read (by simp)).trans ((ae.read (by simp)).trans value), alt, alt.external (by simp [Component.Covers])⟩
  · exact ⟨3, v, advv, rv, by simp only [ite_eq_right eq],
      by simpa only [ite_eq_right eq] using pcv, (ae.read (by simp)).trans value,
      all, all.external (by simp [Component.Covers])⟩

end Hkdf.Proofs.NewExpand.Expand.Info
