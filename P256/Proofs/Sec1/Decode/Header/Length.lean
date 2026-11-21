import P256.Proofs.Sec1.Decode.Header.Tag
import P256.Proofs.Common.Encoding.Parser.LengthCheck.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Header

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Encoding.Parser.LengthCheck

def expectedLength (tag : BitVec 8) : BitVec 64 :=
  if tag = 0 then 1 else if tag = 4 then 65 else 33

private theorem table_bytes (tag : BitVec 8) (valid : validTag tag = true) :
    ∀ i : Fin 8, Extracted.programSections.fetchByte
      ((tag.setWidth 64 <<< 3) + 0x202b40 + BitVec.ofNat 64 i.val) =
        some (storedByte (expectedLength tag) i.val) := by
  simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with (((h | h) | h) | h) | h
  all_goals subst tag; decide +kernel

private theorem table_readable {s : RamState} (loaded : ProgramLoaded s)
    (tag : BitVec 8) (valid : validTag tag = true) :
    MemReadable s ((tag.setWidth 64 <<< 3) + 0x202b40) 8 := by
  constructor
  · simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
    rcases valid with (((h | h) | h) | h) | h
    all_goals subst tag; decide +kernel
  · intro i hi
    rw [loaded _ _ (table_bytes tag valid ⟨i, hi⟩)]
    rfl

private theorem table_value {s : RamState} (loaded : ProgramLoaded s)
    (tag : BitVec 8) (valid : validTag tag = true) :
    memLoad s.external ((tag.setWidth 64 <<< 3) + 0x202b40) 64 = expectedLength tag := by
  apply Bytes.memLoad (n := 64) (v := expectedLength tag) ?_ (by decide) (by decide)
  intro i hi
  exact loaded _ _ (table_bytes tag valid ⟨i, hi⟩)

theorem length_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e514)
    (tag : BitVec 8) (valid : validTag tag = true) (rcx : s.regValue .rcx = tag.setWidth 64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .rdx = expectedLength tag then 0x10e522 else 0x10e68e) ∧
      AgreesExcept [.flags, .rip] s t := by
  have address : (AddrMode.abs (some 1) 3 0x202b40).addr s 0x10e51c =
      (tag.setWidth 64 <<< 3) + 0x202b40 := by
    change (s.regValue .rcx <<< 3) + 0x202b40 = _
    rw [rcx]
  obtain ⟨u, au, ru, eu⟩ :=
    (cmp_r64_m64_effect_step 0x10e514 0x48 (by simp [RexWPrefix]) 2
      (.abs (some 1) 3 0x202b40) (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe514 _ (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable s ((AddrMode.abs (some 1) 3 0x202b40).addr s 0x10e51c) 8
        rw [address]; exact table_readable loaded tag valid⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe51c (by decide)))
  have gu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := gu.external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rdx == expectedLength tag) := by
    have h := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (cmpSpec (s.regValue .rdx) (memLoad s.external
        ((AddrMode.abs (some 1) 3 0x202b40).addr s 0x10e51c) 64)).ZF at h
    rw [address, table_value loaded tag valid] at h
    simpa only [cmpSpec_ZF] using h
  have target : (jccEffect 0x10e51c 6 5 ((0x16c : BitVec 32).signExtend 64) u).rip =
      if s.regValue .rdx = expectedLength tag then 0x10e522 else 0x10e68e := by
    simp [jccEffect, branchEffect, branchTarget, condHolds, zf]
  obtain ⟨t, runT, rt, et⟩ := (jcc_rel32_effect_step 0x10e51c 5 0x16c).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0xe51c _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [target]; split
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe522 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe68e (by decide)))
  exact ⟨t, au.trans runT, rt, et.rip.trans target,
    (gu.trans et.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.Sec1.Decode.Header
