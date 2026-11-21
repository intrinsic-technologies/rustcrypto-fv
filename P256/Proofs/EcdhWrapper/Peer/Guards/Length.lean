import P256.Proofs.Sec1.Decode.Header.Length
import P256.Proofs.Common.Encoding.Parser.LengthCheck.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Encoding.Parser.LengthCheck

open P256.Proofs.Sec1.Decode.Header

private theorem table_bytes (tag : BitVec 8) (valid : validTag tag = true) :
    ∀ i : Fin 8, Extracted.programSections.fetchByte
      ((tag.setWidth 64 <<< 3) + 0x202680 + BitVec.ofNat 64 i.val) =
        some (storedByte (expectedLength tag) i.val) := by
  simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with (((h | h) | h) | h) | h
  all_goals subst tag; decide +kernel

private theorem table_readable {s : RamState} (loaded : ProgramLoaded s)
    (tag : BitVec 8) (valid : validTag tag = true) :
    MemReadable s ((tag.setWidth 64 <<< 3) + 0x202680) 8 := by
  constructor
  · simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
    rcases valid with (((h | h) | h) | h) | h
    all_goals subst tag; decide +kernel
  · intro i hi
    rw [loaded _ _ (table_bytes tag valid ⟨i, hi⟩)]
    rfl

private theorem table_value {s : RamState} (loaded : ProgramLoaded s)
    (tag : BitVec 8) (valid : validTag tag = true) :
    memLoad s.external ((tag.setWidth 64 <<< 3) + 0x202680) 64 = expectedLength tag := by
  apply Bytes.memLoad (n := 64) (v := expectedLength tag) ?_ (by decide) (by decide)
  intro i hi
  exact loaded _ _ (table_bytes tag valid ⟨i, hi⟩)

theorem length_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1069f6)
    (tag : BitVec 8) (valid : validTag tag = true) (rcx : s.regValue .rcx = tag.setWidth 64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .rbp = expectedLength tag then 0x106a04 else 0x106cee) ∧
      AgreesExcept [.flags, .rip] s t := by
  have address : (AddrMode.abs (some 1) 3 0x202680).addr s 0x1069fe =
      (tag.setWidth 64 <<< 3) + 0x202680 := by
    change (s.regValue .rcx <<< 3) + 0x202680 = _
    rw [rcx]
  obtain ⟨u, au, ru, eu⟩ :=
    (cmp_r64_m64_effect_step 0x1069f6 0x48 (by simp [RexWPrefix]) 5
      (.abs (some 1) 3 0x202680) (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x69f6 _ (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable s ((AddrMode.abs (some 1) 3 0x202680).addr s 0x1069fe) 8
        rw [address]; exact table_readable loaded tag valid⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x69fe (by decide)))
  have gu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := gu.external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rbp == expectedLength tag) := by
    have h := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (cmpSpec (s.regValue .rbp) (memLoad s.external
        ((AddrMode.abs (some 1) 3 0x202680).addr s 0x1069fe) 64)).ZF at h
    rw [address, table_value loaded tag valid] at h
    simpa only [cmpSpec_ZF] using h
  have target : (jccEffect 0x1069fe 6 5 ((0x2ea : BitVec 32).signExtend 64) u).rip =
      if s.regValue .rbp = expectedLength tag then 0x106a04 else 0x106cee := by
    simp [jccEffect, branchEffect, branchTarget, condHolds, zf]
  obtain ⟨t, runT, rt, et⟩ := (jcc_rel32_effect_step 0x1069fe 5 0x2ea).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x69fe _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [target]; split
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x6a04 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x6cee (by decide)))
  exact ⟨t, au.trans runT, rt, et.rip.trans target,
    (gu.trans et.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.EcdhWrapper.Peer.Guards
