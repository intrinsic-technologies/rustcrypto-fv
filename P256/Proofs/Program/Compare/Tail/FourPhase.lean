import P256.Proofs.Program.Compare.Tail.Support
import P256.Proofs.Program.Compare.Mismatch.Main

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

structure FourPhasePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cd70
  alias : (Operand.reg 8 : Operand 64).read s = (Operand.reg 6 : Operand 64).read s
  count : maskedLength s 4 = 0 ∨ maskedLength s 4 = 4
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) (maskedLength s 4).toNat
  right : MemReadable s ((Operand.reg 2 : Operand 64).read s) (maskedLength s 4).toNat

theorem four_phase [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : FourPhasePre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ AgreesExcept changes s t ∧
      ((PhaseSuccess s t (maskedLength s 4).toNat 0x11cdaf ∧
          (Operand.reg 0 : Operand 64).read t = (Operand.reg 6 : Operand 64).read t) ∨
        PhaseFailure s t (maskedLength s 4).toNat) := by
  obtain ⟨na, a, ha, hra, hca, hea, hspa⟩ := four_gate boundary s hr hc hp.rip hb
  have hba := hb.of_stack_eq hspa
  have hfa : AgreesExcept [.reg 0, .reg 9, .flags, .rip] s a := hea.agrees.mono
    (by simp [fourGateEffect, fourPrepareEffect, Effect.components,
      Write.component, Operand.component])
  rcases hp.count with hcount | hcount
  · refine ⟨na, a, ha, hra, hca, hfa.mono (by simp [changes]), Or.inl ⟨?_, ?_⟩⟩
    · refine ⟨?_, hfa.read (by decide), ?_, ?_, ?_⟩
      · simpa only [fourGateEffect, hcount, beq_self_eq_true, ite_true] using hea.rip
      · rw [hcount]
        exact (hfa.read (n := 64) (r := 6) (by decide)).trans (BitVec.add_zero _).symm
      · rw [hcount]
        exact (hfa.read (n := 64) (r := 2) (by decide)).trans (BitVec.add_zero _).symm
      · intro i hi
        rw [hcount] at hi
        change i < 0 at hi
        omega
    · rw [hfa.read (n := 64) (r := 6) (by decide)]
      have hwrite : (Operand.reg 0 : Operand 64).read a =
          (Operand.reg 6 : Operand 64).read s + maskedLength s 4 := hea.writes.2
      rw [hcount] at hwrite
      exact hwrite.trans (BitVec.add_zero _)
  · have hipa : a.RIP = 0x11cd80 := by
      have hh := hea.rip
      change a.RIP = (if maskedLength s 4 == 0 then _ else _) at hh
      rw [hcount] at hh
      exact hh
    obtain ⟨nb, b, hab, hrb, _, heb, hspb⟩ := four_start boundary a hra
      (program_text_slice hca 0x1cd80 16 (by decide +kernel)) hipa hba
    have hfb : AgreesExcept [.reg 10, .reg 11, .flags, .rip] a b := heb.agrees
    have hcb := hfb.codeIn (by simp [Component.Covers]) hca
    have hbb := hba.of_stack_eq hspb
    have hmem : b.external = s.external :=
      (hfa.trans hfb).external (by simp [Component.Covers])
    have hleft : fourLeft b = (Operand.reg 6 : Operand 64).read s := by
      simp only [fourLeft, show (Operand.reg 11 : Operand 64).read b = 0 from heb.writes.2,
        hfb.read (n := 64) (r := 8) (by decide), hfa.read (n := 64) (r := 8) (by decide), hp.alias]
      exact BitVec.add_zero _
    have hright : fourRight b = (Operand.reg 2 : Operand 64).read s := by
      simp only [fourRight, show (Operand.reg 11 : Operand 64).read b = 0 from heb.writes.2,
        hfb.read (n := 64) (r := 2) (by decide), hfa.read (n := 64) (r := 2) (by decide)]
      exact BitVec.add_zero _
    have hpb : FourComparePre b := by
      refine ⟨heb.rip, ?_, ?_⟩
      · rw [hleft]
        have hh := hp.left
        rw [hcount] at hh
        exact hh.of_external_eq hmem
      · rw [hright]
        have hh := hp.right
        rw [hcount] at hh
        exact hh.of_external_eq hmem
    obtain ⟨nc, c, hbc, hrc, hcc, hec, hspc⟩ := four_dispatch boundary b hrb hcb hpb hbb
    have hfc : AgreesExcept [.reg 6, .reg 7, .flags, .rip] b c := hec.agrees
    have hbc' := hbb.of_stack_eq hspc
    have heqv : (Operand.mem (fourLeft b) : Operand 32).read b =
        (Operand.mem (fourRight b) : Operand 32).read b ↔
      BytesEqual s ((Operand.reg 6 : Operand 64).read s)
        ((Operand.reg 2 : Operand 64).read s) 4 := by
      rw [← bytesEqual_iff_load]
      simp only [BytesEqual, hleft, hright, hmem]
    by_cases heq : (Operand.mem (fourLeft b) : Operand 32).read b =
        (Operand.mem (fourRight b) : Operand 32).read b
    · have hipc : c.RIP = 0x11cda0 := by
        simpa only [fourDispatchEffect, ite_eq_left heq] using hec.rip
      obtain ⟨nd, d, hcd, hrd, _, hed, hspd⟩ := four_advance boundary c hrc
        (program_text_slice hcc 0x1cda0 7 (by decide +kernel)) hipc hbc'
      have hfd : AgreesExcept [.reg 11, .flags, .rip] c d := hed.agrees
      have hccd := hfd.codeIn (by simp [Component.Covers]) hcc
      have hbd := hbc'.of_stack_eq hspd
      have hzero : (StatusFlags.ofRFLAGS d.RFLAGS).ZF = true := by
        have hz := hed.flags.2.2.2.1
        change (StatusFlags.ofRFLAGS d.RFLAGS).ZF =
          (((Operand.reg 9 : Operand 64).read c -
            ((Operand.reg 11 : Operand 64).read c + 4)) == 0) at hz
        rw [hfc.read (n := 64) (r := 9) (by decide),
          hfb.read (n := 64) (r := 9) (by decide), hea.writes.1,
          hfc.read (n := 64) (r := 11) (by decide), heb.writes.2] at hz
        change (StatusFlags.ofRFLAGS d.RFLAGS).ZF =
          ((maskedLength s 4 - (0 + 4)) == 0) at hz
        rw [hcount] at hz
        exact hz
      obtain ⟨ne, e, hde, hre, hce, hspe, hfe, hipe⟩ :=
        branch_zero boundary d 0x11cda7 0xe7 hrd hccd hbd hed.rip
          (program_text_slice hccd 0x1cda7 2 (by decide +kernel))
          (by unfold InRoutine; decide +kernel) (by unfold InRoutine; decide +kernel) hzero
      obtain ⟨nf, t, het, hrt, _, hef, _⟩ := four_finish boundary e hre
        (program_text_slice hce 0x1cda9 6 (by decide +kernel)) hipe (hbd.of_stack_eq hspe)
      have hff : AgreesExcept [.reg 2, .reg 6, .rip] e t := hef.agrees
      have hct := hff.codeIn (by simp [Component.Covers]) hce
      have hmid : AgreesExcept [.reg 6, .reg 7, .reg 11, .flags, .rip] b e :=
        ((hfc.trans hfd).trans hfe).mono (by simp)
      have hfull := (((hfa.trans hfb).trans hmid).trans hff)
      have hlen : (Operand.reg 1 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s :=
        hfull.read (by decide)
      have hl : (Operand.reg 6 : Operand 64).read t =
          (Operand.reg 6 : Operand 64).read s + 4 := by
        rw [hef.writes.2, hmid.read (n := 64) (r := 0) (by decide),
          hfb.read (n := 64) (r := 0) (by decide), hea.writes.2]
        change _ + maskedLength s 4 = _
        rw [hcount]
      have hright' : (Operand.reg 2 : Operand 64).read t =
          (Operand.reg 2 : Operand 64).read s + 4 := by
        rw [hef.writes.1, hmid.read (n := 64) (r := 10) (by decide), heb.writes.1,
          hfa.read (n := 64) (r := 2) (by decide), hea.writes.1]
        change _ + maskedLength s 4 = _
        rw [hcount]
      refine ⟨na + nb + nc + nd + ne + nf, t,
        ((((ha.trans hab).trans hbc).trans hcd).trans hde).trans het, hrt, hct,
        hfull.mono (by simp [changes]), Or.inl ⟨?_, ?_⟩⟩
      · refine ⟨hef.rip, hlen, ?_, ?_, ?_⟩
        · rw [hcount]
          exact hl
        · rw [hcount]
          exact hright'
        · rw [hcount]
          exact heqv.mp heq
      · rw [hff.read (n := 64) (r := 0) (by decide), hef.writes.2]
    · have hipc : c.RIP = 0x11ce4d := by
        simpa only [fourDispatchEffect, ite_eq_right heq] using hec.rip
      have hne : (Operand.reg 6 : Operand 32).read c ≠ (Operand.reg 7 : Operand 32).read c := by
        have hl := congrArg (BitVec.setWidth 32) hec.writes.1
        have hr := congrArg (BitVec.setWidth 32) hec.writes.2
        simp only [Mismatch.register_setWidth _ _ _ _ (by decide : 32 ≤ 64),
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] at hl hr
        rwa [hl, hr]
      obtain ⟨t, ht, hipt, hnet⟩ := Mismatch.four_mismatch boundary c hrc hcc hbc' hipc hne
      obtain ⟨nf, hct⟩ := ht.advances
      refine ⟨na + nb + nc + nf, t, ((ha.trans hab).trans hbc).trans hct,
        ht.ready, ht.code, ?_, Or.inr ⟨hipt, hnet, ?_⟩⟩
      · apply (((hfa.trans hfb).trans hfc).trans ht.frame).mono
        simp [changes, Mismatch.changes]
      · rw [hcount]
        exact fun h ↦ heq (heqv.mpr h)

end P256.Proofs.Program.Compare.Tail
