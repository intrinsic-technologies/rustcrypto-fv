import P256.Proofs.Program.LimbSelect.Prologue.Prepare
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary} {select : Bool}
    (hp : Pre s boundary)
    (hs : (s.regValue .r8).setWidth 8 = if select then 1 else 0) :
    ∃ t, (∃ fuel, Advances boundary fuel s t) ∧ LoopState s t select 0 ∧
      t.RIP = 0x1191f0 := by
  obtain ⟨t, ht, hrt, fst, hit, spt, axt, cxt⟩ := prepare hp hs
  have code := programLoaded_codeIn (loaded_of_agrees hp (by decide) fst)
  have sit : t.regValue .rsi = 4 :=
    (fst.read (r := 6) (n := 64) (by simp [components, registers])).trans hp.leftCount
  obtain ⟨a, ha, hra, ea⟩ :=
    (cmp_r64_r64_effect_step 0x1191dd 0x48 0xce (by simp [RexWPrefix])
      (by decide +kernel)).advances hrt
      (programText_slice code 0x191dd [0x48,0x39,0xce] (by decide +kernel) rfl) hit
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191e0 (by decide +kernel)))
  change (cmpR64R64Effect 0x1191dd 6 1 t).Holds t a at ea
  have fa : AgreesExcept [.flags, .rip] t a := ea.agrees
  have extA : a.external = t.external := fa.external (by simp [Component.Covers])
  have zfA : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = true := by
    have hz := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (t.regValue .rsi - t.regValue .rcx == 0) at hz
    rw [hz, sit, cxt]
    rfl
  have ripB : (jccEffect 0x1191e0 2 5 ((0x2d : BitVec 8).signExtend 64) a).rip = 0x1191e2 := by
    change (if !(StatusFlags.ofRFLAGS a.RFLAGS).ZF then (0x11920f : BitVec 64) else 0x1191e2) = _
    rw [zfA]
    rfl
  obtain ⟨b, hb, hrb, eb⟩ := (jcc_rel8_effect_step 0x1191e0 5 0x2d).advances hra
    (programText_slice (code.of_external_eq extA) 0x191e0 [0x75,0x2d] (by decide +kernel) rfl)
    ⟨ea.rip, by intro _; decide +kernel⟩
    (by rw [ripB]; exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191e2 (by decide +kernel)))
  have fb : AgreesExcept [.rip] a b := eb.agrees
  have fab : AgreesExcept [.flags,.rip] t b := (fa.trans fb).mono (by simp)
  have extB : b.external = t.external := fab.external (by simp [Component.Covers])
  have siB : b.regValue .rsi = 4 := (fab.read (r := 6) (n := 64) (by simp)).trans sit
  obtain ⟨c, hcc, hrc, ec⟩ :=
    (test_r64_r64_effect_step 0x1191e2 0x48 0xf6 (by simp [RexWPrefix])
      (by decide +kernel)).advances hrb
      (programText_slice (code.of_external_eq extB) 0x191e2 [0x48,0x85,0xf6]
        (by decide +kernel) rfl) (eb.rip.trans ripB)
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191e5 (by decide +kernel)))
  change (testR64R64Effect 0x1191e2 6 6 b).Holds b c at ec
  have fc : AgreesExcept [.flags,.rip] b c := ec.agrees
  have ftc : AgreesExcept [.flags,.rip] t c := (fab.trans fc).mono (by simp)
  have extC : c.external = t.external := ftc.external (by simp [Component.Covers])
  have zfC : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = false := by
    have hz := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((b.regValue .rsi &&& b.regValue .rsi) == 0) at hz
    rw [hz, siB]
    rfl
  have ripD : (jccEffect 0x1191e5 2 4 ((0x23 : BitVec 8).signExtend 64) c).rip = 0x1191e7 := by
    change (if (StatusFlags.ofRFLAGS c.RFLAGS).ZF then (0x11920a : BitVec 64) else 0x1191e7) = _
    rw [zfC]
    rfl
  obtain ⟨d, hd, hrd, ed⟩ := (jcc_rel8_effect_step 0x1191e5 4 0x23).advances hrc
    (programText_slice (code.of_external_eq extC) 0x191e5 [0x74,0x23] (by decide +kernel) rfl)
    ⟨ec.rip, by intro _; decide +kernel⟩
    (by rw [ripD]; exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191e7 (by decide +kernel)))
  have fd : AgreesExcept [.rip] c d := ed.agrees
  have ftd : AgreesExcept [.flags,.rip] t d := (ftc.trans fd).mono (by simp)
  have extD : d.external = t.external := ftd.external (by simp [Component.Covers])
  obtain ⟨e, he, hre, ee⟩ := (xor_r32_r32_effect_step 0x1191e7 0xc9 (by decide +kernel)).advances hrd
    (programText_slice (code.of_external_eq extD) 0x191e7 [0x31,0xc9] (by decide +kernel) rfl)
    (ed.rip.trans ripD)
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191e9 (by decide +kernel)))
  change (xorR32R32Effect 0x1191e7 2 1 1 d).Holds d e at ee
  have fe : AgreesExcept [.reg 1,.flags,.rip] d e := ee.agrees
  have fte : AgreesExcept [.reg 1,.flags,.rip] t e := (ftd.trans fe).mono (by simp)
  have extE : e.external = t.external := fte.external (by simp [Component.Covers])
  have cxE : e.regValue .rcx = 0 := by
    have hw : e.regValue .rcx =
      (((Operand.reg 1 : Operand 32).read d) ^^^ ((Operand.reg 1 : Operand 32).read d)).setWidth 64 := ee.writes
    rw [hw, BitVec.xor_self]
    rfl
  obtain ⟨f, hf, hrf, ef⟩ :=
    (nop_m_effect_step 0x1191e9 [] (by simp) (by decide) (.base 0 (.d32 0))
      (by simp [AddrMode.Valid, regLow]) (by decide +kernel) (by decide +kernel)).advances hre
      (programText_slice (code.of_external_eq extE) 0x191e9 [0x0f,0x1f,0x80,0,0,0,0]
        (by decide +kernel) rfl) ee.rip
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191f0 (by decide +kernel)))
  have ff : AgreesExcept [.rip] e f := ef.agrees
  have ftf : AgreesExcept [.reg 1,.flags,.rip] t f := (fte.trans ff).mono (by simp)
  refine ⟨f, ⟨12, (((((ht.trans ha).trans hb).trans hcc).trans hd).trans he).trans hf⟩,
    ⟨hrf, (fst.trans ftf).mono (by simp [components, registers]), ?_, ?_, ?_, ?_⟩, ef.rip⟩
  · exact (ftf.read (r := 4) (n := 64) (by simp)).trans spt
  · exact (ftf.read (r := 0) (n := 64) (by simp)).trans axt
  · exact (ff.read (r := 1) (n := 64) (by simp)).trans cxE
  · intro i hi
    omega

end P256.Proofs.Program.LimbSelect
