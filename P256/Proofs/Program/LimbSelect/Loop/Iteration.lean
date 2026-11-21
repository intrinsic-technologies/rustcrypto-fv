import P256.Proofs.Program.LimbSelect.Data
import P256.Proofs.Common.Field.Operations.Select.TestAl
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import P256.Proofs.Common.Instructions.CrossPageStore.Mov
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovne_r9_r8_effect_step)
open P256.Proofs.Common.Field (test_al_al_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem indexed_address {t : RamState} {base : BitVec 4} {addr : BitVec 64} {count : Nat}
    (hb : AddrMode.reg64 base t = addr) (hc : t.regValue .rcx = BitVec.ofNat 64 count)
    (hn : count < 4) (next : BitVec 64) :
    (AddrMode.sib base (some 1) 3 .none).addr t next = addr + BitVec.ofNat 64 (8*count) := by
  simp only [AddrMode.addr, hb, Disp.value]
  change addr + (t.regValue .rcx <<< 3) + (0 : BitVec 64) = _
  rw [hc]
  have hcases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp

theorem iteration [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    {count : Nat} (hp : Pre s boundary) (h : LoopState s t select count)
    (hc : count < 4) (hrip : t.RIP = 0x1191f0) :
    ∃ u, Advances boundary 8 t u ∧ LoopState s u select (count+1) ∧
      u.RIP = if count+1 = 4 then 0x11920a else 0x1191f0 := by
  have code := programLoaded_codeIn (h.loaded hp (by omega))
  have haddrT : (AddrMode.sib 2 (some 1) 3 .none).addr t (0x1191f0+4) =
      s.regValue .rdx + BitVec.ofNat 64 (8*count) :=
    indexed_address (base := 2) (t := t) h.rdx h.rcx hc _
  obtain ⟨a, ha, hra, ea⟩ :=
    (mov_r64_m64_effect_step 0x1191f0 0x4c (by simp [RexWPrefix])
      0 (.sib 2 (some 1) 3 .none) (by simp [AddrMode.Valid, regLow]) (by decide +kernel)
      (by decide +kernel)).advances h.ready
      (programText_slice code 0x191f0 [0x4c,0x8b,0x04,0xca] (by decide +kernel) rfl)
      ⟨hrip, haddrT ▸ source_readable hp h.agrees (by omega)⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191f4 (by decide +kernel)))
  change (movR64M64Effect 0x1191f0 8 (.sib 2 (some 1) 3 .none) t).Holds t a at ea
  have fa : AgreesExcept [.reg 8, .rip] t a := ea.agrees
  have extA : a.external = t.external := fa.external (by simp [Component.Covers])
  have cxA : a.regValue .rcx = BitVec.ofNat 64 count :=
    (fa.read (r := 1) (n := 64) (by simp)).trans h.rcx
  have diA : a.regValue .rdi = s.regValue .rdi :=
    (fa.read (r := 7) (n := 64) (by simp)).trans h.rdi
  have haddrA : (AddrMode.sib 7 (some 1) 3 .none).addr a (0x1191f4+4) =
      s.regValue .rdi + BitVec.ofNat 64 (8*count) := indexed_address (base := 7) (t := a) diA cxA hc _
  have r8A : a.regValue .r8 =
      (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read s := by
    have hw : a.regValue .r8 =
      (Operand.mem ((AddrMode.sib 2 (some 1) 3 .none).addr t (0x1191f0+4)) : Operand 64).read t := ea.writes
    rw [hw, haddrT, source_word hp hc h.agrees]
  obtain ⟨b, hb, hrb, eb⟩ :=
    (mov_r64_m64_effect_step 0x1191f4 0x4c (by simp [RexWPrefix])
      1 (.sib 7 (some 1) 3 .none) (by simp [AddrMode.Valid, regLow]) (by decide +kernel)
      (by decide +kernel)).advances hra
      (programText_slice (code.of_external_eq extA) 0x191f4 [0x4c,0x8b,0x0c,0xcf]
        (by decide +kernel) rfl)
      ⟨ea.rip, haddrA ▸ (output_readable hp h.agrees (by omega)).of_external_eq extA⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191f8 (by decide +kernel)))
  change (movR64M64Effect 0x1191f4 9 (.sib 7 (some 1) 3 .none) a).Holds a b at eb
  have fb : AgreesExcept [.reg 9, .rip] a b := eb.agrees
  have extB : b.external = t.external := (fb.external (by simp [Component.Covers])).trans extA
  have fab : AgreesExcept [.reg 8, .reg 9, .rip] t b := (fa.trans fb).mono (by simp)
  have axB : b.regValue .rax = if select then 1 else 0 :=
    (fab.read (r := 0) (n := 64) (by simp)).trans h.rax
  have r8B : b.regValue .r8 =
      (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read s :=
    (fb.read (r := 8) (n := 64) (by simp)).trans r8A
  have r9B : b.regValue .r9 =
      (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read s := by
    have hw : b.regValue .r9 =
      (Operand.mem ((AddrMode.sib 7 (some 1) 3 .none).addr a (0x1191f4+4)) : Operand 64).read a := eb.writes
    rw [hw, haddrA]
    change memLoad a.external _ 64 = _
    rw [extA]
    exact output_word hp hc h.agrees
  obtain ⟨c, hcc, hrc, ec⟩ := (test_al_al_effect_step 0x1191f8).advances hrb
    (programText_slice (code.of_external_eq extB) 0x191f8 [0x84,0xc0]
      (by decide +kernel) rfl) eb.rip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191fa (by decide +kernel)))
  have fc : AgreesExcept [.flags, .rip] b c := ec.agrees
  have extC : c.external = t.external := (fc.external (by simp [Component.Covers])).trans extB
  have zfC : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = !select := by
    have hz := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((Operand.reg 0 : Operand 8).read b == 0) at hz
    rw [hz]
    change ((b.regValue .rax).setWidth 8 == 0) = !select
    rw [axB]
    cases select <;> decide +kernel
  obtain ⟨d, hd, hrd, ed⟩ := (cmovne_r9_r8_effect_step 0x1191fa).advances hrc
    (programText_slice (code.of_external_eq extC) 0x191fa [0x4d,0x0f,0x45,0xc8]
      (by decide +kernel) rfl) ec.rip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191fe (by decide +kernel)))
  have fd : AgreesExcept [.reg 9, .rip] c d := ed.agrees
  have ftd : AgreesExcept [.reg 8, .reg 9, .flags, .rip] t d :=
    (((fa.trans fb).trans fc).trans fd).mono (by simp)
  have extD : d.external = t.external := ftd.external (by simp [Component.Covers])
  have r9D : d.regValue .r9 =
      if select then (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read s
      else (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read s := by
    have hw : d.regValue .r9 = if !(StatusFlags.ofRFLAGS c.RFLAGS).ZF then
      c.regValue .r8 else c.regValue .r9 := ed.writes
    have r8C : c.regValue .r8 = b.regValue .r8 := fc.read (r := 8) (n := 64) (by simp)
    have r9C : c.regValue .r9 = b.regValue .r9 := fc.read (r := 9) (n := 64) (by simp)
    rw [hw, zfC, Bool.not_not, r8C, r9C, r8B, r9B]
  have cxD : d.regValue .rcx = BitVec.ofNat 64 count :=
    (ftd.read (r := 1) (n := 64) (by simp)).trans h.rcx
  have diD : d.regValue .rdi = s.regValue .rdi :=
    (ftd.read (r := 7) (n := 64) (by simp)).trans h.rdi
  have addrD : (AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe+4) =
      s.regValue .rdi + BitVec.ofNat 64 (8*count) :=
    indexed_address (base := 7) (t := d) diD cxD hc _
  have writableD : P256.Proofs.Common.Instructions.CrossPageStore.Writable d (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8 :=
    ⟨(output_readable hp h.agrees (by omega)).of_external_eq extD,
      PageTableEntriesApart.of_frames (output_tables hp (by omega) (by decide))⟩
  have codeApart : RangeApart (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8 0x1191fe 4 := by
    intro i hi j hj hij
    have hin := output_contains hp (show 8*count+i < 32 by omega)
    rw [← add_ofNat_add_ofNat, hij] at hin
    apply hp.avoids (registerRegion s .rdi 32) (by simp) _ hin
    left
    have hh := inProgram_of_textOffset (0x191fe+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hh
    exact hh
  obtain ⟨e, he, hre, ee⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1191fe 0x4c (by simp [RexWPrefix])
      1 (.sib 7 (some 1) 3 .none) (by simp [AddrMode.Valid, regLow])
      (by decide +kernel) (by decide +kernel)).advances hrd
      (programText_slice (code.of_external_eq extD) 0x191fe [0x4c,0x89,0x0c,0xcf]
        (by decide +kernel) rfl)
      ⟨ed.rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable d ((AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe + BitVec.ofNat 64 4)) 8
        have heq : (AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe + BitVec.ofNat 64 4) =
            s.regValue .rdi + BitVec.ofNat 64 (8*count) := addrD
        rw [heq]
        exact writableD,
      by
        change RangeApart ((AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe + BitVec.ofNat 64 4)) 8 0x1191fe 4
        have heq : (AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe + BitVec.ofNat 64 4) =
            s.regValue .rdi + BitVec.ofNat 64 (8*count) := addrD
        rw [heq]
        exact codeApart⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x19202 (by decide +kernel)))
  change (movM64R64Effect 0x1191fe 9 (.sib 7 (some 1) 3 .none) d).Holds d e at ee
  have fe : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8, .rip] d e := by
    have hh := ee.agrees
    simp only [movM64R64Effect_components] at hh
    change AgreesExcept [.mem ((AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe + BitVec.ofNat 64 4)) 8, .rip] d e at hh
    have heq : (AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe + BitVec.ofNat 64 4) =
        s.regValue .rdi + BitVec.ofNat 64 (8*count) := addrD
    rwa [heq] at hh
  have fte : AgreesExcept ([.reg 8, .reg 9, .flags, .rip] ++
      [.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8]) t e :=
    (ftd.trans fe).mono (by simp)
  have fteWide : AgreesExcept (registers ++
      [.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8]) t e :=
    fte.mono (by simp [registers])
  have fse : AgreesExcept (components s (count+1)) s e := append_agrees h.agrees fteWide
  have memE : (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read e =
      if select then (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read s
      else (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read s := by
    have hw : (Operand.mem ((AddrMode.sib 7 (some 1) 3 .none).addr d (0x1191fe+4)) : Operand 64).read e =
      d.regValue .r9 := ee.writes
    rwa [addrD, r9D] at hw
  have bytesE := selected_append hp hc h fteWide memE
  have cxE : e.regValue .rcx = BitVec.ofNat 64 count :=
    (fte.read (r := 1) (n := 64) (by simp)).trans h.rcx
  have codeE := programLoaded_codeIn (loaded_of_agrees hp (by omega) fse)
  obtain ⟨f, hf, hrf, ef⟩ :=
    (inc_r64_effect_step 0x119202 0x48 0xc1 (by simp [RexWPrefix])
      (by decide +kernel) (by decide +kernel)).advances hre
      (programText_slice codeE 0x19202 [0x48,0xff,0xc1] (by decide +kernel) rfl) ee.rip
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x19205 (by decide +kernel)))
  change (incR64Effect 0x119202 1 e).Holds e f at ef
  have ff : AgreesExcept [.reg 1, .flags, .rip] e f := ef.agrees
  have cxF : f.regValue .rcx = BitVec.ofNat 64 (count+1) := by
    have hw : f.regValue .rcx = e.regValue .rcx + 1 := ef.writes
    rw [hw, cxE, BitVec.ofNat_add]
    rfl
  have siF : f.regValue .rsi = 4 :=
    (((fte.trans ff).read (r := 6) (n := 64) (by simp)).trans (h.rsi hp))
  have extF : f.external = e.external := ff.external (by simp [Component.Covers])
  obtain ⟨g, hg, hrg, eg⟩ :=
    (cmp_r64_r64_effect_step 0x119205 0x48 0xce (by simp [RexWPrefix])
      (by decide +kernel)).advances hrf
      (programText_slice (codeE.of_external_eq extF) 0x19205 [0x48,0x39,0xce]
        (by decide +kernel) rfl) ef.rip
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x19208 (by decide +kernel)))
  change (cmpR64R64Effect 0x119205 6 1 f).Holds f g at eg
  have fg : AgreesExcept [.flags, .rip] f g := eg.agrees
  have extG : g.external = e.external := (fg.external (by simp [Component.Covers])).trans extF
  have zfG : (StatusFlags.ofRFLAGS g.RFLAGS).ZF = decide (count+1 = 4) := by
    have hz := eg.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS g.RFLAGS).ZF = (f.regValue .rsi - f.regValue .rcx == 0) at hz
    rw [hz, siF, cxF]
    have hcases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> decide +kernel
  have branchRip : (jccEffect 0x119208 2 5 ((0xe6 : BitVec 8).signExtend 64) g).rip =
      if count+1 = 4 then 0x11920a else 0x1191f0 := by
    change (if !(StatusFlags.ofRFLAGS g.RFLAGS).ZF then (0x1191f0 : BitVec 64) else 0x11920a) = _
    rw [zfG]
    by_cases hn : count+1 = 4 <;> simp [hn]
  obtain ⟨u, hu, hru, eu⟩ := (jcc_rel8_effect_step 0x119208 5 0xe6).advances hrg
    (programText_slice (codeE.of_external_eq extG) 0x19208 [0x75,0xe6]
      (by decide +kernel) rfl) ⟨eg.rip, by intro _; decide +kernel⟩
    (by rw [branchRip]
        split
        · exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1920a (by decide +kernel))
        · exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191f0 (by decide +kernel)))
  have fu : AgreesExcept [.rip] g u := eu.agrees
  have feu : AgreesExcept [.reg 1, .flags, .rip] e u :=
    ((ff.trans fg).trans fu).mono (by simp)
  have ftu : AgreesExcept ([.reg 1, .reg 8, .reg 9, .flags, .rip] ++
      [.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8]) t u :=
    (fte.trans feu).mono (by simp)
  refine ⟨u, ((((((ha.trans hb).trans hcc).trans hd).trans he).trans hf).trans hg).trans hu,
    ⟨hru, ?_, ?_, ?_, ?_, ?_⟩, eu.rip.trans branchRip⟩
  · exact append_agrees h.agrees (ftu.mono (by simp [registers]))
  · exact (ftu.read (r := 4) (n := 64) (by simp)).trans h.rsp
  · exact (ftu.read (r := 0) (n := 64) (by simp)).trans h.rax
  · exact ((fg.trans fu).read (r := 1) (n := 64) (by simp)).trans cxF
  · intro i hi
    exact (feu.byte (by simp [Component.Covers])).trans (bytesE i hi)

end P256.Proofs.Program.LimbSelect
