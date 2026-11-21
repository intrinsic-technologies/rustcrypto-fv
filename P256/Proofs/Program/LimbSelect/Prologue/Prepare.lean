import P256.Proofs.Program.LimbSelect.Prologue.Stack
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {s : RamState} {boundary : ReturnBoundary} {select : Bool}
    (hp : Pre s boundary) (hs : (s.regValue .r8).setWidth 8 = if select then 1 else 0) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ AgreesExcept (components s 0) s t ∧
      t.RIP = 0x1191dd ∧ t.regValue .rsp = s.regValue .rsp - 72 ∧
      t.regValue .rax = (if select then 1 else 0) ∧ t.regValue .rcx = 4 := by
  have code := programLoaded_codeIn hp.loaded
  obtain ⟨a, ha, hra, ea⟩ :=
    (sub_r64_imm8_effect_step 0x1191c0 0x48 0xec 72 (by simp [RexWPrefix])
      (by decide +kernel) (by decide +kernel)).advances (readyToStep hp.machine hp.bindingsSupported)
      (programText_slice code 0x191c0 [0x48,0x83,0xec,0x48] (by decide +kernel) rfl) hp.rip
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191c4 (by decide +kernel)))
  change (subR64Imm8Effect 0x1191c0 4 72 s).Holds s a at ea
  have fa : AgreesExcept [.reg 4, .flags, .rip] s a := ea.agrees
  have fsa : AgreesExcept (components s 0) s a := fa.mono (by simp [components, registers])
  have spA : a.regValue .rsp = s.regValue .rsp - 72 := ea.writes
  have r8A : (a.regValue .r8).setWidth 8 = if select then 1 else 0 :=
    (congrArg (BitVec.setWidth 8) (fa.read (r := 8) (n := 64) (by simp))).trans hs
  have addrA (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 7)).addr a next = stackPtr s-65 :=
    stack_offset spA (offset := 7) (by decide) next
  have writableA : MemWritable a (stackPtr s-65) 1 := by
    apply P256.Proofs.Program.writable_of_grow _ fsa.grow
    apply P256.Proofs.Program.stack_sub_writable hp.stack (fun a ha ht ↦ hp.avoids _ (by simp) a ha (.inr ht)) (offset := 65) (len := 1)
      (by decide) (by decide) (by decide)
    have := Nat.mod_lt (stackPtr s-65).toNat (show 0 < 4096 by decide)
    omega
  obtain ⟨b, hb, hrb, eb⟩ :=
    (mov_m8_r8_effect_step 0x1191c4 0x44 (by simp [RexPrefix]) 0 (.sib 4 none 0 (.d8 7))
      (by simp [AddrMode.Valid]) (by decide +kernel) (by decide +kernel)).advances hra
      (programText_slice (programLoaded_codeIn (loaded_of_agrees hp (by decide) fsa))
        0x191c4 [0x44,0x88,0x44,0x24,0x07] (by decide +kernel) rfl)
      ⟨ea.rip, by
        change MemWritable a ((AddrMode.sib 4 none 0 (.d8 7)).addr a _) 1
        rw [addrA]; exact writableA,
       by
        change RangeApart ((AddrMode.sib 4 none 0 (.d8 7)).addr a _) 1 0x1191c4 5
        rw [addrA]
        exact stack_offset_code hp (offset := 65) (p := 0x191c4) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191c9 (by decide +kernel)))
  have fb : AgreesExcept [.mem (stackPtr s-65) 1, .rip] a b := by
    have hh := eb.agrees
    simp only [storeEffect_components] at hh
    change AgreesExcept [.mem ((AddrMode.sib 4 none 0 (.d8 7)).addr a _) 1, .rip] a b at hh
    simpa only [addrA] using hh
  have fsb : AgreesExcept (components s 0) s b :=
    stack_store_frame fsa (offset := 65) (by decide) (by decide) (by decide) fb
  have spB : b.regValue .rsp = s.regValue .rsp - 72 :=
    (fb.read (r := 4) (n := 64) (by simp)).trans spA
  have addrB (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 7)).addr b next = stackPtr s-65 :=
    stack_offset spB (offset := 7) (by decide) next
  have flagB : (Operand.mem (stackPtr s-65) : Operand 8).read b =
      (if select then 1 else 0) := by
    have hw : (Operand.mem ((AddrMode.sib 4 none 0 (.d8 7)).addr a _) : Operand 8).read b =
      (Operand.reg 8 : Operand 8).read a := eb.writes
    rw [addrA] at hw
    change (Operand.mem (stackPtr s-65) : Operand 8).read b = (a.regValue .r8).setWidth 8 at hw
    exact hw.trans r8A
  obtain ⟨c, hcc, hrc, ec⟩ :=
    (lea_r64_effect_step 0x1191c9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 7))
      (by simp [AddrMode.Valid]) (by decide +kernel) (by decide +kernel)).advances hrb
      (programText_slice (programLoaded_codeIn (loaded_of_agrees hp (by decide) fsb))
        0x191c9 [0x48,0x8d,0x44,0x24,0x07] (by decide +kernel) rfl) eb.rip
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191ce (by decide +kernel)))
  change (leaR64Effect 0x1191c9 0 (.sib 4 none 0 (.d8 7)) b).Holds b c at ec
  have fc : AgreesExcept [.reg 0, .rip] b c := ec.agrees
  have fsc : AgreesExcept (components s 0) s c := (fsb.trans fc).mono (by simp [components, registers])
  have spC : c.regValue .rsp = s.regValue .rsp-72 :=
    (fc.read (r := 4) (n := 64) (by simp)).trans spB
  have addrC (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 7)).addr c next = stackPtr s-65 :=
    stack_offset spC (offset := 7) (by decide) next
  have extC : c.external = b.external := fc.external (by simp [Component.Covers])
  obtain ⟨d, hd, hrd, ed⟩ :=
    (movzx_r32_m8_effect_step 0x1191ce 0 (.sib 4 none 0 (.d8 7))
      (by simp [AddrMode.Valid]) (by decide +kernel) (by decide +kernel)).advances hrc
      (programText_slice (programLoaded_codeIn (loaded_of_agrees hp (by decide) fsc))
        0x191ce [0x0f,0xb6,0x44,0x24,0x07] (by decide +kernel) rfl)
      ⟨ec.rip, by
        change MemReadable c ((AddrMode.sib 4 none 0 (.d8 7)).addr c _) 1
        rw [addrC]
        exact P256.Proofs.Program.readable_of_grow
          (P256.Proofs.Program.stack_sub_readable hp.stack (offset := 65) (len := 1) (by decide) (by decide)) fsc.grow⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191d3 (by decide +kernel)))
  change (movzxR32M8Effect 0x1191ce 5 0 (.sib 4 none 0 (.d8 7)) c).Holds c d at ed
  have fd : AgreesExcept [.reg 0, .rip] c d := ed.agrees
  have fsd : AgreesExcept (components s 0) s d := (fsc.trans fd).mono (by simp [components, registers])
  have spD : d.regValue .rsp = s.regValue .rsp-72 :=
    (fd.read (r := 4) (n := 64) (by simp)).trans spC
  have axD : d.regValue .rax = if select then 1 else 0 := by
    have hw : d.regValue .rax =
      ((Operand.mem ((AddrMode.sib 4 none 0 (.d8 7)).addr c _) : Operand 8).read c).setWidth 64 := ed.writes
    rw [hw, addrC]
    change (memLoad c.external (stackPtr s-65) 8).setWidth 64 = _
    rw [extC]
    change ((Operand.mem (stackPtr s-65) : Operand 8).read b).setWidth 64 = _
    rw [flagB]
    cases select <;> rfl
  have addrD (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 8)).addr d next = stackPtr s-64 :=
    stack_offset spD (offset := 8) (by decide) next
  obtain ⟨e, he, hre, ee⟩ :=
    (mov_m64_r64_effect_step 0x1191d3 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8))
      (by simp [AddrMode.Valid]) (by decide +kernel) (by decide +kernel)).advances hrd
      (programText_slice (programLoaded_codeIn (loaded_of_agrees hp (by decide) fsd))
        0x191d3 [0x48,0x89,0x74,0x24,0x08] (by decide +kernel) rfl)
      ⟨ed.rip, by
        change MemWritable d ((AddrMode.sib 4 none 0 (.d8 8)).addr d _) 8
        rw [addrD]
        exact P256.Proofs.Program.writable_of_grow
          (P256.Proofs.Program.stack_sub_writable8 hp.stack (fun a ha ht ↦ hp.avoids _ (by simp) a ha (.inr ht)) (offset := 64) (by decide) (by decide)) fsd.grow,
       by
        change RangeApart ((AddrMode.sib 4 none 0 (.d8 8)).addr d _) 8 0x1191d3 5
        rw [addrD]
        exact stack_offset_code hp (offset := 64) (p := 0x191d3) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191d8 (by decide +kernel)))
  have fe : AgreesExcept [.mem (stackPtr s-64) 8, .rip] d e := by
    have hh := ee.agrees
    simp only [movM64R64Effect_components] at hh
    change AgreesExcept [.mem ((AddrMode.sib 4 none 0 (.d8 8)).addr d _) 8, .rip] d e at hh
    simpa only [addrD] using hh
  have fse : AgreesExcept (components s 0) s e :=
    stack_store_frame fsd (offset := 64) (by decide) (by decide) (by decide) fe
  have spE : e.regValue .rsp = s.regValue .rsp-72 :=
    (fe.read (r := 4) (n := 64) (by simp)).trans spD
  have addrE (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 16)).addr e next = stackPtr s-56 :=
    stack_offset spE (offset := 16) (by decide) next
  obtain ⟨f, hf, hrf, ef⟩ :=
    (mov_m64_r64_effect_step 0x1191d8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16))
      (by simp [AddrMode.Valid]) (by decide +kernel) (by decide +kernel)).advances hre
      (programText_slice (programLoaded_codeIn (loaded_of_agrees hp (by decide) fse))
        0x191d8 [0x48,0x89,0x4c,0x24,0x10] (by decide +kernel) rfl)
      ⟨ee.rip, by
        change MemWritable e ((AddrMode.sib 4 none 0 (.d8 16)).addr e _) 8
        rw [addrE]
        exact P256.Proofs.Program.writable_of_grow
          (P256.Proofs.Program.stack_sub_writable8 hp.stack (fun a ha ht ↦ hp.avoids _ (by simp) a ha (.inr ht)) (offset := 56) (by decide) (by decide)) fse.grow,
       by
        change RangeApart ((AddrMode.sib 4 none 0 (.d8 16)).addr e _) 8 0x1191d8 5
        rw [addrE]
        exact stack_offset_code hp (offset := 56) (p := 0x191d8) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x191dd (by decide +kernel)))
  have ff : AgreesExcept [.mem (stackPtr s-56) 8, .rip] e f := by
    have hh := ef.agrees
    simp only [movM64R64Effect_components] at hh
    change AgreesExcept [.mem ((AddrMode.sib 4 none 0 (.d8 16)).addr e _) 8, .rip] e f at hh
    simpa only [addrE] using hh
  have fsf : AgreesExcept (components s 0) s f :=
    stack_store_frame fse (offset := 56) (by decide) (by decide) (by decide) ff
  refine ⟨f, ((((ha.trans hb).trans hcc).trans hd).trans he).trans hf,
    hrf, fsf, ef.rip, ?_, ?_, ?_⟩
  · exact (ff.read (r := 4) (n := 64) (by simp)).trans spE
  · exact ((fe.trans ff).read (r := 0) (n := 64) (by simp)).trans axD
  · exact (((((fa.trans fb).trans fc).trans fd).trans fe).trans ff).read
      (r := 1) (n := 64) (by simp) |>.trans hp.rightCount

end P256.Proofs.Program.LimbSelect
