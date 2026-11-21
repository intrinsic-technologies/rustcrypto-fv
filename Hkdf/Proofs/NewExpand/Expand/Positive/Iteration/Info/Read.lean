import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Hkdf.Proofs.NewExpand.Expand.Info

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine

def readBytes : List UInt8 :=
  [0x49,0x8b,0x5d,0,0x49,0x8b,0x6d,8,0x44,0x0f,0xb6,0xb4,0x24,0x4f,1,0,0,
   0xba,0x40,0,0,0,0x4c,0x29,0xf2,0x49,0x89,0xef,0x49,0x29,0xd7,0x72,0xae]

def bufferIndex (s : RamState) : BitVec 64 :=
  ((Operand.mem (rspOf s + 335) : Operand 8).read s).setWidth 64

def inputLength (s : RamState) : BitVec 64 :=
  (Operand.mem ((Operand.reg 13 : Operand 64).read s + 8) : Operand 64).read s

theorem readDescriptor [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pc : s.RIP = 0x10f721)
    (pointer : MemReadable s ((Operand.reg 13 : Operand 64).read s) 8)
    (length : MemReadable s ((Operand.reg 13 : Operand 64).read s + 8) 8)
    (index : MemReadable s (rspOf s + 335) 1) (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧
      t.RIP = (if (inputLength s).toNat < (64 - bufferIndex s).toNat then 0x10f6f0 else 0x10f742) ∧
      (Operand.reg 3 : Operand 64).read t =
        (Operand.mem ((Operand.reg 13 : Operand 64).read s) : Operand 64).read s ∧
      (Operand.reg 5 : Operand 64).read t = inputLength s ∧
      (Operand.reg 14 : Operand 64).read t = bufferIndex s ∧
      (Operand.reg 2 : Operand 64).read t = 64 - bufferIndex s ∧
      (Operand.reg 15 : Operand 64).read t = inputLength s - (64 - bufferIndex s) ∧
      AgreesExcept [.reg 3, .reg 5, .reg 14, .reg 2, .reg 15, .flags, .rip] s t ∧
      t.external = s.external := by
  have code : CodeIn (codeRange 0x10f721 readBytes) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf721 _ (by decide) (by decide +kernel)
  have pre1 : LoadPre 0x10f721 (fun u => (AddrMode.base 13 (.d8 0)).addr u (0x10f721 + 4)) 8 s := by
    exact ⟨pc, by simpa only [x86_compose, BitVec.add_zero] using pointer⟩
  obtain ⟨s1, st1, r1, e1⟩ := mov_r64_m64_effect_step 0x10f721 0x49 (by simp [RexWPrefix])
    3 (.base 13 (.d8 0)) (by decide) rfl rfl s ready
    (code.mono (codeRange_mem_of_drop (p := 0x10f721) 0 (by decide +kernel))) pre1
  change (movR64M64Effect 0x10f721 3 (.base 13 (.d8 0)) s).Holds s s1 at e1
  have ag1 : AgreesExcept [.reg 3, .rip] s s1 := e1.agrees
  have m1 : s1.external = s.external := ag1.external (by simp [Component.Covers])
  have v1 : (Operand.reg 3 : Operand 64).read s1 =
      (Operand.mem ((Operand.reg 13 : Operand 64).read s) : Operand 64).read s := by
    have val : (Operand.reg 3 : Operand 64).read s1 =
        (Operand.mem ((Operand.reg 13 : Operand 64).read s + 0#64) : Operand 64).read s := e1.writes
    simpa only [BitVec.add_zero] using val
  have cur1 : (Operand.reg 13 : Operand 64).read s1 = (Operand.reg 13 : Operand 64).read s :=
    ag1.read (by simp)
  have sp1 : rspOf s1 = rspOf s := ag1.read (by simp)
  have read1 : MemReadable s1 ((Operand.reg 13 : Operand 64).read s1 + 8) 8 := by
    rw [cur1]
    exact ⟨length.low, fun i hi => ag1.grow _ (length.mem i hi)⟩
  obtain ⟨s2, st2, r2, e2⟩ := mov_r64_m64_effect_step 0x10f725 0x49 (by simp [RexWPrefix])
    5 (.base 13 (.d8 8)) (by decide) rfl rfl s1 r1
    ((code.of_external_eq m1).mono (codeRange_mem_of_drop (p := 0x10f721) 4 (by decide +kernel)))
    ⟨e1.rip, by simpa only [x86_compose] using read1⟩
  change (movR64M64Effect 0x10f725 5 (.base 13 (.d8 8)) s1).Holds s1 s2 at e2
  have ag2 : AgreesExcept [.reg 5, .rip] s1 s2 := e2.agrees
  have ag12 := ag1.trans ag2
  have m2 : s2.external = s.external := ag12.external (by simp [Component.Covers])
  have sp2 : rspOf s2 = rspOf s := ag12.read (by simp)
  have v2 : (Operand.reg 5 : Operand 64).read s2 = inputLength s := by
    have val : (Operand.reg 5 : Operand 64).read s2 =
        (Operand.mem ((Operand.reg 13 : Operand 64).read s1 + 8) : Operand 64).read s1 := e2.writes
    rw [cur1] at val
    change _ = memLoad s1.external _ 64 at val
    rw [m1] at val
    exact val
  have read2 : MemReadable s2 (rspOf s2 + 335) 1 := by
    rw [sp2]
    exact ⟨index.low, fun i hi => ag12.grow _ (index.mem i hi)⟩
  obtain ⟨s3, st3, r3, e3⟩ := movzx_r32_m8_rex_effect_step 0x10f729 0x44 (by simp [RexNoWPrefix])
    6 (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl s2 r2
    ((code.of_external_eq m2).mono (codeRange_mem_of_drop (p := 0x10f721) 8 (by decide +kernel)))
    ⟨e2.rip, by simpa only [x86_compose] using read2⟩
  change (movzxR32M8Effect 0x10f729 9 14 (.sib 4 none 0 (.d32 335)) s2).Holds s2 s3 at e3
  have ag3 : AgreesExcept [.reg 14, .rip] s2 s3 := e3.agrees
  have ag123 := ag12.trans ag3
  have m3 : s3.external = s.external := ag123.external (by simp [Component.Covers])
  have v3 : (Operand.reg 14 : Operand 64).read s3 = bufferIndex s := by
    have val : (Operand.reg 14 : Operand 64).read s3 =
        ((Operand.mem (rspOf s2 + 335) : Operand 8).read s2).setWidth 64 := e3.writes
    rw [sp2] at val
    change _ = (memLoad s2.external _ 8).setWidth 64 at val
    rw [m2] at val
    exact val
  obtain ⟨s4, st4, r4, e4⟩ := mov_r32_imm32_effect_step 0x10f732 0xba (by decide) 64 s3 r3
    ((code.of_external_eq m3).mono (codeRange_mem_of_drop (p := 0x10f721) 17 (by decide +kernel))) e3.rip
  change (movR32Imm32Effect 0x10f732 5 2 64 s3).Holds s3 s4 at e4
  have ag4 : AgreesExcept [.reg 2, .rip] s3 s4 := e4.agrees
  have ag1234 := ag123.trans ag4
  have m4 : s4.external = s.external := ag1234.external (by simp [Component.Covers])
  have v4 : (Operand.reg 2 : Operand 64).read s4 = 64 := e4.writes
  have bp4 : (Operand.reg 14 : Operand 64).read s4 = bufferIndex s := (ag4.read (by simp)).trans v3
  obtain ⟨s5, st5, r5, e5⟩ := sub_r64_r64_effect_step 0x10f737 0x4c 0xf2
    (by simp [RexWPrefix]) (by decide) s4 r4
    ((code.of_external_eq m4).mono (codeRange_mem_of_drop (p := 0x10f721) 22 (by decide +kernel))) e4.rip
  change (subR64R64Effect 0x10f737 2 14 s4).Holds s4 s5 at e5
  have ag5 : AgreesExcept [.reg 2, .flags, .rip] s4 s5 := e5.agrees
  have ag12345 := ag1234.trans ag5
  have m5 : s5.external = s.external := ag12345.external (by simp [Component.Covers])
  have v5 : (Operand.reg 2 : Operand 64).read s5 = 64 - bufferIndex s := by
    have val : (Operand.reg 2 : Operand 64).read s5 =
        (Operand.reg 2 : Operand 64).read s4 - (Operand.reg 14 : Operand 64).read s4 := e5.writes
    rw [v4, bp4] at val
    exact val
  obtain ⟨s6, st6, r6, e6⟩ := mov_r64_r64_effect_step 0x10f73a 0x49 0xef
    (by simp [RexWPrefix]) (by decide) s5 r5
    ((code.of_external_eq m5).mono (codeRange_mem_of_drop (p := 0x10f721) 25 (by decide +kernel))) e5.rip
  change (movR64R64Effect 0x10f73a 15 5 s5).Holds s5 s6 at e6
  have ag6 : AgreesExcept [.reg 15, .rip] s5 s6 := e6.agrees
  have ag123456 := ag12345.trans ag6
  have m6 : s6.external = s.external := ag123456.external (by simp [Component.Covers])
  have v6 : (Operand.reg 15 : Operand 64).read s6 = inputLength s :=
    e6.writes.trans (((ag3.trans ag4).trans ag5).read (by simp) |>.trans v2)
  have dx6 : (Operand.reg 2 : Operand 64).read s6 = 64 - bufferIndex s := (ag6.read (by simp)).trans v5
  obtain ⟨s7, st7, r7, e7⟩ := sub_r64_r64_effect_step 0x10f73d 0x49 0xd7
    (by simp [RexWPrefix]) (by decide) s6 r6
    ((code.of_external_eq m6).mono (codeRange_mem_of_drop (p := 0x10f721) 28 (by decide +kernel))) e6.rip
  change (subR64R64Effect 0x10f73d 15 2 s6).Holds s6 s7 at e7
  have ag7 : AgreesExcept [.reg 15, .flags, .rip] s6 s7 := e7.agrees
  have ag1234567 := ag123456.trans ag7
  have m7 : s7.external = s.external := ag1234567.external (by simp [Component.Covers])
  have v7 : (Operand.reg 15 : Operand 64).read s7 = inputLength s - (64 - bufferIndex s) := by
    have val : (Operand.reg 15 : Operand 64).read s7 =
        (Operand.reg 15 : Operand 64).read s6 - (Operand.reg 2 : Operand 64).read s6 := e7.writes
    rw [v6, dx6] at val
    exact val
  have cf : (StatusFlags.ofRFLAGS s7.RFLAGS).CF =
      decide ((inputLength s).toNat < (64 - bufferIndex s).toNat) := by
    have val := e7.flags.1
    change (StatusFlags.ofRFLAGS s7.RFLAGS).CF =
      decide (((Operand.reg 15 : Operand 64).read s6).toNat <
        ((Operand.reg 2 : Operand 64).read s6).toNat) at val
    rw [v6, dx6] at val
    exact val
  obtain ⟨t, st8, rt, e8⟩ := jcc_rel8_effect_step 0x10f740 2 0xae s7 r7
    ((code.of_external_eq m7).mono (codeRange_mem_of_drop (p := 0x10f721) 31 (by decide +kernel)))
    ⟨e7.rip, by intro; decide⟩
  have ag8 : AgreesExcept [.rip] s7 t := e8.agrees
  have all : AgreesExcept [.reg 3, .reg 5, .reg 14, .reg 2, .reg 15, .flags, .rip] s t :=
    (ag1234567.trans ag8).mono (by simp)
  have a1 : Advances boundary 1 s s1 := Advances.of_step st1 (.inl (by rw [e1.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf725 (by decide))))
  have a2 : Advances boundary 1 s1 s2 := Advances.of_step st2 (.inl (by rw [e2.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf729 (by decide))))
  have a3 : Advances boundary 1 s2 s3 := Advances.of_step st3 (.inl (by rw [e3.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf732 (by decide))))
  have a4 : Advances boundary 1 s3 s4 := Advances.of_step st4 (.inl (by rw [e4.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf737 (by decide))))
  have a5 : Advances boundary 1 s4 s5 := Advances.of_step st5 (.inl (by rw [e5.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf73a (by decide))))
  have a6 : Advances boundary 1 s5 s6 := Advances.of_step st6 (.inl (by rw [e6.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf73d (by decide))))
  have a7 : Advances boundary 1 s6 s7 := Advances.of_step st7 (.inl (by rw [e7.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf740 (by decide))))
  have target : t.RIP = if (inputLength s).toNat < (64 - bufferIndex s).toNat then 0x10f6f0 else 0x10f742 := by
    simpa [jccEffect, branchEffect, condHolds, branchTarget, cf] using e8.rip
  have a8 : Advances boundary 1 s7 t := Advances.of_step st8 (.inl (by
      rw [target]
      split
      · exact boundary_ne_program outer (inProgram_of_textOffset 0xf6f0 (by decide))
      · exact boundary_ne_program outer (inProgram_of_textOffset 0xf742 (by decide))))
  refine ⟨t, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8,
    rt, target, ?_, ?_, ?_, ?_, ?_, all, all.external (by simp [Component.Covers])⟩
  · exact ((((((ag2.trans ag3).trans ag4).trans ag5).trans ag6).trans ag7).trans ag8).read
      (by simp) |>.trans v1
  · exact (((((ag3.trans ag4).trans ag5).trans ag6).trans ag7).trans ag8).read
      (by simp) |>.trans v2
  · exact ((((ag4.trans ag5).trans ag6).trans ag7).trans ag8).read (by simp) |>.trans v3
  · exact ((ag6.trans ag7).trans ag8).read (by simp) |>.trans v5
  · exact (ag8.read (by simp)).trans v7

theorem branchOnBufferedBytes [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pc : s.RIP = 0x10f742)
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (Operand.reg 14 : Operand 64).read s = 0 then 0x10f7f5 else 0x10f74b) ∧
      AgreesExcept [.flags, .rip] s t ∧ t.external = s.external := by
  have testCode : CodeIn (codeRange 0x10f742 [0x4d, 0x85, 0xf6]) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf742 _ (by decide) (by decide +kernel)
  obtain ⟨u, st1, ru, e1⟩ := test_r64_r64_effect_step 0x10f742 0x4d 0xf6
    (by simp [RexWPrefix]) (by decide) s ready testCode pc
  change (testR64R64Effect 0x10f742 14 14 s).Holds s u at e1
  have ag1 : AgreesExcept [.flags, .rip] s u := e1.agrees
  have mem1 : u.external = s.external := ag1.external (by simp [Component.Covers])
  have sp1 : rspOf u = rspOf s := ag1.read (by simp)
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((Operand.reg 14 : Operand 64).read s == 0) := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((Operand.reg 14 : Operand 64).read s &&& (Operand.reg 14 : Operand 64).read s) == 0) at h
    simpa only [BitVec.and_self] using h
  have branchCode : CodeIn (codeRange 0x10f745 [0x0f, 0x84, 0xaa, 0, 0, 0]) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf745 _ (by decide) (by decide +kernel)
  obtain ⟨t, st2, rt, e2⟩ := jcc_rel32_effect_step 0x10f745 4 0xaa u ru
    (branchCode.of_external_eq mem1) ⟨e1.rip, by intro; decide⟩
  have ag2 : AgreesExcept [.rip] u t := e2.agrees
  have ag : AgreesExcept [.flags, .rip] s t := (ag1.trans ag2).mono (by simp)
  have sp2 : rspOf t = rspOf s := ag.read (by simp)
  have target : t.RIP = if (Operand.reg 14 : Operand 64).read s = 0 then 0x10f7f5 else 0x10f74b := by
    simpa [jccEffect, branchEffect, condHolds, branchTarget, zf] using e2.rip
  exact ⟨t, (Advances.of_step st1 (.inl (by rw [e1.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf745 (by decide))))).trans
    (Advances.of_step st2 (.inl (by
      rw [target]
      split
      · exact boundary_ne_program outer (inProgram_of_textOffset 0xf7f5 (by decide))
      · exact boundary_ne_program outer (inProgram_of_textOffset 0xf74b (by decide))))), rt,
    target,
    ag, ag.external (by simp [Component.Covers])⟩

end Hkdf.Proofs.NewExpand.Expand.Info
