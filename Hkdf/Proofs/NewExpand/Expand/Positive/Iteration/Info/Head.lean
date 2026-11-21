import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.MovLoad.Triple

namespace Hkdf.Proofs.NewExpand.Expand.Info

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine

private def headBytes : List UInt8 :=
  [0x4c,0x89,0xbc,0x24,0xb0,1,0,0,0x48,0x83,0xbc,0x24,0xf8,0,0,0,0,
   0x0f,0x84,0xc6,1,0,0,0x4c,0x8b,0xac,0x24,0xe8,0,0,0,0xeb,0x3d]

theorem start [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pc : s.RIP = 0x10f6c3)
    (count : (Operand.mem (rspOf s + 248) : Operand 64).read s ≠ 0)
    (readCount : MemReadable s (rspOf s + 248) 8)
    (readTable : MemReadable s (rspOf s + 232) 8)
    (writable : MemWritable s (rspOf s + 432) 8)
    (apart : RangeApart (rspOf s + 432) 8 0x10f6c3 33)
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x10f721 ∧
      (Operand.mem (rspOf s + 432) : Operand 64).read t = (Operand.reg 15 : Operand 64).read s ∧
      (Operand.reg 13 : Operand 64).read t = (Operand.mem (rspOf s + 232) : Operand 64).read s ∧
      AgreesExcept [.mem (rspOf s + 432) 8, .flags, .rip, .reg 13] s t := by
  have code : CodeIn (codeRange 0x10f6c3 headBytes) s :=
    programText_slice (programLoaded_codeIn loaded) 0xf6c3 _ (by decide) (by decide +kernel)
  obtain ⟨s1, st1, r1, e1⟩ := mov_m64_r64_effect_step 0x10f6c3 0x4c
    (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 432)) (by decide) rfl rfl s ready
    (code.mono (codeRange_mem_of_drop (p := 0x10f6c3) 0 (by decide +kernel)))
    ⟨pc, writable, apart.sub0 8 (by decide)⟩
  change (movM64R64Effect 0x10f6c3 15 (.sib 4 none 0 (.d32 432)) s).Holds s s1 at e1
  have ag1 : AgreesExcept [.mem (rspOf s + 432) 8, .rip] s s1 := by
    simpa only [x86_compose] using e1.agrees
  have sp1 : rspOf s1 = rspOf s := ag1.read (by simp)
  have code1 : CodeIn (codeRange 0x10f6c3 headBytes) s1 :=
    e1.codeIn (by x86_avoid) code
  have mem1 (offset : BitVec 64) (off : offset = 232 ∨ offset = 248) :
      (Operand.mem (rspOf s + offset) : Operand 64).read s1 =
        (Operand.mem (rspOf s + offset) : Operand 64).read s := by
    apply Common.Encoding.Serialize.read_mem_of_agrees ag1
    intro i hi c hc cov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := cov
      rcases off with rfl | rfl
      · exact (RangeApart.offsets (rspOf s) (a := 232) (b := 432) (len := 8) (count := 8)
          (by decide) (by decide) (by decide)) i hi j hj he
      · exact (RangeApart.offsets (rspOf s) (a := 248) (b := 432) (len := 8) (count := 8)
          (by decide) (by decide) (by decide)) i hi j hj he
    · exact cov.elim
  have countReadable : MemReadable s1 (rspOf s1 + 248) 8 := by
    rw [sp1]
    have h := readCount
    exact ⟨h.low, fun i hi => ag1.grow _ (h.mem i hi)⟩
  obtain ⟨s2, st2, r2, e2⟩ := cmp_m64_imm8_effect_step 0x10f6cb 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl 0 s1 r1
    (code1.mono (codeRange_mem_of_drop (p := 0x10f6c3) 8 (by decide +kernel)))
    ⟨e1.rip, by simpa only [x86_compose] using countReadable⟩
  have ag2 : AgreesExcept [.flags, .rip] s1 s2 := e2.agrees
  have sp2 : rspOf s2 = rspOf s := (ag2.read (by simp)).trans sp1
  have code2 := e2.codeIn (by x86_avoid) code1
  have zf : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      ((Operand.mem (rspOf s + 248) : Operand 64).read s == 0) := by
    have h := e2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (cmpSpec ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 248)).addr s1 (0x10f6cb + 9)) : Operand 64).read s1) 0).ZF at h
    have h1 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
        ((Operand.mem (rspOf s1 + 248) : Operand 64).read s1 == 0) := by
      simpa only [x86_compose, cmpSpec, subSpec, BitVec.sub_zero] using h
    rw [sp1, mem1 248 (.inr rfl)] at h1
    exact h1
  obtain ⟨s3, st3, r3, e3⟩ := jcc_rel32_effect_step 0x10f6d4 4 0x1c6 s2 r2
    (code2.mono (codeRange_mem_of_drop (p := 0x10f6c3) 17 (by decide +kernel)))
    ⟨e2.rip, by intro; decide⟩
  have ag3 : AgreesExcept [.rip] s2 s3 := e3.agrees
  have sp3 : rspOf s3 = rspOf s := (ag3.read (by simp)).trans sp2
  have pc3 : s3.RIP = if (Operand.mem (rspOf s + 248) : Operand 64).read s = 0 then 0x10f8a0 else 0x10f6da := by
    simpa [jccEffect, branchEffect, condHolds, zf, branchTarget] using e3.rip
  have adv1 := Advances.of_step st1 (.inl (by rw [e1.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf6cb (by decide))))
  have adv2 := Advances.of_step st2 (.inl (by rw [e2.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf6d4 (by decide))))
  have adv3 := Advances.of_step st3 (.inl (by rw [pc3, ite_eq_right count]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf6da (by decide))))
  have saved : (Operand.mem (rspOf s + 432) : Operand 64).read s3 =
      (Operand.reg 15 : Operand 64).read s := by
    have mem := Common.Encoding.Serialize.read_mem_of_agrees (n := 64) (ag2.trans ag3) (rspOf s + 432) (by simp [Component.Covers])
    have val : (Operand.mem (rspOf s + 432) : Operand 64).read s1 =
        (Operand.reg 15 : Operand 64).read s := e1.writes
    exact mem.trans val
  have code3 := e3.codeIn (by unfold jccEffect branchEffect; x86_avoid) code2
  have tableReadable : MemReadable s3 (rspOf s3 + 232) 8 := by
    rw [sp3]
    have h := readTable
    exact ⟨h.low, fun i hi => ((ag1.trans ag2).trans ag3).grow _ (h.mem i hi)⟩
  obtain ⟨s4, st4, r4, e4⟩ := mov_r64_m64_effect_step 0x10f6da 0x4c
    (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl s3 r3
    (code3.mono (codeRange_mem_of_drop (p := 0x10f6c3) 23 (by decide +kernel)))
    ⟨by simpa only [ite_eq_right count] using pc3, by simpa only [x86_compose] using tableReadable⟩
  change (movR64M64Effect 0x10f6da 13 (.sib 4 none 0 (.d32 232)) s3).Holds s3 s4 at e4
  have ag4 : AgreesExcept [.reg 13, .rip] s3 s4 := e4.agrees
  have code4 := e4.codeIn (by x86_avoid) code3
  obtain ⟨t, st5, rt, e5⟩ := jmp_rel8_effect_step 0x10f6e2 0x3d (by decide) s4 r4
    (code4.mono (codeRange_mem_of_drop (p := 0x10f6c3) 31 (by decide +kernel))) e4.rip
  have ag5 : AgreesExcept [.rip] s4 t := e5.agrees
  refine ⟨t, ((((adv1.trans adv2).trans adv3).trans
    (Advances.of_step st4 (.inl (by rw [e4.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf6e2 (by decide)))))).trans
    (Advances.of_step st5 (.inl (by rw [e5.rip]; exact boundary_ne_program outer (inProgram_of_textOffset 0xf721 (by decide)))))), rt, (show t.RIP = 0x10f721 from e5.rip), ?_, ?_, ?_⟩
  · exact (Common.Encoding.Serialize.read_mem_of_agrees (n := 64) (ag4.trans ag5) _ (by simp [Component.Covers])).trans saved
  · have val : (Operand.reg 13 : Operand 64).read s4 =
        (Operand.mem (rspOf s3 + 232) : Operand 64).read s3 := e4.writes
    rw [sp3] at val
    have keep : (Operand.mem (rspOf s + 232) : Operand 64).read s3 =
        (Operand.mem (rspOf s + 232) : Operand 64).read s1 := by
      exact Common.Encoding.Serialize.read_mem_of_agrees (ag2.trans ag3) _ (by simp [Component.Covers])
    exact (ag5.read (by simp)).trans (val.trans (keep.trans (mem1 232 (.inl rfl))))
  · exact ((((ag1.trans ag2).trans ag3).trans ag4).trans ag5).mono (by simp)

end Hkdf.Proofs.NewExpand.Expand.Info
