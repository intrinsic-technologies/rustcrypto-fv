import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def bulkPrepareBytes : List UInt8 :=
  [0x4c, 0x89, 0xf2, 0x48, 0xc1, 0xea, 6,
   0x49, 0xbc, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
   0x4d, 0x21, 0xf4, 0x41, 0x83, 0xe6, 0x3f, 0x4d, 0x01, 0xfc,
   0x48, 0x01, 0x94, 0x24, 0xd8, 0, 0, 0, 0x48, 0x89, 0xc7, 0x4c, 0x89, 0xfe]

private theorem narrowLength (len : BitVec 64) :
    ((len.setWidth 32 &&& 63).setWidth 64) = len &&& 63 := by
  change ((len.setWidth 32 &&& (63 : BitVec 64).setWidth 32).setWidth 64) = len &&& 63
  rw [← BitVec.setWidth_and, BitVec.setWidth_setWidth_eq_self]
  change (len &&& 63).toNat < 2^32
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem prepareBulk [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10fc84)
    (outside : ¬ InProgram boundary.rip)
    (writable : MemWritable s (stackPtr s + 216) 8)
    (apart : RangeApart (stackPtr s + 216) 8 0x10fc9f 14) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ t.RIP = 0x10fcad ∧
      t.regValue .rdi = s.regValue .rax ∧ t.regValue .rsi = s.regValue .r15 ∧
      t.regValue .rdx = s.regValue .r14 >>> 6 ∧
      t.regValue .r14 = s.regValue .r14 &&& 63 ∧
      t.regValue .r12 = s.regValue .r15 + (s.regValue .r14 &&& 0x7fffffffffffffc0) ∧
      memLoad t.external (stackPtr s + 216) 64 =
        memLoad s.external (stackPtr s + 216) 64 + t.regValue .rdx ∧
      AgreesExcept [.reg 2, .reg 12, .reg 14, .reg 7, .reg 6, .flags, .rip,
        .mem (stackPtr s + 216) 8] s t := by
  have code : CodeIn (codeRange 0x10fc84 bulkPrepareBytes) s :=
    programText_slice (programLoaded_codeIn loaded) 0xfc84 bulkPrepareBytes (by decide)
      (by decide +kernel)
  have next (offset : Nat) (bound : offset < 115149) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x10fc84 0x4c 0xf2 (by simp [RexWPrefix]) rfl).advances ready
      (code.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 0 3)) rip
      (next 0xfc87 (by decide))
  have a1 : AgreesExcept [.reg 2, .rip] s s1 := e1.agrees
  have c1 := a1.codeIn (by simp [Component.Covers]) code
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (shr_r64_imm8_effect_step 0x10fc87 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl).advances ready1
      (c1.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 3 4)) e1.rip
      (next 0xfc8b (by decide))
  have a2 : AgreesExcept [.reg 2, .flags, .rip] s1 s2 := e2.agrees
  have c2 := a2.codeIn (by simp [Component.Covers]) c1
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_r64_imm64_effect_step 0x10fc8b 0x49 0xbc (by simp [RexWPrefix]) (by decide)
      0x7fffffffffffffc0).advances ready2
        (c2.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 7 10)) e2.rip
        (next 0xfc95 (by decide))
  have a3 : AgreesExcept [.reg 12, .rip] s2 s3 := e3.agrees
  have c3 := a3.codeIn (by simp [Component.Covers]) c2
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (and_r64_r64_effect_step 0x10fc95 0x4d 0xf4 (by simp [RexWPrefix]) rfl).advances ready3
      (c3.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 17 3)) e3.rip
      (next 0xfc98 (by decide))
  have a4 : AgreesExcept [.reg 12, .flags, .rip] s3 s4 := e4.agrees
  have c4 := a4.codeIn (by simp [Component.Covers]) c3
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (and_r32_imm8_rex_effect_step 0x10fc98 0x41 0xe6 0x3f
      (by simp [RexNoWPrefix]) rfl rfl).advances ready4
        (c4.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 20 4)) e4.rip
        (next 0xfc9c (by decide))
  have a5 : AgreesExcept [.reg 14, .flags, .rip] s4 s5 := e5.agrees
  have c5 := a5.codeIn (by simp [Component.Covers]) c4
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (add_r64_r64_effect_step 0x10fc9c 0x4d 0xfc (by simp [RexWPrefix]) rfl).advances ready5
      (c5.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 24 3)) e5.rip
      (next 0xfc9f (by decide))
  have a6 : AgreesExcept [.reg 12, .flags, .rip] s5 s6 := e6.agrees
  have c6 := a6.codeIn (by simp [Component.Covers]) c5
  have registerFrame := ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6
  have memory := registerFrame.external (by simp [Component.Covers])
  have rsp : stackPtr s6 = stackPtr s := registerFrame.read (n := 64) (r := 4) (by decide)
  have addr : (AddrMode.sib 4 none 0 (.d32 216)).addr s6 0x10fca7 = stackPtr s + 216 := by
    change stackPtr s6 + 216 = _
    rw [rsp]
  have storePre : RmwPre 0x10fc9f (.sib 4 none 0 (.d32 216)) 8 8 s6 := by
    refine ⟨e6.rip, ?_, ?_⟩
    · change MemWritable s6 ((AddrMode.sib 4 none 0 (.d32 216)).addr s6 0x10fca7) 8
      rw [addr]
      exact writable.of_external_eq memory
    · change RangeApart ((AddrMode.sib 4 none 0 (.d32 216)).addr s6 0x10fca7) 8 0x10fc9f 8
      rw [addr]
      exact fun i hi j hj => apart i hi j (by omega)
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (add_m64_r64_effect_step 0x10fc9f 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl).advances ready6
        (c6.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 27 8)) storePre
        (next 0xfca7 (by decide))
  have a7 : AgreesExcept [.mem (stackPtr s + 216) 8, .flags, .rip] s6 s7 := by
    have frame : AgreesExcept [.mem ((AddrMode.sib 4 none 0 (.d32 216)).addr s6 0x10fca7) 8,
      .flags, .rip] s6 s7 := by
      simpa only [addMREffect_components, Nat.reduceDiv,
        show 3 + (AddrMode.sib 4 none 0 (.d32 216)).tail.length = 8 from rfl,
        show (0x10fc9f : BitVec 64) + BitVec.ofNat 64 8 = 0x10fca7 from rfl] using e7.agrees
    rwa [addr] at frame
  let argumentBytes := bulkPrepareBytes.drop 35
  have c7 : CodeIn (codeRange 0x10fca7 argumentBytes) s7 := by
    apply CodeIn.of_agreesExcept a7 _ (c6.mono (codeRange_slice_subset 0x10fc84 bulkPrepareBytes 35 6))
    intro x hx c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨i, hi, address⟩ := covered
      obtain ⟨j, hj, codeAddress⟩ := exists_of_mem_codeRange hx
      apply apart i hi (8 + j) (by change j < 6 at hj; omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact address.symm.trans codeAddress
    · exact covered.elim
    · exact covered.elim
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x10fca7 0x48 0xc7 (by simp [RexWPrefix]) rfl).advances ready7
      (c7.mono (codeRange_slice_subset 0x10fca7 argumentBytes 0 3))
      e7.rip (next 0xfcaa (by decide))
  have a8 : AgreesExcept [.reg 7, .rip] s7 s8 := e8.agrees
  have c8 := a8.codeIn (by simp [Component.Covers]) c7
  obtain ⟨t, run9, ready9, e9⟩ :=
    (mov_r64_r64_effect_step 0x10fcaa 0x4c 0xfe (by simp [RexWPrefix]) rfl).advances ready8
      (c8.mono (codeRange_slice_subset 0x10fca7 argumentBytes 3 3))
      e8.rip (next 0xfcad (by decide))
  have a9 : AgreesExcept [.reg 6, .rip] s8 t := e9.agrees
  have suffix := (a7.trans a8).trans a9
  have beforeMask := ((a1.trans a2).trans a3).trans a4
  have rdx6 : s6.regValue .rdx = s.regValue .r14 >>> 6 := by
    have same : s6.regValue .rdx = s2.regValue .rdx :=
      (((a3.trans a4).trans a5).trans a6).read (n := 64) (r := 2) (by decide)
    have shift : s2.regValue .rdx = s1.regValue .rdx >>> 6 := e2.writes
    have copy : s1.regValue .rdx = s.regValue .r14 := e1.writes
    rw [same, shift, copy]
  have rdx : t.regValue .rdx = s6.regValue .rdx := suffix.read (n := 64) (r := 2) (by simp)
  have run := run1.trans <| run2.trans <| run3.trans <| run4.trans <| run5.trans <|
    run6.trans <| run7.trans <| run8.trans run9
  refine ⟨t, run, ready9, e9.rip, ?_, ?_, rdx.trans rdx6, ?_, ?_, ?_, ?_⟩
  · have dest : s8.regValue .rdi = s7.regValue .rax := e8.writes
    exact (a9.read (n := 64) (r := 7) (by decide)).trans (dest.trans
      ((registerFrame.trans a7).read (n := 64) (r := 0) (by simp)))
  · have src : t.regValue .rsi = s8.regValue .r15 := e9.writes
    exact src.trans (((registerFrame.trans a7).trans a8).read (n := 64) (r := 15) (by simp))
  · have mask : s5.regValue .r14 = ((s4.regValue .r14).setWidth 32 &&& 63).setWidth 64 := e5.writes
    have len : s4.regValue .r14 = s.regValue .r14 := beforeMask.read (n := 64) (r := 14) (by decide)
    have keep : t.regValue .r14 = s5.regValue .r14 :=
      (a6.trans suffix).read (n := 64) (r := 14) (by simp)
    rw [keep, mask, len, narrowLength]
  · have mask : s4.regValue .r12 = s3.regValue .r12 &&& s3.regValue .r14 := e4.writes
    have imm : s3.regValue .r12 = 0x7fffffffffffffc0 := e3.writes
    have len : s3.regValue .r14 = s.regValue .r14 :=
      ((a1.trans a2).trans a3).read (n := 64) (r := 14) (by decide)
    have ptr : s5.regValue .r15 = s.regValue .r15 :=
      (beforeMask.trans a5).read (n := 64) (r := 15) (by decide)
    have keep : s5.regValue .r12 = s4.regValue .r12 := a5.read (n := 64) (r := 12) (by decide)
    have add : s6.regValue .r12 = s5.regValue .r12 + s5.regValue .r15 := e6.writes
    have tail : t.regValue .r12 = s6.regValue .r12 := suffix.read (n := 64) (r := 12) (by simp)
    rw [tail, add, ptr, keep, mask, imm, len, BitVec.and_comm 0x7fffffffffffffc0, BitVec.add_comm]
  · let slot := (AddrMode.sib 4 none 0 (.d32 216)).addr s6 0x10fca7
    have value : memLoad s7.external slot 64 = memLoad s6.external slot 64 + s6.regValue .rdx := e7.writes
    rw [show slot = stackPtr s + 216 from addr, memory] at value
    rw [(a8.trans a9).external (by simp [Component.Covers]), rdx]
    exact value
  · exact (registerFrame.trans suffix).mono (by simp)

end Hkdf.Proofs.NewExpand.Extract.Update
