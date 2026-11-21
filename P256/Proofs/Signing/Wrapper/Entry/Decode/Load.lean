import P256.Proofs.Signing.Wrapper.Entry.Decode.Block

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

abbrev LoadBlockPre := BlockPre 0x10246e [(0,8),(8,8),(16,8),(24,8)] [(328,8),(320,8),(312,8)]

def loadBytes : List UInt8 :=
  [76, 137, 188, 36, 72, 1, 0, 0, 76, 137, 180, 36, 64, 1, 0, 0, 72, 137, 156, 36, 56, 1, 0, 0, 72, 139, 44, 36, 76, 139, 116, 36, 8, 72, 139, 92, 36, 16, 76, 139, 124, 36, 24]

def loadEffect (s : RamState) : Effect :=
  { rip := 0x102499
    writes := [⟨(.mem (stackPtr s + 328) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 320) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 312) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 5 : Operand 64), memLoad s.external (stackPtr s + 0) 64⟩,
      ⟨(.reg 14 : Operand 64), memLoad s.external (stackPtr s + 8) 64⟩,
      ⟨(.reg 3 : Operand 64), memLoad s.external (stackPtr s + 16) 64⟩,
      ⟨(.reg 15 : Operand 64), memLoad s.external (stackPtr s + 24) 64⟩] }

theorem load_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadBlockPre (codeRange 0x10246e loadBytes)
      (Effect.post loadEffect) := by
  advance_begin (CrossPageStore.mov_m64_r64_effect_step_any 0x10246e 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.writable (328,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.codeApart (328,8) (by simp) 0x246e 8 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.codeApart (328,8) (by simp) 0x246e 43 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x2476 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102476 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10246e loadBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (320,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (320,8) (by simp) 0x2476 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (320,8) (by simp) 0x246e 43 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x247e (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10247e 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10246e loadBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (312,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (312,8) (by simp) 0x247e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (312,8) (by simp) 0x246e 43 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2486 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102486 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10246e loadBytes 24 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (0,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x248a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10248a 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10246e loadBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (8,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x248f (by decide))
  advance_then (mov_r64_m64_effect_step 0x10248f 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10246e loadBytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (16,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2494 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102494 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10246e loadBytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (24,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2499 (by decide))
  have read0_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+328) v) (sp+0) 64 =
        memLoad m (sp+0) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+320) v) (sp+0) 64 =
        memLoad m (sp+0) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+312) v) (sp+0) 64 =
        memLoad m (sp+0) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+328) v) (sp+8) 64 =
        memLoad m (sp+8) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+320) v) (sp+8) 64 =
        memLoad m (sp+8) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+312) v) (sp+8) 64 =
        memLoad m (sp+8) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+328) v) (sp+16) 64 =
        memLoad m (sp+16) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+320) v) (sp+16) 64 =
        memLoad m (sp+16) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+312) v) (sp+16) 64 =
        memLoad m (sp+16) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+328) v) (sp+24) 64 =
        memLoad m (sp+24) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+320) v) (sp+24) 64 =
        memLoad m (sp+24) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+312) v) (sp+24) 64 =
        memLoad m (sp+24) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have reg0 : gprNumber (0#1) (rexR (UInt8.toBitVec 76)) 7 = 15#5 := by decide +kernel
  have reg1 : gprNumber (0#1) (rexR (UInt8.toBitVec 76)) 6 = 14#5 := by decide +kernel
  have reg2 : gprNumber (0#1) (rexR (UInt8.toBitVec 72)) 3 = 3#5 := by decide +kernel
  have reg3 : gprNumber (0#1) (rexR (UInt8.toBitVec 72)) 5 = 5#5 := by decide +kernel
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,loadEffect,stackPtr,BitVec.add_zero ,read0_0,read0_1,read0_2,read1_0,read1_1,read1_2,read2_0,read2_1,read2_2,read3_0,read3_1,read3_2,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,loadEffect,stackPtr,BitVec.add_zero ,read0_0,read0_1,read0_2,read1_0,read1_1,read1_2,read2_0,read2_1,read2_2,read3_0,read3_1,read3_2,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
    exact ⟨rfl,rfl,rfl⟩
  · intro i
    cases i <;> x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,loadEffect,stackPtr,BitVec.add_zero ,read0_0,read0_1,read0_2,read1_0,read1_1,read1_2,read2_0,read2_1,read2_2,read3_0,read3_1,read3_2,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,loadEffect,stackPtr,BitVec.add_zero ,read0_0,read0_1,read0_2,read1_0,read1_1,read1_2,read2_0,read2_1,read2_2,read3_0,read3_1,read3_2,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]


end P256.Proofs.Signing.Wrapper.Entry.Decode
