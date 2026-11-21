import P256.Proofs.Signing.Wrapper.Entry.Decode.Block

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

abbrev OutputPre := BlockPre 0x1025eb [(304,8),(296,8),(280,8),(288,8)] [(24,8),(16,8),(8,8),(0,8),(200,8),(192,8),(184,8),(176,8)]

def outputBytes : List UInt8 :=
  [72, 139, 132, 36, 48, 1, 0, 0, 72, 137, 68, 36, 24, 72, 139, 140, 36, 40, 1, 0, 0, 72, 137, 76, 36, 16, 72, 139, 148, 36, 24, 1, 0, 0, 72, 139, 180, 36, 32, 1, 0, 0, 72, 137, 116, 36, 8, 72, 137, 20, 36, 72, 137, 132, 36, 200, 0, 0, 0, 72, 137, 140, 36, 192, 0, 0, 0, 72, 137, 180, 36, 184, 0, 0, 0, 72, 137, 148, 36, 176, 0, 0, 0]

def outputEffect (s : RamState) : Effect :=
  { rip := 0x10263e
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 304) 64⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), memLoad s.external (stackPtr s + 304) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 296) 64⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), memLoad s.external (stackPtr s + 296) 64⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩,
      ⟨(.reg 6 : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩,
      ⟨(.mem (stackPtr s + 0) : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩,
      ⟨(.mem (stackPtr s + 200) : Operand 64), memLoad s.external (stackPtr s + 304) 64⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), memLoad s.external (stackPtr s + 296) 64⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩] }

theorem output_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputPre (codeRange 0x1025eb outputBytes)
      (Effect.post outputEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1025eb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip,?_⟩
    x86_norm [stackPtr]
    simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.readable (304,8) (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x25f3 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1025f3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (24,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (24,8) (by simp) 0x25f3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (24,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25f8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1025f8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (296,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2600 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102600 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (16,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (16,8) (by simp) 0x2600 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (16,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2605 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102605 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (280,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x260d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10260d 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.readable (288,8) (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2615 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102615 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (8,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (8,8) (by simp) 0x2615 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (8,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x261a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10261a 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 47 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (0,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (0,8) (by simp) 0x261a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (0,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x261e (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10261e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 51 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (200,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (200,8) (by simp) 0x261e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (200,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2626 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102626 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 59 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (192,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (192,8) (by simp) 0x2626 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (192,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x262e (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10262e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (184,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (184,8) (by simp) 0x262e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (184,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2636 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102636 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1025eb outputBytes 75 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (176,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (176,8) (by simp) 0x2636 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (176,8) (by simp) 0x25eb 83 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x263e (by decide))
  have read0_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+24) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+16) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+8) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_3 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+0) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_4 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+200) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_5 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+192) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_6 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+184) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read0_7 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+176) v) (sp+304) 64 =
        memLoad m (sp+304) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+24) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+16) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+8) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_3 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+0) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_4 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+200) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_5 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+192) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_6 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+184) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read1_7 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+176) v) (sp+296) 64 =
        memLoad m (sp+296) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+24) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+16) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+8) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_3 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+0) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_4 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+200) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_5 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+192) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_6 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+184) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read2_7 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+176) v) (sp+280) 64 =
        memLoad m (sp+280) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_0 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+24) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_1 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+16) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_2 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+8) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_3 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+0) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_4 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+200) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_5 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+192) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_6 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+184) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  have read3_7 (m : Ram) (sp : BitVec 64) (v : BitVec 64) :
      memLoad (memStore m (sp+176) v) (sp+288) 64 =
        memLoad m (sp+288) 64 := by
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) sp hi hj (by decide) he
  advance_finish [outputEffect,stackPtr,Operand.read_reg64,State.regValue,BitVec.add_zero ,read0_0,read0_1,read0_2,read0_3,read0_4,read0_5,read0_6,read0_7,read1_0,read1_1,read1_2,read1_3,read1_4,read1_5,read1_6,read1_7,read2_0,read2_1,read2_2,read2_3,read2_4,read2_5,read2_6,read2_7,read3_0,read3_1,read3_2,read3_3,read3_4,read3_5,read3_6,read3_7]
  all_goals (repeat constructor <;> rfl)

end P256.Proofs.Signing.Wrapper.Entry.Decode
