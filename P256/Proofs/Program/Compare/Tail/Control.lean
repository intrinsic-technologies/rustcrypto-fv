import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem program_block [Bindings] {pre : RamState → Prop} {code : CodeMap}
    {effect : RamState → Effect} (h : RegisterBlock pre code effect)
    (hCode : ∀ s, CodeIn Extracted.programSections.toCodeMap s → CodeIn code s)
    (hNoMem : ∀ s, pre s → ∀ c ∈ (effect s).components, ∀ x, ¬ c.Covers x) :
    RegisterBlock pre Extracted.programSections.toCodeMap effect := by
  intro boundary s hReady hProgram hPre hBoundary
  obtain ⟨fuel, t, hRun, hReady', _, hEffect, hStack⟩ :=
    h boundary s hReady (hCode s hProgram) hPre hBoundary
  exact ⟨fuel, t, hRun, hReady',
    hEffect.codeIn (Effect.Avoids.of_noMem (hNoMem s hPre) _) hProgram, hEffect, hStack⟩

theorem branch8 [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8)
    (hNext : InRoutine (p + 2))
    (hTarget : InRoutine (branchTarget p 2 (disp.signExtend 64))) :
    RegisterBlock (fun s ↦ s.RIP = p) (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (jccEffect p 2 cc (disp.signExtend 64)) := by
  apply RegisterBlock.first (jcc_rel8_effect_step p cc disp) (fun _ h ↦ h)
  · intro s h
    refine ⟨h, fun _ ↦ ?_⟩
    have := hTarget.2
    omega
  · intro s _
    exact branchEffect_avoids _ _ _ _
  · intro s _
    simp [jccEffect]
  · intro s _
    change InRoutine (if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)
      then branchTarget p 2 (disp.signExtend 64) else p + 2)
    split <;> assumption

theorem branch32 [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 32)
    (hNext : InRoutine (p + 6))
    (hTarget : InRoutine (branchTarget p 6 (disp.signExtend 64))) :
    RegisterBlock (fun s ↦ s.RIP = p)
      (codeRange p (0x0f :: jccOpcode32 cc :: immBytes 32 disp))
      (jccEffect p 6 cc (disp.signExtend 64)) := by
  apply RegisterBlock.first (jcc_rel32_effect_step p cc disp) (fun _ h ↦ h)
  · intro s h
    refine ⟨h, fun _ ↦ ?_⟩
    have := hTarget.2
    omega
  · intro s _
    exact branchEffect_avoids _ _ _ _
  · intro s _
    simp [jccEffect]
  · intro s _
    change InRoutine (if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)
      then branchTarget p 6 (disp.signExtend 64) else p + 6)
    split <;> assumption

private theorem nopEffect_local (p : BitVec 64) (len : Nat) :
    Effect.Local (fun _ : RamState ↦ nopEffect p len) :=
  AdvancesTriple.const_local (by simp [nopEffect])

attribute [local x86_local] nopEffect_local
attribute [local x86_compose] nopEffect BitVec.shiftLeft_zero BitVec.add_zero

def eightStartBytes : List UInt8 :=
  [0x4e, 0x8d, 0x14, 0x0a, 0x45, 0x31, 0xdb, 0x66, 0x0f, 0x1f, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

def eightStartEffect (s : RamState) : Effect :=
  { rip := 0x11cd50
    writes := [⟨(Operand.reg 10 : Operand 64),
      (Operand.reg 2 : Operand 64).read s + (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(Operand.reg 11 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

set_option maxRecDepth 2048 in
theorem eight_start [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd40) (codeRange 0x11cd40 eightStartBytes)
      eightStartEffect := by
  unfold eightStartBytes
  p256_memcmp_run_begin lea_r64_effect_step 0x11cd40 0x4e
    (by unfold RexWPrefix; decide) 2 (.sib 2 (some 9) 0 .none)
    (by decide) (by decide) (by decide)
  p256_memcmp_run_then xor_r32_r32_rex_effect_step 0x11cd44 0x45 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd40) (all := eightStartBytes) 4 (by decide +kernel)
  p256_memcmp_run_then nop_m_effect_step 0x11cd47 [0x66]
    (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd40) (all := eightStartBytes) 7 (by decide +kernel)
  try (case mid =>
    intro s t hP hH _
    exact ⟨hH.rip, nopEffect_avoids _ _ _⟩)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [eightStartEffect]
  · x86_norm [eightStartEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [eightStartEffect]
    all_goals simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · x86_norm [eightStartEffect]

def fourStartBytes : List UInt8 :=
  [0x4e, 0x8d, 0x14, 0x0a, 0x45, 0x31, 0xdb, 0x66, 0x0f, 0x1f, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

def fourStartEffect (s : RamState) : Effect :=
  { rip := 0x11cd90
    writes := [⟨(Operand.reg 10 : Operand 64),
      (Operand.reg 2 : Operand 64).read s + (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(Operand.reg 11 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

set_option maxRecDepth 2048 in
theorem four_start [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd80) (codeRange 0x11cd80 fourStartBytes)
      fourStartEffect := by
  unfold fourStartBytes
  p256_memcmp_run_begin lea_r64_effect_step 0x11cd80 0x4e
    (by unfold RexWPrefix; decide) 2 (.sib 2 (some 9) 0 .none)
    (by decide) (by decide) (by decide)
  p256_memcmp_run_then xor_r32_r32_rex_effect_step 0x11cd84 0x45 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd80) (all := fourStartBytes) 4 (by decide +kernel)
  p256_memcmp_run_then nop_m_effect_step 0x11cd87 [0x66]
    (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd80) (all := fourStartBytes) 7 (by decide +kernel)
  try (case mid =>
    intro s t hP hH _
    exact ⟨hH.rip, nopEffect_avoids _ _ _⟩)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [fourStartEffect]
  · x86_norm [fourStartEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [fourStartEffect]
    all_goals simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · x86_norm [fourStartEffect]

def eightAdvanceEffect (s : RamState) : Effect :=
  { rip := 0x11cd68
    writes := [⟨(Operand.reg 11 : Operand 64), (Operand.reg 11 : Operand 64).read s + 8⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 9 : Operand 64).read s)
      ((Operand.reg 11 : Operand 64).read s + 8))) }

theorem eight_advance [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd61)
      (codeRange 0x11cd61 [0x49, 0x83, 0xc3, 8, 0x4d, 0x39, 0xd9]) eightAdvanceEffect := by
  p256_memcmp_run_begin add_r64_imm8_effect_step 0x11cd61 0x49 0xc3 8
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  p256_memcmp_run_then cmp_r64_r64_effect_step 0x11cd65 0x4d 0xd9
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd61)
      (all := [0x49, 0x83, 0xc3, 8, 0x4d, 0x39, 0xd9]) 4 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [eightAdvanceEffect]
  · x86_norm [eightAdvanceEffect]
    simp [Operand.read, gprNumber, rexB, modrmRm]
  · intro i; cases i <;> x86_norm [eightAdvanceEffect]
    all_goals simp [Operand.read, gprNumber, rexB, modrmRm]
  · x86_norm [eightAdvanceEffect]

def fourAdvanceEffect (s : RamState) : Effect :=
  { rip := 0x11cda7
    writes := [⟨(Operand.reg 11 : Operand 64), (Operand.reg 11 : Operand 64).read s + 4⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 9 : Operand 64).read s)
      ((Operand.reg 11 : Operand 64).read s + 4))) }

theorem four_advance [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cda0)
      (codeRange 0x11cda0 [0x49, 0x83, 0xc3, 4, 0x4d, 0x39, 0xd9]) fourAdvanceEffect := by
  p256_memcmp_run_begin add_r64_imm8_effect_step 0x11cda0 0x49 0xc3 4
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  p256_memcmp_run_then cmp_r64_r64_effect_step 0x11cda4 0x4d 0xd9
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cda0)
      (all := [0x49, 0x83, 0xc3, 4, 0x4d, 0x39, 0xd9]) 4 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [fourAdvanceEffect]
  · x86_norm [fourAdvanceEffect]
    simp [Operand.read, gprNumber, rexB, modrmRm]
  · intro i; cases i <;> x86_norm [fourAdvanceEffect]
    all_goals simp [Operand.read, gprNumber, rexB, modrmRm]
  · x86_norm [fourAdvanceEffect]

def twoAdvanceEffect (s : RamState) : Effect :=
  { rip := 0x11cdeb
    writes := [⟨(Operand.reg 11 : Operand 64), (Operand.reg 11 : Operand 64).read s + 2⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 9 : Operand 64).read s)
      ((Operand.reg 11 : Operand 64).read s + 2))) }

theorem two_advance [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cde4)
      (codeRange 0x11cde4 [0x49, 0x83, 0xc3, 2, 0x4d, 0x39, 0xd9]) twoAdvanceEffect := by
  p256_memcmp_run_begin add_r64_imm8_effect_step 0x11cde4 0x49 0xc3 2
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  p256_memcmp_run_then cmp_r64_r64_effect_step 0x11cde8 0x4d 0xd9
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cde4)
      (all := [0x49, 0x83, 0xc3, 2, 0x4d, 0x39, 0xd9]) 4 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [twoAdvanceEffect]
  · x86_norm [twoAdvanceEffect]
    simp [Operand.read, gprNumber, rexB, modrmRm]
  · intro i; cases i <;> x86_norm [twoAdvanceEffect]
    all_goals simp [Operand.read, gprNumber, rexB, modrmRm]
  · x86_norm [twoAdvanceEffect]

def eightFinishEffect (s : RamState) : Effect :=
  { rip := 0x11cd70
    writes := [⟨(Operand.reg 2 : Operand 64), (Operand.reg 10 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 8 : Operand 64).read s⟩] }

theorem eight_finish [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd6a)
      (codeRange 0x11cd6a [0x4c, 0x89, 0xd2, 0x4c, 0x89, 0xc6]) eightFinishEffect := by
  p256_memcmp_run_begin mov_r64_r64_effect_step 0x11cd6a 0x4c 0xd2
    (by unfold RexWPrefix; decide) (by decide)
  p256_memcmp_run_then mov_r64_r64_effect_step 0x11cd6d 0x4c 0xc6
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd6a)
      (all := [0x4c, 0x89, 0xd2, 0x4c, 0x89, 0xc6]) 3 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [eightFinishEffect]
  · x86_norm [eightFinishEffect]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [eightFinishEffect]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [eightFinishEffect]

def fourFinishEffect (s : RamState) : Effect :=
  { rip := 0x11cdaf
    writes := [⟨(Operand.reg 2 : Operand 64), (Operand.reg 10 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 0 : Operand 64).read s⟩] }

theorem four_finish [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cda9)
      (codeRange 0x11cda9 [0x4c, 0x89, 0xd2, 0x48, 0x89, 0xc6]) fourFinishEffect := by
  p256_memcmp_run_begin mov_r64_r64_effect_step 0x11cda9 0x4c 0xd2
    (by unfold RexWPrefix; decide) (by decide)
  p256_memcmp_run_then mov_r64_r64_effect_step 0x11cdac 0x48 0xc6
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cda9)
      (all := [0x4c, 0x89, 0xd2, 0x48, 0x89, 0xc6]) 3 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [fourFinishEffect]
  · x86_norm [fourFinishEffect]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fourFinishEffect]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [fourFinishEffect]

def twoStartBytes : List UInt8 :=
  [0x4c, 0x01, 0xce, 0x4e, 0x8d, 0x14, 0x0a, 0x45, 0x31, 0xdb,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

def twoStartEffect (s : RamState) : Effect :=
  { rip := 0x11cdd0
    writes := [⟨(Operand.reg 6 : Operand 64),
      (Operand.reg 6 : Operand 64).read s + (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(Operand.reg 10 : Operand 64),
      (Operand.reg 2 : Operand 64).read s + (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(Operand.reg 11 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

set_option maxRecDepth 2048 in
theorem two_start [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cdb8) (codeRange 0x11cdb8 twoStartBytes)
      twoStartEffect := by
  unfold twoStartBytes
  p256_memcmp_run_begin add_r64_r64_effect_step 0x11cdb8 0x4c 0xce
    (by unfold RexWPrefix; decide) (by decide)
  p256_memcmp_run_then lea_r64_effect_step 0x11cdbb 0x4e
    (by unfold RexWPrefix; decide) 2 (.sib 2 (some 9) 0 .none)
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdb8) (all := twoStartBytes) 3 (by decide +kernel)
  p256_memcmp_run_then xor_r32_r32_rex_effect_step 0x11cdbf 0x45 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdb8) (all := twoStartBytes) 7 (by decide +kernel)
  p256_memcmp_run_then nop_m_effect_step 0x11cdc2 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2e]
    (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdb8) (all := twoStartBytes) 10 (by decide +kernel)
  try (case mid =>
    intro s t hP hH _
    exact ⟨hH.rip, nopEffect_avoids _ _ _⟩)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [twoStartEffect]
  · x86_norm [twoStartEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [twoStartEffect]
    all_goals simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · x86_norm [twoStartEffect]

def twoFinishEffect (s : RamState) : Effect :=
  { rip := 0x11cdf0
    writes := [⟨(Operand.reg 2 : Operand 64), (Operand.reg 10 : Operand 64).read s⟩] }

theorem two_finish [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cded)
      (codeRange 0x11cded [0x4c, 0x89, 0xd2]) twoFinishEffect := by
  p256_memcmp_run_begin mov_r64_r64_effect_step 0x11cded 0x4c 0xd2
    (by unfold RexWPrefix; decide) (by decide)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [twoFinishEffect]
  · x86_norm [twoFinishEffect]
    rfl
  · intro i; cases i <;> x86_norm [twoFinishEffect]
  · x86_norm [twoFinishEffect]

end P256.Proofs.Program.Compare.Tail
