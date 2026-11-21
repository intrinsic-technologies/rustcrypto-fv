import P256.Proofs.Program.Compare.Mismatch.Support

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs

def unknownFlags : StatusFlagsOutcome := ⟨none, none, none, none, none, none⟩

private theorem shr32_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    Effect.Local (shrR32Effect p len dst c) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · simp only [shrR32Effect, h.read_reg]
  · intro s t h i hi
    cases i <;> simp_all [shrR32Effect, Effect.flag, shrFlags,
      StatusFlagsOutcome.get, StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg] <;> split <;> simp_all
  · intro s
    simp [shrR32Effect, Write.Full, Operand.Full]

private theorem movzxReg_local (p : BitVec 64) (len width : Nat) (dst src : BitVec 5) :
    Effect.Local (movzxR32RegEffect p len width dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ h ↦ congrArg some h, ?_⟩
  · simp only [movzxR32RegEffect, h.read_reg]
  · intro s
    simp [movzxR32RegEffect, Write.Full, Operand.Full]

private theorem sub32_local (p : BitVec 64) (len : Nat) (dst src : BitVec 5) :
    Effect.Local (subR32R32Effect p len dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun s t h i _ ↦ ?_, ?_⟩
  · simp only [subR32R32Effect, h.read_reg]
  · simp only [subR32R32Effect, Effect.flag, h.read_reg]
  · intro s
    simp [subR32R32Effect, Write.Full, Operand.Full]

attribute [local x86_local] shr32_local movzxReg_local sub32_local
attribute [local x86_compose] shrR32Effect movzxR32RegEffect subR32R32Effect unknownFlags

macro "mismatch_finish " effect:Lean.Parser.Tactic.simpLemma : tactic => `(tactic| (
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [$effect]
  · x86_norm [$effect]
    all_goals simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm, shiftCount]
  · intro i; cases i <;> x86_norm [$effect]
  · x86_norm [$effect]))

def selectSecondBytes : List UInt8 :=
  [0x48, 0x89, 0xd8, 0x4c, 0x89, 0xf7]

def selectSecondEffect (s : RamState) : Effect :=
  { rip := 0x11c8e0
    writes := [⟨(Operand.reg 0 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

set_option maxRecDepth 2048 in
theorem select_second_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c8da) (codeRange 0x11c8da selectSecondBytes)
      selectSecondEffect := by
  unfold selectSecondBytes
  p256_memcmp_run_begin mov_r64_r64_effect_step 0x11c8da 0x48 0xd8
    (by unfold RexWPrefix; decide) (by decide)
  p256_memcmp_run_then mov_r64_r64_effect_step 0x11c8dd 0x4c 0xf7
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c8da) (all := selectSecondBytes) 3
      (by decide +kernel)
  mismatch_finish selectSecondEffect

def mainHigh32Bytes : List UInt8 :=
  [0x48, 0xc1, 0xef, 0x20, 0x48, 0xc1, 0xe8, 0x20]

def mainHigh32Effect (s : RamState) : Effect :=
  { rip := 0x11c8ec
    writes := [⟨(Operand.reg 7 : Operand 64), ((Operand.reg 7 : Operand 64).read s >>> 32)⟩,
      ⟨(Operand.reg 0 : Operand 64), ((Operand.reg 0 : Operand 64).read s >>> 32)⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem main_high32_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c8e4) (codeRange 0x11c8e4 mainHigh32Bytes)
      mainHigh32Effect := by
  unfold mainHigh32Bytes
  p256_memcmp_run_begin shr_r64_imm8_effect_step 0x11c8e4 0x48 0xef 32
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  p256_memcmp_run_then shr_r64_imm8_effect_step 0x11c8e8 0x48 0xe8 32
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c8e4) (all := mainHigh32Bytes) 4
      (by decide +kernel)
  mismatch_finish mainHigh32Effect

def tailHigh32Bytes : List UInt8 :=
  [0x48, 0xc1, 0xef, 0x20, 0x48, 0xc1, 0xe8, 0x20]

def tailHigh32Effect (s : RamState) : Effect :=
  { rip := 0x11ce1a
    writes := [⟨(Operand.reg 7 : Operand 64), ((Operand.reg 7 : Operand 64).read s >>> 32)⟩,
      ⟨(Operand.reg 0 : Operand 64), ((Operand.reg 0 : Operand 64).read s >>> 32)⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem tail_high32_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce12) (codeRange 0x11ce12 tailHigh32Bytes)
      tailHigh32Effect := by
  unfold tailHigh32Bytes
  p256_memcmp_run_begin shr_r64_imm8_effect_step 0x11ce12 0x48 0xef 32
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  p256_memcmp_run_then shr_r64_imm8_effect_step 0x11ce16 0x48 0xe8 32
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce12) (all := tailHigh32Bytes) 4
      (by decide +kernel)
  mismatch_finish tailHigh32Effect

def mainHigh16Bytes : List UInt8 :=
  [0xc1, 0xef, 0x10, 0xc1, 0xe8, 0x10]

def mainHigh16Effect (s : RamState) : Effect :=
  { rip := 0x11c8fc
    writes := [⟨(Operand.reg 7 : Operand 64), (((Operand.reg 7 : Operand 32).read s >>> 16)).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), (((Operand.reg 0 : Operand 32).read s >>> 16)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem main_high16_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c8f6) (codeRange 0x11c8f6 mainHigh16Bytes)
      mainHigh16Effect := by
  unfold mainHigh16Bytes
  p256_memcmp_run_begin shr_r32_imm8_effect_step 0x11c8f6 0xef 16
    (by decide) (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11c8f9 0xe8 16
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c8f6) (all := mainHigh16Bytes) 3
      (by decide +kernel)
  mismatch_finish mainHigh16Effect

def tailHigh16Bytes : List UInt8 :=
  [0xc1, 0xef, 0x10, 0xc1, 0xe8, 0x10]

def tailHigh16Effect (s : RamState) : Effect :=
  { rip := 0x11ce2a
    writes := [⟨(Operand.reg 7 : Operand 64), (((Operand.reg 7 : Operand 32).read s >>> 16)).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), (((Operand.reg 0 : Operand 32).read s >>> 16)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem tail_high16_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce24) (codeRange 0x11ce24 tailHigh16Bytes)
      tailHigh16Effect := by
  unfold tailHigh16Bytes
  p256_memcmp_run_begin shr_r32_imm8_effect_step 0x11ce24 0xef 16
    (by decide) (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce27 0xe8 16
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce24) (all := tailHigh16Bytes) 3
      (by decide +kernel)
  mismatch_finish tailHigh16Effect

def fourHigh16Bytes : List UInt8 :=
  [0xc1, 0xef, 0x10, 0xc1, 0xee, 0x10]

def fourHigh16Effect (s : RamState) : Effect :=
  { rip := 0x11ce58
    writes := [⟨(Operand.reg 7 : Operand 64), (((Operand.reg 7 : Operand 32).read s >>> 16)).setWidth 64⟩,
      ⟨(Operand.reg 6 : Operand 64), (((Operand.reg 6 : Operand 32).read s >>> 16)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem four_high16_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce52) (codeRange 0x11ce52 fourHigh16Bytes)
      fourHigh16Effect := by
  unfold fourHigh16Bytes
  p256_memcmp_run_begin shr_r32_imm8_effect_step 0x11ce52 0xef 16
    (by decide) (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce55 0xee 16
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce52) (all := fourHigh16Bytes) 3
      (by decide +kernel)
  mismatch_finish fourHigh16Effect

def mainHigh8Bytes : List UInt8 :=
  [0xf, 0xb7, 0xff, 0xc1, 0xef, 0x8, 0xf, 0xb7, 0xc0, 0xc1, 0xe8, 0x8]

def mainHigh8Effect (s : RamState) : Effect :=
  { rip := 0x11c911
    writes := [⟨(Operand.reg 7 : Operand 64), ((((Operand.reg 7 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), ((((Operand.reg 0 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem main_high8_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c905) (codeRange 0x11c905 mainHigh8Bytes)
      mainHigh8Effect := by
  unfold mainHigh8Bytes
  p256_memcmp_run_begin movzx_r32_r16_effect_step 0x11c905 0xff (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11c908 0xef 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c905) (all := mainHigh8Bytes) 3
      (by decide +kernel)
  p256_memcmp_run_then movzx_r32_r16_effect_step 0x11c90b 0xc0 (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c905) (all := mainHigh8Bytes) 6
      (by decide +kernel)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11c90e 0xe8 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c905) (all := mainHigh8Bytes) 9
      (by decide +kernel)
  mismatch_finish mainHigh8Effect

def tailHigh8Bytes : List UInt8 :=
  [0xf, 0xb7, 0xff, 0xc1, 0xef, 0x8, 0xf, 0xb7, 0xc0, 0xc1, 0xe8, 0x8]

def tailHigh8Effect (s : RamState) : Effect :=
  { rip := 0x11ce3f
    writes := [⟨(Operand.reg 7 : Operand 64), ((((Operand.reg 7 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), ((((Operand.reg 0 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem tail_high8_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce33) (codeRange 0x11ce33 tailHigh8Bytes)
      tailHigh8Effect := by
  unfold tailHigh8Bytes
  p256_memcmp_run_begin movzx_r32_r16_effect_step 0x11ce33 0xff (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce36 0xef 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce33) (all := tailHigh8Bytes) 3
      (by decide +kernel)
  p256_memcmp_run_then movzx_r32_r16_effect_step 0x11ce39 0xc0 (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce33) (all := tailHigh8Bytes) 6
      (by decide +kernel)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce3c 0xe8 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce33) (all := tailHigh8Bytes) 9
      (by decide +kernel)
  mismatch_finish tailHigh8Effect

def fourHigh8Bytes : List UInt8 :=
  [0xf, 0xb7, 0xff, 0xc1, 0xef, 0x8, 0xf, 0xb7, 0xf6, 0xc1, 0xee, 0x8]

def fourHigh8Effect (s : RamState) : Effect :=
  { rip := 0x11ce6d
    writes := [⟨(Operand.reg 7 : Operand 64), ((((Operand.reg 7 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩,
      ⟨(Operand.reg 6 : Operand 64), ((((Operand.reg 6 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem four_high8_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce61) (codeRange 0x11ce61 fourHigh8Bytes)
      fourHigh8Effect := by
  unfold fourHigh8Bytes
  p256_memcmp_run_begin movzx_r32_r16_effect_step 0x11ce61 0xff (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce64 0xef 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce61) (all := fourHigh8Bytes) 3
      (by decide +kernel)
  p256_memcmp_run_then movzx_r32_r16_effect_step 0x11ce67 0xf6 (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce61) (all := fourHigh8Bytes) 6
      (by decide +kernel)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce6a 0xee 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce61) (all := fourHigh8Bytes) 9
      (by decide +kernel)
  mismatch_finish fourHigh8Effect

def twoHigh8Bytes : List UInt8 :=
  [0xf, 0xb7, 0xff, 0xc1, 0xef, 0x8, 0x45, 0xf, 0xb7, 0xc0, 0x41, 0xc1, 0xe8, 0x8]

def twoHigh8Effect (s : RamState) : Effect :=
  { rip := 0x11ce8b
    writes := [⟨(Operand.reg 7 : Operand 64), ((((Operand.reg 7 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩,
      ⟨(Operand.reg 8 : Operand 64), ((((Operand.reg 8 : Operand 16).read s).setWidth 32 >>> 8)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem two_high8_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce7d) (codeRange 0x11ce7d twoHigh8Bytes)
      twoHigh8Effect := by
  unfold twoHigh8Bytes
  p256_memcmp_run_begin movzx_r32_r16_effect_step 0x11ce7d 0xff (by decide)
  p256_memcmp_run_then shr_r32_imm8_effect_step 0x11ce80 0xef 8
    (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce7d) (all := twoHigh8Bytes) 3
      (by decide +kernel)
  p256_memcmp_run_then movzx_r32_r16_rex_effect_step 0x11ce83 0x45 (by unfold RexNoWPrefix; decide) 0xc0 (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce7d) (all := twoHigh8Bytes) 6
      (by decide +kernel)
  p256_memcmp_run_then shr_r32_imm8_rex_effect_step 0x11ce87 0x41 0xe8 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce7d) (all := twoHigh8Bytes) 10
      (by decide +kernel)
  mismatch_finish twoHigh8Effect

def mainSubtractBytes : List UInt8 :=
  [0xf, 0xb6, 0xc0, 0x40, 0xf, 0xb6, 0xcf, 0x29, 0xc8]

def mainSubtractEffect (s : RamState) : Effect :=
  { rip := 0x11c923
    writes := [⟨(Operand.reg 0 : Operand 64), ((((Operand.reg 0 : Operand 8).read s).setWidth 32 - ((Operand.reg 7 : Operand 8).read s).setWidth 32)).setWidth 64⟩,
      ⟨(Operand.reg 1 : Operand 64), ((Operand.reg 7 : Operand 8).read s).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem main_subtract_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c91a) (codeRange 0x11c91a mainSubtractBytes)
      mainSubtractEffect := by
  unfold mainSubtractBytes
  p256_memcmp_run_begin movzx_r32_r8_effect_step 0x11c91a 0xc0 (by decide) (by decide)
  p256_memcmp_run_then movzx_r32_r8_rex_effect_step 0x11c91d 0x40 (by unfold RexNoWPrefix; decide) 0xcf (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c91a) (all := mainSubtractBytes) 3
      (by decide +kernel)
  p256_memcmp_run_then sub_r32_r32_effect_step 0x11c921 0xc8 (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c91a) (all := mainSubtractBytes) 7
      (by decide +kernel)
  mismatch_finish mainSubtractEffect

def tailBytesBytes : List UInt8 :=
  [0xf, 0xb6, 0xc0, 0x40, 0xf, 0xb6, 0xcf]

def tailBytesEffect (s : RamState) : Effect :=
  { rip := 0x11ce4b
    writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.reg 0 : Operand 8).read s).setWidth 64⟩,
      ⟨(Operand.reg 1 : Operand 64), ((Operand.reg 7 : Operand 8).read s).setWidth 64⟩] }

set_option maxRecDepth 2048 in
theorem tail_bytes_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce44) (codeRange 0x11ce44 tailBytesBytes)
      tailBytesEffect := by
  unfold tailBytesBytes
  p256_memcmp_run_begin movzx_r32_r8_effect_step 0x11ce44 0xc0 (by decide) (by decide)
  p256_memcmp_run_then movzx_r32_r8_rex_effect_step 0x11ce47 0x40 (by unfold RexNoWPrefix; decide) 0xcf (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce44) (all := tailBytesBytes) 3
      (by decide +kernel)
  mismatch_finish tailBytesEffect

def fourByteBytes : List UInt8 :=
  [0x40, 0xf, 0xb6, 0xc6]

def fourByteEffect (s : RamState) : Effect :=
  { rip := 0x11ce76
    writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.reg 6 : Operand 8).read s).setWidth 64⟩] }

set_option maxRecDepth 2048 in
theorem four_byte_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce72) (codeRange 0x11ce72 fourByteBytes)
      fourByteEffect := by
  unfold fourByteBytes
  p256_memcmp_run_begin movzx_r32_r8_rex_effect_step 0x11ce72 0x40 (by unfold RexNoWPrefix; decide) 0xc6 (by decide)
  mismatch_finish fourByteEffect

def twoByteBytes : List UInt8 :=
  [0x41, 0xf, 0xb6, 0xc0]

def twoByteEffect (s : RamState) : Effect :=
  { rip := 0x11ce98
    writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.reg 8 : Operand 8).read s).setWidth 64⟩] }

set_option maxRecDepth 2048 in
theorem two_byte_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce94) (codeRange 0x11ce94 twoByteBytes)
      twoByteEffect := by
  unfold twoByteBytes
  p256_memcmp_run_begin movzx_r32_r8_rex_effect_step 0x11ce94 0x41 (by unfold RexNoWPrefix; decide) 0xc0 (by decide)
  mismatch_finish twoByteEffect

def rightByteBytes : List UInt8 :=
  [0x40, 0xf, 0xb6, 0xcf]

def rightByteEffect (s : RamState) : Effect :=
  { rip := 0x11ce9c
    writes := [⟨(Operand.reg 1 : Operand 64), ((Operand.reg 7 : Operand 8).read s).setWidth 64⟩] }

set_option maxRecDepth 2048 in
theorem right_byte_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce98) (codeRange 0x11ce98 rightByteBytes)
      rightByteEffect := by
  unfold rightByteBytes
  p256_memcmp_run_begin movzx_r32_r8_rex_effect_step 0x11ce98 0x40 (by unfold RexNoWPrefix; decide) 0xcf (by decide)
  mismatch_finish rightByteEffect

def tailSubtractBytes : List UInt8 :=
  [0x29, 0xc8]

def tailSubtractEffect (s : RamState) : Effect :=
  { rip := 0x11ce9e
    writes := [⟨(Operand.reg 0 : Operand 64), (((Operand.reg 0 : Operand 32).read s - (Operand.reg 1 : Operand 32).read s)).setWidth 64⟩]
    flags := some unknownFlags }

set_option maxRecDepth 2048 in
theorem tail_subtract_block [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce9c) (codeRange 0x11ce9c tailSubtractBytes)
      tailSubtractEffect := by
  unfold tailSubtractBytes
  p256_memcmp_run_begin sub_r32_r32_effect_step 0x11ce9c 0xc8 (by decide)
  mismatch_finish tailSubtractEffect

end P256.Proofs.Program.Compare.Mismatch
