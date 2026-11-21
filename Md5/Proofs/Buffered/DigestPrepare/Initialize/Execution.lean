import Md5.Proofs.Buffered.DigestPrepare.Initialize.Pushes
import X86Proofs.Instructions.Lea.Triple

namespace Md5.Proofs.Buffered.DigestPrepare.Initialize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Streaming Block

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read BitVec.sub_eq_add_neg
  movM8Imm8Effect subR64Imm32Effect

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_local] movM8Imm8Effect_local

def initializeBytes : List UInt8 := [
    0x48, 0x81, 0xec, 0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0xd3, 0x49, 0x89, 0xf7, 0x48,
    0x89, 0xfe, 0x4c, 0x8d, 0xb4, 0x24, 0xf0, 0x00, 0x00, 0x00, 0x48, 0xb8, 0xfe, 0xdc,
    0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0x48, 0x89, 0x84, 0x24, 0xf8, 0x00, 0x00, 0x00,
    0x48, 0xb8, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x48, 0x89, 0x84, 0x24,
    0xf0, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0xc6, 0x84, 0x24, 0xef, 0x00, 0x00, 0x00, 0x00]

def initializeEffect (s : RamState) : Effect where
  rip := 0x100067
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 264⟩,
     ⟨(.reg 3 : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.reg 15 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
     ⟨(.reg 6 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.reg 14 : Operand 64), stackPtr s - 24⟩,
     ⟨(.mem (stackPtr s - 16) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.reg 0 : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 8) : Operand 64), 0⟩,
     ⟨(.mem (stackPtr s - 25) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem initialize_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x100017 584)
      (codeRange 0x100017 initializeBytes) initializeEffect := by
  have hSub := prologue_text_sub 0x17 80 (by decide +kernel)
  unfold initializeBytes
  have hFirst := sub_r64_imm32_effect_step 0x100017 0x48 0xec 264
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (subR64Imm32Effect 0x100017 4 264) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1e (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x10001e 0x48 0xd3
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 7 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x21 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100021 0x49 0xf7
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 10 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x24 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100024 0x48 0xfe
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x27 (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x100027 0x4c
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 240))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2f (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x10002f 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 24 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x39 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100039 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 248))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 34 (by decide +kernel)
  case mid => init_store_mid 16, 8, (prologue_text_sub 0x39 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x41 (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x100041 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 42 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x4b (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x10004b 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 240))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 52 (by decide +kernel)
  case mid => init_store_mid 24, 8, (prologue_text_sub 0x4b 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x53 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_imm32_effect_step 0x100053 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 256))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 60 (by decide +kernel)
  case mid => init_store_mid 8, 8, (prologue_text_sub 0x53 12 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5f (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m8_imm8_effect_step 0x10005f
    (.sib 4 none 0 (.d32 239)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x100017) 72 (by decide +kernel)
  case mid => init_store_mid 25, 1, (prologue_text_sub 0x5f 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x67 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [initializeEffect]
  · x86_norm [initializeEffect]
    repeat constructor
  · intro i; cases i <;> x86_norm [initializeEffect]
  · x86_norm [initializeEffect]

private theorem initializeEffect_local : Effect.Local initializeEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [initializeEffect, stackPtr_read, h.read_reg]
  · cases i <;> rfl
  · simp [initializeEffect, Write.Full, Operand.Full]

set_option maxRecDepth 2048 in
theorem execute [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x100010 Digest.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  obtain ⟨n, u, hPush, hu, _, hePush⟩ := pushes boundary hOutside s hReady
    (program_text_slice hCode 0x10 7 (by decide +kernel)) hFrame
  have hCodeU := hePush.codeIn (pushes_avoids hFrame) hCode
  have hFrameU := pushes_frame hFrame hePush
  obtain ⟨m, t, hInit, ht, _, heInit⟩ := initialize_block boundary hOutside u hu
    (program_text_slice hCodeU 0x17 80 (by decide +kernel)) hFrameU
  have heSeq := hePush.seq initializeEffect_local
    (by simp [pushEffect, Write.Full, Operand.Full]) heInit
  have he : (effect s).Holds s t := by
    apply heSeq.weaken
    · x86_norm [pushEffect, initializeEffect, effect]
    · x86_norm [pushEffect, initializeEffect, effect]
      repeat constructor
    · intro i; cases i <;> x86_norm [pushEffect, initializeEffect, effect]
    · x86_norm [pushEffect, initializeEffect, effect]
  exact ⟨n + m, t, hPush.trans hInit, ht, he.codeIn (effect_avoids hFrame) hCode, he⟩

end Md5.Proofs.Buffered.DigestPrepare.Initialize
