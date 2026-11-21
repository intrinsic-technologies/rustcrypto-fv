import Md5.Proofs.Streaming.Prologue

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Block Md5.Proofs.Streaming

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_compose] stackPtr_read BitVec.sub_eq_add_neg
  movM8Imm8Effect subR64Imm32Effect
attribute [local x86_local] movM8Imm8Effect_local



def resetInitBytes : List UInt8 := [0x48, 0x81, 0xec, 0x38, 0x1, 0x0, 0x0, 0x4c, 0x89, 0x84, 0x24, 0x20, 0x1, 0x0, 0x0, 0x49, 0x89, 0xcc, 0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0x7c, 0x24, 0x10, 0x48, 0xba, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0x48, 0x89, 0x54, 0x24, 0x68, 0x48, 0xbf, 0x1, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x48, 0x89, 0x7c, 0x24, 0x60, 0x48, 0xc7, 0x44, 0x24, 0x70, 0x0, 0x0, 0x0, 0x0, 0xc6, 0x44, 0x24, 0x5f, 0x0]

def resetInitEffect (s : RamState) : Effect where
  rip := 0x101392
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 312⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
     ⟨(.reg 12 : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 288) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 296) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.reg 2 : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.mem (stackPtr s - 208) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.reg 7 : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 216) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 200) : Operand 64), 0⟩,
     ⟨(.mem (stackPtr s - 217) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem reset_initialize [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x10134a 632)
      (codeRange 0x10134a resetInitBytes) resetInitEffect := by
  have hSub := prologue_text_sub 0x134a 72 (by decide +kernel)
  unfold resetInitBytes
  have hFirst := sub_r64_imm32_effect_step 0x10134a 0x48 0xec 312
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (subR64Imm32Effect 0x10134a 4 312) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1351 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101351 0x4c (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 288)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 7 (by decide +kernel)
  case mid => init_store_mid 24, 8, (prologue_text_sub 0x1351 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1359 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x101359 0x49 0xcc (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 15 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x135c (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x10135c 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 24)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 18 (by decide +kernel)
  case mid => init_store_mid 288, 8, (prologue_text_sub 0x135c 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1361 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101361 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 16)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 23 (by decide +kernel)
  case mid => init_store_mid 296, 8, (prologue_text_sub 0x1361 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1366 (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x101366 0x48 0xba (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 28 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1370 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x101370 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 104)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 38 (by decide +kernel)
  case mid => init_store_mid 208, 8, (prologue_text_sub 0x1370 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1375 (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x101375 0x48 0xbf (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 43 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x137f (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x10137f 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 53 (by decide +kernel)
  case mid => init_store_mid 216, 8, (prologue_text_sub 0x137f 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1384 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_imm32_effect_step 0x101384 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 112)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 58 (by decide +kernel)
  case mid => init_store_mid 200, 8, (prologue_text_sub 0x1384 9 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x138d (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m8_imm8_effect_step 0x10138d (.sib 4 none 0 (.d8 95)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10134a) 67 (by decide +kernel)
  case mid => init_store_mid 217, 1, (prologue_text_sub 0x138d 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1392 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetInitEffect]
  · x86_norm [resetInitEffect]
    repeat constructor
  · intro i; cases i <;> x86_norm [resetInitEffect]
  · x86_norm [resetInitEffect]


private theorem resetInitEffect_local : Effect.Local resetInitEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [resetInitEffect, stackPtr_read, h.read_reg]
  · cases i <;> rfl
  · simp [resetInitEffect, Write.Full, Operand.Full]

theorem resetInitEffect_avoids {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 296 ≤ budget) :
    (resetInitEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [resetInitEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact h.avoids_mem 24 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 288 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 296 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 208 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 216 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 200 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 217 1 (by omega) (by decide) x hx hcov

theorem reset_initialized [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x101340 680 s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (Effect.seq (prologuePushEffect 0x101340) resetInitEffect s).Holds s t := by
  obtain ⟨n, u, hPush, hu, _, hEPush⟩ :=
    prologue_pushes boundary 0x101340 680 (by decide +kernel)
      (prologue_text_sub 0x1340 10 (by decide +kernel))
      (prologue_boundary boundary hOutside 0x1340 (by decide +kernel))
      s hReady (program_text_slice hCode 0x1340 10 (by decide +kernel)) hFrame
  have hCodeU := hEPush.codeIn (prologuePushEffect_avoids hFrame (by decide +kernel)) hCode
  have hFrameU : PrologueFrame 0x10134a 632 u :=
    hFrame.after_pushes (by decide +kernel) hEPush
  obtain ⟨m, t, hInit, ht, _, hEInit⟩ :=
    reset_initialize boundary hOutside u hu
      (program_text_slice hCodeU 0x134a 72 (by decide +kernel)) hFrameU
  refine ⟨n + m, t, hPush.trans hInit, ht,
    hEInit.codeIn (resetInitEffect_avoids hFrameU (by decide)) hCodeU, ?_⟩
  exact hEPush.seq resetInitEffect_local
    (by simp [prologuePushEffect, Write.Full, Operand.Full]) hEInit


end Md5.Proofs.NewEntries.Reset
