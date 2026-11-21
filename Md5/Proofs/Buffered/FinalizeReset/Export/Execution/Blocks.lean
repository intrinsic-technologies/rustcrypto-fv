import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.FinalizeReset.Export

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem stackPtr_eq_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_eq_read

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] movM8Imm8Effect_local

structure StagePre (pc : BitVec 64) (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = pc

def saveEffect (s : RamState) : Effect :=
  let lo := (Operand.mem (stackPtr s + 0xe8) : Operand 64).read s
  let hi := (Operand.mem (stackPtr s + 0xf0) : Operand 64).read s
  { rip := 0x10093c
    writes := [⟨(.reg 0 : Operand 64), lo⟩, ⟨(.reg 1 : Operand 64), hi⟩,
      ⟨(.mem (stackPtr s + 0x128) : Operand 64), lo⟩,
      ⟨(.mem (stackPtr s + 0x130) : Operand 64), hi⟩] }

def resetEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := match variant with | .saved => 0x10096a | .direct => 0x101019
    writes := [⟨(.reg 0 : Operand 64), stackPtr s + 0x48⟩,
      ⟨(.reg 1 : Operand 64), 0xefcdab8967452301⟩,
      ⟨(.mem (stackPtr s + 0x50) : Operand 64), 0x1032547698badcfe⟩,
      ⟨(.mem (stackPtr s + 0x48) : Operand 64), 0xefcdab8967452301⟩,
      ⟨(.mem (stackPtr s + 0x58) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 0x47) : Operand 8), 0⟩] }

def copyEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  let lo := (Operand.mem (stackPtr s + (match variant with | .saved => 0x128 | .direct => 0xe8)) : Operand 64).read s
  let hi := (Operand.mem (stackPtr s + (match variant with | .saved => 0x130 | .direct => 0xf0)) : Operand 64).read s
  { rip := match variant with | .saved => 0x100989 | .direct => 0x100feb
    writes := [⟨(.reg 0 : Operand 64), lo⟩, ⟨(.reg 1 : Operand 64), hi⟩,
      ⟨(.reg 2 : Operand 64), outputAddress s⟩,
      ⟨(.mem (outputAddress s + 8) : Operand 64), hi⟩,
      ⟨(.mem (outputAddress s) : Operand 64), lo⟩] }

set_option maxHeartbeats 500000 in
theorem saveExecution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (StagePre 0x10091c) (codeRange 0x10091c bytes) saveEffect := by
  unfold bytes
  md5_run_begin (mov_r64_m64_effect_step 0x10091c 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe8))
    (by decide) (by decide) (by decide))
  case pre => intro s h; exact ⟨h.rip, (stackWritable h.toStorage 0xe8 8 (by decide)).readable⟩
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x924 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step 0x100924 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xf0))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10091c) 8 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (stackWritable h.toStorage 0xf0 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x92c (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step 0x10092c 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0x128))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10091c) 16 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
      Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · x86_norm
      exact stackWritable h.toStorage 0x128 8 (by decide)
    · x86_norm
      exact stackTextApart h.toStorage 0x128 8 0x92c 8
        (by decide) (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      exact stackTextApart h.toStorage 0x128 8 0x91c 109
        (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x934 (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step 0x100934 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x130))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10091c) 24 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
      Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · x86_norm
      exact stackWritable h.toStorage 0x130 8 (by decide)
    · x86_norm
      exact stackTextApart h.toStorage 0x130 8 0x934 8
        (by decide) (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      exact stackTextApart h.toStorage 0x130 8 0x91c 109
        (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x93c (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [saveEffect]
  · x86_norm [saveEffect, outputAddress]
    repeat constructor
  · intro i; cases i <;> x86_norm [saveEffect]
  · x86_norm [saveEffect]

set_option maxHeartbeats 500000 in
theorem resetExecution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) {variant : Variant} :
    AdvancesBlock boundary (fun s ↦ StagePre (match variant with | .saved => 0x10093c | .direct => 0x100feb) s variant) (codeRange (variant.address 0x10091c) (bytes variant)) (fun s ↦ resetEffect s variant) := by
  cases variant with
  | saved =>
      change AdvancesBlock boundary (fun s ↦ StagePre 0x10093c s .saved) (codeRange 0x10091c (bytes .saved)) (fun s ↦ resetEffect s .saved)
      unfold bytes
      md5_run_begin (lea_r64_effect_step 0x10093c 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x48))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 32 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x941 (by decide +kernel)
      md5_run_then (mov_r64_imm64_effect_step 0x100941 0x48 0xb9
        (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 37 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x94b (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x10094b 0x48
        (by unfold RexWPrefix; decide) 1 (.base 0 (.d8 8))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 47 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x50 8 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x50 8 0x94b 4
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x50 8 0x91c 109
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x94f (by decide +kernel)
      md5_run_then (mov_r64_imm64_effect_step 0x10094f 0x48 0xb9
        (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 51 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x959 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100959 0x48
        (by unfold RexWPrefix; decide) 1 (.base 0 .none)
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 61 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x48 8 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x48 8 0x959 3
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x48 8 0x91c 109
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x95c (by decide +kernel)
      md5_run_then (Stores.mov_m64_imm32_effect_step 0x10095c 0x48
        (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x58))
        (by decide) (by decide) (by decide) 0)
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 64 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x58 8 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x58 8 0x95c 9
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x58 8 0x91c 109
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x965 (by decide +kernel)
      md5_run_then (Stores.mov_m8_imm8_effect_step 0x100965 (.sib 4 none 0 (.d8 0x47))
        (by decide) (by decide) (by decide) 0)
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 73 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x47 1 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x47 1 0x965 5
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x47 1 0x91c 109
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x96a (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [resetEffect]
      · x86_norm [resetEffect, outputAddress]
        repeat constructor
      · intro i; cases i <;> x86_norm [resetEffect]
      · x86_norm [resetEffect]
  | direct =>
      change AdvancesBlock boundary (fun s ↦ StagePre 0x100feb s .direct) (codeRange 0x100fcc (bytes .direct)) (fun s ↦ resetEffect s .direct)
      unfold bytes
      md5_run_begin (lea_r64_effect_step 0x100feb 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x48))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 31 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xff0 (by decide +kernel)
      md5_run_then (mov_r64_imm64_effect_step 0x100ff0 0x48 0xb9
        (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 36 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xffa (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100ffa 0x48
        (by unfold RexWPrefix; decide) 1 (.base 0 (.d8 8))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 46 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x50 8 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x50 8 0xffa 4
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x50 8 0xfcc 77
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xffe (by decide +kernel)
      md5_run_then (mov_r64_imm64_effect_step 0x100ffe 0x48 0xb9
        (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 50 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1008 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x101008 0x48
        (by unfold RexWPrefix; decide) 1 (.base 0 .none)
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 60 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x48 8 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x48 8 0x1008 3
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x48 8 0xfcc 77
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x100b (by decide +kernel)
      md5_run_then (Stores.mov_m64_imm32_effect_step 0x10100b 0x48
        (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x58))
        (by decide) (by decide) (by decide) 0)
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 63 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x58 8 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x58 8 0x100b 9
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x58 8 0xfcc 77
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1014 (by decide +kernel)
      md5_run_then (Stores.mov_m8_imm8_effect_step 0x101014 (.sib 4 none 0 (.d8 0x47))
        (by decide) (by decide) (by decide) 0)
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 72 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact stackWritable h.toStorage 0x47 1 (by decide)
        · x86_norm
          exact stackTextApart h.toStorage 0x47 1 0x1014 5
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact stackTextApart h.toStorage 0x47 1 0xfcc 77
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1019 (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [resetEffect]
      · x86_norm [resetEffect, outputAddress]
        repeat constructor
      · intro i; cases i <;> x86_norm [resetEffect]
      · x86_norm [resetEffect]

set_option maxHeartbeats 500000 in
theorem copyExecution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) {variant : Variant} :
    AdvancesBlock boundary (fun s ↦ StagePre (match variant with | .saved => 0x10096a | .direct => 0x100fcc) s variant) (codeRange (variant.address 0x10091c) (bytes variant)) (fun s ↦ copyEffect s variant) := by
  cases variant with
  | saved =>
      change AdvancesBlock boundary (fun s ↦ StagePre 0x10096a s .saved) (codeRange 0x10091c (bytes .saved)) (fun s ↦ copyEffect s .saved)
      unfold bytes
      md5_run_begin (mov_r64_m64_effect_step 0x10096a 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0x128))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 78 (by decide +kernel)
      case pre =>
        intro s h
        exact ⟨h.rip, (stackWritable h.toStorage 0x128 8 (by decide)).readable⟩
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x972 (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x100972 0x48
        (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x130))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 86 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (stackWritable h.toStorage 0x130 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x97a (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x10097a 0x48
        (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 0xb8))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 94 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (stackWritable h.toStorage 0xb8 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x982 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100982 0x48
        (by unfold RexWPrefix; decide) 1 (.base 2 (.d8 8))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 102 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact outputWritable h.toStorage 0x8 8 (by decide)
        · x86_norm
          exact outputTextApart h.toStorage 0x8 8 0x982 4
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact outputTextApart h.toStorage 0x8 8 0x91c 109
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x986 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100986 0x48
        (by unfold RexWPrefix; decide) 0 (.base 2 .none)
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10091c) 106 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact outputWritable h.toStorage 0x0 8 (by decide)
        · x86_norm
          exact outputTextApart h.toStorage 0x0 8 0x986 3
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact outputTextApart h.toStorage 0x0 8 0x91c 109
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x989 (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [copyEffect, outputAddress, BitVec.add_zero]
      · x86_norm [copyEffect, outputAddress, BitVec.add_zero]
        repeat constructor
      · intro i; cases i <;> x86_norm [copyEffect, outputAddress, BitVec.add_zero]
      · x86_norm [copyEffect, outputAddress, BitVec.add_zero]
  | direct =>
      change AdvancesBlock boundary (fun s ↦ StagePre 0x100fcc s .direct) (codeRange 0x100fcc (bytes .direct)) (fun s ↦ copyEffect s .direct)
      unfold bytes
      md5_run_begin (mov_r64_m64_effect_step 0x100fcc 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe8))
        (by decide) (by decide) (by decide))
      case pre =>
        intro s h
        exact ⟨h.rip, (stackWritable h.toStorage 0xe8 8 (by decide)).readable⟩
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xfd4 (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x100fd4 0x48
        (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xf0))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 8 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (stackWritable h.toStorage 0xf0 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xfdc (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x100fdc 0x48
        (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 0xb8))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 16 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (stackWritable h.toStorage 0xb8 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xfe4 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100fe4 0x48
        (by unfold RexWPrefix; decide) 1 (.base 2 (.d8 8))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 24 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact outputWritable h.toStorage 0x8 8 (by decide)
        · x86_norm
          exact outputTextApart h.toStorage 0x8 8 0xfe4 4
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact outputTextApart h.toStorage 0x8 8 0xfcc 77
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xfe8 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100fe8 0x48
        (by unfold RexWPrefix; decide) 0 (.base 2 .none)
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100fcc) 28 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_,
          Effect.Local.avoids (by x86_local) (hO true) ?_⟩
        · x86_norm
          exact outputWritable h.toStorage 0x0 8 (by decide)
        · x86_norm
          exact outputTextApart h.toStorage 0x0 8 0xfe8 3
            (by decide) (by decide +kernel)
        · apply Effect.avoids_codeRange
          x86_norm
          exact outputTextApart h.toStorage 0x0 8 0xfcc 77
            (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xfeb (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [copyEffect, outputAddress, BitVec.add_zero]
      · x86_norm [copyEffect, outputAddress, BitVec.add_zero]
        repeat constructor
      · intro i; cases i <;> x86_norm [copyEffect, outputAddress, BitVec.add_zero]
      · x86_norm [copyEffect, outputAddress, BitVec.add_zero]

end Md5.Proofs.Buffered.FinalizeReset.Export
