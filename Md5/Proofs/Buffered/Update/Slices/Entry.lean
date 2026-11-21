import Md5.Proofs.Buffered.Update.Memory
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def kind (variant : Bool) : UpdateKind :=
  if variant then .updateFinalizeInto else .slices

def pc (variant : Bool) (old : BitVec 64) : BitVec 64 :=
  if variant then old + 0x15b0 else old

theorem kind_context (variant : Bool) (s : RamState) :
    (kind variant).context s = stackPtr s + 192 := by cases variant <;> rfl

theorem kind_inputRegister (variant : Bool) :
    (kind variant).inputRegister = 14 := by cases variant <;> rfl

theorem kind_sizeRegister (variant : Bool) :
    (kind variant).sizeRegister = 3 := by cases variant <;> rfl

attribute [local x86_compose] movzxR32M8Effect

def entryBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0xac, 0x24, 0xff, 0x00, 0x00, 0x00,
    0xba, 0x40, 0x00, 0x00, 0x00, 0x4c, 0x29, 0xea, 0x48, 0x89, 0xdd,
    0x48, 0x29, 0xd5]

def position (s : RamState) : BitVec 64 :=
  ((Operand.mem (stackPtr s + 255) : Operand 8).read s).setWidth 64

def entryEffect (variant : Bool) (s : RamState) : Effect where
  rip := pc variant 0x10036c
  writes := [⟨(.reg 13 : Operand 64), position s⟩,
    ⟨(.reg 2 : Operand 64), 64 - position s⟩,
    ⟨(.reg 5 : Operand 64), (Operand.reg 3 : Operand 64).read s - (64 - position s)⟩]
  flags := some (.ofStatusFlags
    (subSpec ((Operand.reg 3 : Operand 64).read s) (64 - position s)).2)

structure EntryPre (variant : Bool) (s : RamState) : Prop where
  rip : s.RIP = pc variant 0x100355
  readable : MemReadable s (stackPtr s + 255) 1

theorem entry {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (EntryPre variant) (codeRange (pc variant 0x100355) entryBytes) (entryEffect variant) := by
  cases variant with
  | false =>
    unfold entryBytes
    md5_run_begin movzx_r_m8_rex_effect_step 0x100355 0x44 (by unfold RexPrefix; decide)
      32 (Or.inr rfl) (by intro seg; rfl) 5 (.sib 4 none 0 (.d32 255))
      (by decide) (by decide) (by decide)
    case pre => intro s h; exact ⟨h.rip, h.readable⟩
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x35e (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x10035e 0xba (by decide) 64
    case sub => apply codeRange_mem_of_drop (p := 0x100355) 9; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x363 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x100363 0x4c 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x100355) 14; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x366 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100366 0x48 0xdd
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x100355) 17; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x369 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x100369 0x48 0xd5
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x100355) 20; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x36c (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [entryEffect]
    · x86_norm [entryEffect, position, stackPtr]
      exact ⟨rfl, rfl, rfl⟩
    · intro i; cases i <;> x86_norm [entryEffect, position, stackPtr]
      all_goals rfl
    · x86_norm [entryEffect]
  | true =>
    unfold entryBytes
    md5_run_begin movzx_r_m8_rex_effect_step 0x101905 0x44 (by unfold RexPrefix; decide)
      32 (Or.inr rfl) (by intro seg; rfl) 5 (.sib 4 none 0 (.d32 255))
      (by decide) (by decide) (by decide)
    case pre => intro s h; exact ⟨h.rip, h.readable⟩
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x190e (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x10190e 0xba (by decide) 64
    case sub => apply codeRange_mem_of_drop (p := 0x101905) 9; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1913 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x101913 0x4c 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x101905) 14; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1916 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101916 0x48 0xdd
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x101905) 17; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1919 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x101919 0x48 0xd5
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x101905) 20; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x191c (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [entryEffect]
    · x86_norm [entryEffect, position, stackPtr]
      exact ⟨rfl, rfl, rfl⟩
    · intro i; cases i <;> x86_norm [entryEffect, position, stackPtr]
      all_goals rfl
    · x86_norm [entryEffect]

structure Prepared (variant : Bool) [Bindings] (boundary : ReturnBoundary) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  effect : (entryEffect variant s).Holds s t

theorem prepare {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre (kind variant) boundary message input s) :
    ∃ u, Prepared variant boundary s u := by
  have hc : CodeIn (codeRange (pc variant 0x100355) entryBytes) s := by
    cases variant with
    | false => exact program_text_slice h.code 0x355 23 (by decide +kernel)
    | true => exact program_text_slice h.code 0x1905 23 (by decide +kernel)
  obtain ⟨fuel, u, ha, hr, _, he⟩ := entry (variant := variant) boundary h.boundaryOutside
    s h.ready hc ⟨(by cases variant <;> exact h.rip),
      (by cases variant <;> exact h.contextReadable 63 1 (by decide))⟩
  refine ⟨u, ⟨⟨fuel, ha⟩, hr, ?_, he⟩⟩
  apply he.codeIn _ h.code
  apply Effect.Avoids.of_noMem
  simp [entryEffect, Effect.components, Component.Covers]

end Md5.Proofs.Buffered.Update.Slices
