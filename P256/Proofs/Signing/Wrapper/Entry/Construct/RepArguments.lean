import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct.RepArguments

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1026df
  readable : ∀ off : Nat, off+8≤520 → MemReadable s (stackPtr s+BitVec.ofNat 64 off) 8
  writable : ∀ off : Nat, off+8≤472 → Common.Instructions.CrossPageStore.Writable s
    (stackPtr s+BitVec.ofNat 64 off) 8
  codeApart : ∀ off co cl : Nat, off+8≤472 → co+cl≤118431 →
    RangeApart (stackPtr s+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 co) cl

def bytes : List UInt8 :=
  [72, 139, 68, 36, 64, 72, 141, 188, 36, 120, 1, 0, 0, 185, 12, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x1026f1
    writes := [⟨(.reg 0 : Operand 64),(Operand.mem ((Operand.reg 4 : Operand 64).read s+64) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 4 : Operand 64).read s+376⟩,
      ⟨(.reg 1 : Operand 64),12⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1026df bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x1026df 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.readable 64 (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x26e4 (by decide))
  advance_then (lea_r64_effect_step 0x1026e4 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1026df bytes 5 8
  case mid =>
    intro s t hp hh ho
    refine ⟨?_,Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    · exact hh.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26ec (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1026ec 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x1026df bytes 13 5
  case mid =>
    intro s t hp hh ho
    refine ⟨?_,Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    · exact hh.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26f1 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect,BitVec.add_assoc]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Wrapper.Entry.Construct.RepArguments
