import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct.Clear

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x102677
  readable : ∀ off : Nat, off+8≤520 → MemReadable s (stackPtr s+BitVec.ofNat 64 off) 8
  writable : ∀ off : Nat, off+8≤472 → Common.Instructions.CrossPageStore.Writable s
    (stackPtr s+BitVec.ofNat 64 off) 8
  codeApart : ∀ off co cl : Nat, off+8≤472 → co+cl≤118431 →
    RangeApart (stackPtr s+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 co) cl

def bytes : List UInt8 :=
  [72, 141, 116, 36, 72, 72, 199, 132, 36, 176, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 184, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 192, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 200, 0, 0, 0, 0, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x1026ac
    writes := [⟨(.reg 6 : Operand 64),(Operand.reg 4 : Operand 64).read s+72⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+176) : Operand 64),0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+184) : Operand 64),0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+192) : Operand 64),0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s+200) : Operand 64),0⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x102677 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x102677 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x267c (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10267c 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102677 bytes 5 12
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 176 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 176 0x267c 12 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 176 0x2677 53 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2688 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x102688 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102677 bytes 17 12
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 184 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 184 0x2688 12 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 184 0x2677 53 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2694 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x102694 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102677 bytes 29 12
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 192 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 192 0x2694 12 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 192 0x2677 53 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26a0 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1026a0 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x102677 bytes 41 12
  case mid =>
    intro s t hp hh ho
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]; exact hp.writable 200 (by decide)
    · x86_norm [stackPtr]; exact hp.codeApart 200 0x26a0 12 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 200 0x2677 53 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x26ac (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect,BitVec.add_assoc]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Wrapper.Entry.Construct.Clear
