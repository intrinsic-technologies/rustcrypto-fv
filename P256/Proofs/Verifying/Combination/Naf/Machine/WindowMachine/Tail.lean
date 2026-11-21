import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad.Triple
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Test
import P256.Proofs.Verifying.Combination.Naf.Machine.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad

attribute [local x86_compose] testDlOneEffect

structure TailPre (s : RamState) : Prop where
  rip : s.RIP=0x10f42d
  mask : MemReadable s (s.regValue .rsp+40) 8
  output : MemReadable s (s.regValue .rsp+16) 8

def tailBytes : List UInt8 :=
  [0x48,0x23,0x54,0x24,0x28,0x4c,0x01,0xea,0xf6,0xc2,0x01,0x48,0x8b,0x74,0x24,0x10]

def tailValue (s : RamState) : BitVec 64 :=
  ((Operand.reg 2 : Operand 64).read s &&& memLoad s.external ((Operand.reg 4 : Operand 64).read s+40) 64)+
    (Operand.reg 13 : Operand 64).read s

def tailEffect (s : RamState) : Effect :=
  { rip := 0x10f43d
    writes := [⟨(Operand.reg 2 : Operand 64),tailValue s⟩,
      ⟨(Operand.reg 6 : Operand 64),memLoad s.external ((Operand.reg 4 : Operand 64).read s+16) 64⟩]
    flags := some ⟨none,none,none,some (((tailValue s).setWidth 8 &&& 1)==0),none,none⟩ }

theorem tail_block [Bindings] (boundary : ReturnBoundary) (outer : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary TailPre (codeRange 0x10f42d tailBytes) (Effect.post tailEffect) := by
  have next (offset : Nat) (bound : offset<118431) :=
    boundary_ne_program outer (inProgram_of_textOffset offset bound)
  advance_begin (show StepEffect _ _ (andR64M64Effect 0x10f42d 2 (.sib 4 none 0 (.d8 40))) from
    and_r64_m64_effect_step 0x10f42d 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case pre => intro s hp; exact ⟨hp.rip,hp.mask⟩
  case next => intro _ _; exact next 0xf432 (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect 0x10f432 2 13) from
    add_r64_r64_effect_step 0x10f432 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f42d tailBytes 5 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,next 0xf435 (by decide)⟩
  advance_then (test_dl_one_effect_step 0x10f435)
  case loc =>
    apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
    · intro s t h; simp only [testDlOneEffect,h.read_reg]
    · intro s; simp [testDlOneEffect,Write.Full]
  case sub => exact codeRange_slice_subset 0x10f42d tailBytes 8 3
  case mid =>
    intro s t hp he ho
    exact ⟨he.rip_of (by x86_norm),Effect.Avoids.of_noMem
      (by simp [testDlOneEffect,Effect.components,Component.Covers]) _,next 0xf438 (by decide)⟩
  advance_then (show StepEffect _ _ (movR64M64Effect 0x10f438 6 (.sib 4 none 0 (.d8 16))) from
    mov_r64_m64_effect_step 0x10f438 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f42d tailBytes 11 5
  case mid =>
    intro s t hp he ho
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,next 0xf43d (by decide)⟩
    x86_norm
    exact hp.output
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [tailEffect]
  · x86_norm [tailEffect,tailValue]
    repeat constructor
  · intro i
    cases i <;> x86_norm [tailEffect,tailValue,testFlags]
  · x86_norm [tailEffect]

end P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine
