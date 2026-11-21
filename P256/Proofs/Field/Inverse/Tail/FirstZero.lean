import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse.FirstZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure SelectZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x114154
  writable : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(144,1),(24,8),(16,8),(8,8),(0,8)] →
    MemWritable s ((Operand.reg 4 : Operand 64).read s+i) n
  codeApart : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(144,1),(24,8),(16,8),(8,8),(0,8)] →
    ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s+i) n (Extracted.textAddress+BitVec.ofNat 64 offset) len

def selectZeroBytes : List UInt8 :=
  [0x88,0x84,0x24,0x90,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x18,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x10,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x8,0x0,0x0,0x0,0x0,0x48,0xc7,0x4,0x24,0x0,0x0,0x0,0x0]

def selectZeroEffect (s : RamState) : Effect :=
  { rip := 0x11417e
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+144) : Operand 8),
      (Operand.reg 0 : Operand 8).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+0) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+16) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+24) : Operand 64),0⟩] }

theorem select_zero_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x114154 selectZeroBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x14154 selectZeroBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem select_zero [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectZeroPre (codeRange 0x114154 selectZeroBytes)
      (Effect.post selectZeroEffect) := by
  advance_begin (mov_m8_r8_legacy_effect_step 0x114154 0 (by decide)
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 144 1 (by simp),h.codeApart 144 1 (by simp) 0x14154 7 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1415b (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 144 1 (by simp) 0x14154 42 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x11415b 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114154 selectZeroBytes 7 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 8 (by simp)
    · x86_norm
      exact hP.codeApart 24 8 (by simp) 0x1415b 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 8 (by simp) 0x14154 42 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14164 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x114164 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114154 selectZeroBytes 16 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 8 (by simp)
    · x86_norm
      exact hP.codeApart 16 8 (by simp) 0x14164 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 8 (by simp) 0x14154 42 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1416d (by decide))
  advance_then (mov_m64_imm32_effect_step 0x11416d 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114154 selectZeroBytes 25 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 8 (by simp) 0x1416d 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 8 (by simp) 0x14154 42 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14176 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x114176 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114154 selectZeroBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 8 (by simp)
    · x86_norm
      exact hP.codeApart 0 8 (by simp) 0x14176 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 8 (by simp) 0x14154 42 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1417e (by decide))
  advance_finish [selectZeroEffect]

theorem selectZeroPre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x114154) : SelectZeroPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro i n hi
    rw [state.stack_address]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp only [BitVec.reduceSub]
    · exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable pre.stack (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide) (by decide) (by omega)) state.allocated
    all_goals exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht)) (by decide) (by decide)) state.allocated
  · intro i n hi offset len hcode
    rw [state.stack_address]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_code_apart pre (by decide) (by decide) hcode

end P256.Proofs.Field.Inverse.FirstZero
