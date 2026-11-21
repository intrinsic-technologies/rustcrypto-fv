import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Encoding.Parser.ByteStore
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
open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse.SecondZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure SelectZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x1141c2
  writable : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(72,1),(24,8),(16,8),(8,8),(0,8)] →
    MemWritable s ((Operand.reg 4 : Operand 64).read s+i) n
  codeApart : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(72,1),(24,8),(16,8),(8,8),(0,8)] →
    ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s+i) n (Extracted.textAddress+BitVec.ofNat 64 offset) len

def selectZeroBytes : List UInt8 :=
  [0x40,0x88,0x6c,0x24,0x48,0x48,0xc7,0x44,0x24,0x18,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x10,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x8,0x0,0x0,0x0,0x0,0x48,0xc7,0x4,0x24,0x0,0x0,0x0,0x0]

def selectZeroEffect (s : RamState) : Effect :=
  { rip := 0x1141ea
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+72) : Operand 8),
      (Operand.reg 5 : Operand 8).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+0) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+8) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+16) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+24) : Operand 64),0⟩] }

theorem select_zero_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1141c2 selectZeroBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x141c2 selectZeroBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem select_zero [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectZeroPre (codeRange 0x1141c2 selectZeroBytes)
      (Effect.post selectZeroEffect) := by
  advance_begin (mov_m8_r8_effect_step 0x1141c2 0x40 (by simp [RexPrefix]) 5
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 72 1 (by simp),h.codeApart 72 1 (by simp) 0x141c2 5 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x141c7 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 72 1 (by simp) 0x141c2 40 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x1141c7 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1141c2 selectZeroBytes 5 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 8 (by simp)
    · x86_norm
      exact hP.codeApart 24 8 (by simp) 0x141c7 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 8 (by simp) 0x141c2 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141d0 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x1141d0 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1141c2 selectZeroBytes 14 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 8 (by simp)
    · x86_norm
      exact hP.codeApart 16 8 (by simp) 0x141d0 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 8 (by simp) 0x141c2 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141d9 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x1141d9 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1141c2 selectZeroBytes 23 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 8 (by simp) 0x141d9 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 8 (by simp) 0x141c2 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141e2 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x1141e2 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1141c2 selectZeroBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 8 (by simp)
    · x86_norm
      exact hP.codeApart 0 8 (by simp) 0x141e2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 8 (by simp) 0x141c2 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141ea (by decide))
  advance_finish [selectZeroEffect]

theorem selectZeroPre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x1141c2) : SelectZeroPre t := by
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

end P256.Proofs.Field.Inverse.SecondZero
