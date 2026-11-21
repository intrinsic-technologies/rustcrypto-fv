import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.HMAC.Key.Frame
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Field.Preserve
import P256.Proofs.Sec1.SquareRoot.State
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

open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.HMAC.Key (stack_code_apart)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SelectZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x114552
  writable : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(40,1),(72,8),(64,8),(56,8),(48,8)] →
    MemWritable s ((Operand.reg 4 : Operand 64).read s+i) n
  codeApart : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(40,1),(72,8),(64,8),(56,8),(48,8)] →
    ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s+i) n (Extracted.textAddress+BitVec.ofNat 64 offset) len

def selectZeroBytes : List UInt8 :=
  [0x88,0x44,0x24,0x28,0x48,0xc7,0x44,0x24,0x48,0,0,0,0,
    0x48,0xc7,0x44,0x24,0x40,0,0,0,0,0x48,0xc7,0x44,0x24,0x38,0,0,0,0,
    0x48,0xc7,0x44,0x24,0x30,0,0,0,0]

def selectZeroEffect (s : RamState) : Effect :=
  { rip := 0x11457a
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+40) : Operand 8),
      (Operand.reg 0 : Operand 8).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+48) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+56) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+64) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+72) : Operand 64),0⟩] }

theorem select_zero_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x114552 selectZeroBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x14552 selectZeroBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem select_zero [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectZeroPre (codeRange 0x114552 selectZeroBytes)
      (Effect.post selectZeroEffect) := by
  advance_begin (mov_m8_r8_legacy_effect_step 0x114552 0 (by decide)
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 40 1 (by simp),h.codeApart 40 1 (by simp) 0x14552 4 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14556 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 40 1 (by simp) 0x14552 40 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x114556 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114552 selectZeroBytes 4 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 8 (by simp)
    · x86_norm
      exact hP.codeApart 72 8 (by simp) 0x14556 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 8 (by simp) 0x14552 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1455f (by decide))
  advance_then (mov_m64_imm32_effect_step 0x11455f 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114552 selectZeroBytes 13 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 8 (by simp)
    · x86_norm
      exact hP.codeApart 64 8 (by simp) 0x1455f 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 8 (by simp) 0x14552 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14568 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x114568 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114552 selectZeroBytes 22 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 8 (by simp)
    · x86_norm
      exact hP.codeApart 56 8 (by simp) 0x14568 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 8 (by simp) 0x14552 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14571 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x114571 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x114552 selectZeroBytes 31 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 8 (by simp)
    · x86_norm
      exact hP.codeApart 48 8 (by simp) 0x14571 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 8 (by simp) 0x14552 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1457a (by decide))
  advance_finish [selectZeroEffect]

theorem selectZeroPre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x114552) : SelectZeroPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro i n hi
    rw [state.stack_address]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp only [BitVec.reduceSub]
    · exact writable_of_grow (stack_sub_writable pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
        (by decide) (by decide) (by decide) (by omega)) state.allocated
    all_goals exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) state.allocated
  · intro i n hi offset len hcode
    rw [state.stack_address]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_code_apart pre (by decide) (by decide) hcode

end P256.Proofs.Sec1.SquareRoot
