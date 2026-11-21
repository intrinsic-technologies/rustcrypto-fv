import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
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
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Field.Montgomery.Reduction (BorrowSlotPre)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CanonicalPre (p : BitVec 64) (s : RamState) : Prop extends BorrowSlotPre p s where
  pointerWritable : MemWritable s (stackPtr s + 184#64) 8
  pointerAvoids : ∀ a, (Component.mem (stackPtr s + 184#64) 8).Covers a → ¬ InProgram a

theorem CanonicalPre.pointer_apart {p : BitVec 64} {s : RamState} (h : CanonicalPre p s)
    (offset len : Nat) (hc : offset + len ≤ 118431) :
    RangeApart (stackPtr s + 184#64) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply h.pointerAvoids _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

def canonicalHighSetupBytes : List UInt8 :=
  [0x48,0x89,0x0c,0x24,0x48,0x2b,0x34,0x24,
    0x48,0x89,0xbc,0x24,0xb8,0,0,0,0x48,0xc1,0xfe,0x3f]

def canonicalHighSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fcb0
    writes := [⟨(Operand.mem (stackPtr s) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s + 184#64) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64),
        ((Operand.reg 6 : Operand 64).read s - (Operand.reg 1 : Operand 64).read s).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_high_setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (CanonicalPre 0x10fc9c)
      (codeRange 0x10fc9c canonicalHighSetupBytes) (Effect.post canonicalHighSetupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fc9c 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 0#64) 8
      simpa only [BitVec.add_zero] using h.writable
    · change RangeApart (stackPtr s + 0#64) 8 0x10fc9c 4
      have ha := h.toBorrowSlotPre.apart 0xfc9c 4 (by decide +kernel)
      change RangeApart (stackPtr s) 8 (0x10fc9c : BitVec 64) 4 at ha
      simpa only [BitVec.add_zero] using ha
  case av =>
    intro s h
    apply h.toBorrowSlotPre.avoids_code 0xfc9c canonicalHighSetupBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨BitVec.add_zero _, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfca0 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x10fca0 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc9c canonicalHighSetupBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfca4 (by decide +kernel))
  advance_then (mov_m64_r64_effect_step 0x10fca4 0x48
    (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d32 184))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc9c canonicalHighSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.pointerWritable
    · x86_norm [BitVec.add_zero]
      exact hP.pointer_apart 0xfca4 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      intro c hc a len he
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases he
        have hsp : stackPtr t = stackPtr s :=
          hH.agrees.read (n := 64) (r := 4) (by x86_norm)
        change RangeApart (stackPtr t + 184#64) 8 0x10fc9c canonicalHighSetupBytes.length
        rw [hsp]
        exact hP.pointer_apart 0xfc9c canonicalHighSetupBytes.length (by decide +kernel)
      · cases he
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcac (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x10fcac 0x48 0xfe 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc9c canonicalHighSetupBytes 16 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcb0 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [canonicalHighSetupEffect, BitVec.add_zero, stackPtr, Operand.read_reg64]
    exact ⟨.inl ⟨(BitVec.add_zero _).symm, rfl⟩, rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [canonicalHighSetupEffect]
  · x86_norm [canonicalHighSetupEffect, BitVec.add_zero, stackPtr, Operand.read_reg64]
    exact BitVec.add_zero _

end P256.Proofs.Sec1.Decompress.Input
