import X86Proofs.Instructions.Xor.Generated.RR.Triple
import P256.Proofs.Projective.Multiply.Machine.Lookup.Instructions.Cmp
import P256.Proofs.Projective.Multiply.Machine.Lookup.Digit
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_avoids setcc_r8_rex_effect_step)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Lookup.Instructions

def choiceBytes (imm : UInt8) : List UInt8 :=
  [0x31,0xff,0x41,0x80,0xff,imm,0x40,0x0f,0x94,0xc7]

def choiceEffect (p : BitVec 64) (imm : UInt8) (s : RamState) : Effect :=
  { rip := p + 10
    writes := [⟨(Operand.reg 7 : Operand 64),
      if (s.regValue .r15).setWidth 8 = imm.toBitVec then 1 else 0⟩]
    flags := some (.ofStatusFlags (cmpSpec ((s.regValue .r15).setWidth 8) imm.toBitVec)) }

set_option maxHeartbeats 800000 in
theorem choice_prefix [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (imm : UInt8)
    (next : ∀ k : Nat, k ≤ 10 → p + BitVec.ofNat 64 k ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (choiceBytes imm))
      (Effect.post (choiceEffect p imm)) := by
  advance_begin (xor_r32_r32_effect_step p 0xff rfl)
  case sub => simpa [choiceBytes] using codeRange_slice_subset p (choiceBytes imm) 0 2
  case next => intro s h; exact next 2 (by decide)
  advance_then (cmp_r15b_effect_step (p+2) imm)
  case sub => exact codeRange_slice_subset p (choiceBytes imm) 2 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by simpa [cmpR15bEffect, BitVec.add_assoc] using next 6 (by decide)⟩
  advance_then_on [.ZF] using (setcc_r8_rex_effect_step (p+6) 0x40 0x94 0xc7
    (by simp [RexPrefix]) (Or.inr rfl) rfl)
  case sub => exact codeRange_slice_subset p (choiceBytes imm) 6 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), setccR8Effect_avoids _ _ _ _ _ _, ?_⟩
    simpa [setccR8Effect, BitVec.add_assoc] using next 10 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [choiceEffect, BitVec.add_assoc]
  · x86_norm [choiceEffect, cmpSpec, subSpec, mergeGPR]
    change (if (s.regValue .r15).setWidth 8 = imm.toBitVec then 1#64 else 0#64) =
      X86.Runtime.setSlice
        (((s.regValue .rdi).setWidth 32).setWidth 64 ^^^ ((s.regValue .rdi).setWidth 32).setWidth 64)
        0 8 (if ((s.regValue .r15).setWidth 8 - imm.toBitVec == 0#8) = true then 1#8 else 0#8)
    simp only [BitVec.xor_self, beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
    split <;> rfl
  · intro i; cases i <;> x86_norm [choiceEffect]
    all_goals rfl
  · x86_norm [choiceEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
