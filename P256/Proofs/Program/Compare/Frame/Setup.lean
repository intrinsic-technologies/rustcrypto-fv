import P256.Proofs.Program.Compare.Block

namespace P256.Proofs.Program.Compare.Frame

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program.Compare.Block

def setupBytes : List UInt8 :=
  [0x48, 0x89, 0xd1, 0x48, 0x89, 0xf2, 0x48, 0x89, 0xfe,
   0x49, 0x89, 0xc8, 0x49, 0x83, 0xe0, 0xf0]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x11c87f
    writes := [⟨.reg 1, (Operand.reg 2 : Operand 64).read s⟩,
      ⟨.reg 2, (Operand.reg 6 : Operand 64).read s⟩,
      ⟨.reg 6, (Operand.reg 7 : Operand 64).read s⟩,
      ⟨.reg 8, (Operand.reg 2 : Operand 64).read s &&& (0xf0#8).signExtend 64⟩]
    flags := some (andFlags ((Operand.reg 2 : Operand 64).read s &&& (0xf0#8).signExtend 64)) }

theorem setup [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ ip : BitVec 64, 0x11c86f ≤ ip.toNat → ip.toNat ≤ 0x11c87f →
      ip ≠ boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x11c86f)
      (codeRange 0x11c86f setupBytes) setupEffect := by
  have h₀ : StepEffect (fun s ↦ s.RIP = (0x11c86f + 0))
      (codeRange (0x11c86f + 0) [0x48, 0x89, 0xd1])
      (movR64R64Effect (0x11c86f + 0) 1 2) := mov_r64_r64_effect_step (0x11c86f : BitVec 64) 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  have h₁ : StepEffect (fun s ↦ s.RIP = (0x11c86f + 3))
      (codeRange (0x11c86f + 3) [0x48, 0x89, 0xf2])
      (movR64R64Effect (0x11c86f + 3) 2 6) := mov_r64_r64_effect_step (0x11c86f + 3 : BitVec 64) 0x48 0xf2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  have h₂ : StepEffect (fun s ↦ s.RIP = (0x11c86f + 6))
      (codeRange (0x11c86f + 6) [0x48, 0x89, 0xfe])
      (movR64R64Effect (0x11c86f + 6) 6 7) := mov_r64_r64_effect_step (0x11c86f + 6 : BitVec 64) 0x48 0xfe
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  have h₃ : StepEffect (fun s ↦ s.RIP = (0x11c86f + 9))
      (codeRange (0x11c86f + 9) [0x49, 0x89, 0xc8])
      (movR64R64Effect (0x11c86f + 9) 8 1) := mov_r64_r64_effect_step (0x11c86f + 9 : BitVec 64) 0x49 0xc8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  have h₄ : StepEffect (fun s ↦ s.RIP = (0x11c86f + 12))
      (codeRange (0x11c86f + 12) [0x49, 0x83, 0xe0, 0xf0])
      (andR64Imm8Effect (0x11c86f + 12) 8 0xf0) := and_r64_imm8_effect_step (0x11c86f + 12 : BitVec 64) 0x49 0xe0 0xf0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)
  p256_memcmp_block_begin h₀
  p256_memcmp_block_then h₁
  p256_memcmp_block_then h₂
  p256_memcmp_block_then h₃
  p256_memcmp_block_then h₄
  p256_memcmp_block_finish [setupEffect]
  all_goals
    intro s hP
    apply outside
    all_goals dsimp only [movR64R64Effect, andR64Imm8Effect]
    all_goals decide +kernel

end P256.Proofs.Program.Compare.Frame
