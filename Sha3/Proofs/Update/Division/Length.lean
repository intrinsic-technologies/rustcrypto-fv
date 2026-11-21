import Sha3.Proofs.Permutation.Code
import Sha3.Proofs.Update.Division.Scalar
import Sha3.Proofs.Arithmetic
import Sha3.Proofs.Image
import Sha3.Proofs.Multiply
import Sha3.Proofs.Run
import Sha3.Proofs.Permutation.LoadStore.Memory
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.Shr.Triple
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import Sha3.Proofs.X86.Instructions.Sub.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm32.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm8.Triple

namespace Sha3.Proofs.Update.Division.Length

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def clobbers (dst : BitVec 5) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg dst, .reg 12, .flags, .rip]

private theorem clobbers_nomem (dst : BitVec 5) :
    ∀ c ∈ clobbers dst, ∀ x, ¬ c.Covers x := by
  simp [clobbers, Component.Covers]

private theorem gpr0_read (s : RamState) : s.GPR[0] =
    (Operand.reg 0 : Operand 64).read s := rfl

private theorem scalar224 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x10098c) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1009ab ∧
      (Operand.reg 13 : Operand 64).read t =
        sha3_224_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      (Operand.reg 12 : Operand 64).read t =
        (Operand.reg 12 : Operand 64).read s -
          sha3_224_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨s1, h1, r1, l1, e1, o1, a1⟩ := advanceScalar
    (effect := movR64Imm64Effect 0x10098c 1 0xe38e38e38e38e38f) (cs := clobbers 13)
    (mov_r64_imm64_effect_step 0x10098c 0x48 0xb9
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xe38e38e38e38e38f)
    (by decide +kernel)
    (by intro t; simp [movR64Imm64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64Imm64Effect])
    (by intro t; simp [movR64Imm64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ready loaded hb ip (Obs.refl s)
  obtain ⟨s2, h2, r2, l2, e2, o2, a2⟩ := advanceScalar
    (effect := movR64R64Effect 0x100996 0 12) (cs := clobbers 13)
    (mov_r64_r64_effect_step 0x100996 0x4c 0xe0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r1 l1 hb (by exact e1.rip) o1
  obtain ⟨s3, h3, r3, l3, e3, o3, a3⟩ := advanceScalar
    (effect := mulR64Effect 0x100999 1) (cs := clobbers 13)
    (mul_r64_effect_step 0x100999 0x48 0xe1
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [mulR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [mulR64Effect, h.read_reg, h.gpr])
    (by intro t; simp [mulR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r2 l2 hb (by exact e2.rip) o2
  obtain ⟨s4, h4, r4, l4, e4, o4, a4⟩ := advanceScalar
    (effect := shrR64Effect 0x10099c 4 2 3) (cs := clobbers 13)
    (shr_r64_imm8_effect_step 0x10099c 0x48 0xea 3
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [shrR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [shrR64Effect, h.read_reg])
    (by intro t; simp [shrR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r3 l3 hb (by exact e3.rip) o3
  obtain ⟨s5, h5, r5, l5, e5, o5, a5⟩ := advanceScalar
    (effect := andR64Imm8Effect 0x1009a0 2 0xf0) (cs := clobbers 13)
    (and_r64_imm8_effect_step 0x1009a0 0x48 0xe2 0xf0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [andR64Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR64Imm8Effect, h.read_reg])
    (by intro t; simp [andR64Imm8Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r4 l4 hb (by exact e4.rip) o4
  obtain ⟨s6, h6, r6, l6, e6, o6, a6⟩ := advanceScalar
    (effect := leaR64Effect 0x1009a4 13 (.sib 2 (some 2) 3 .none)) (cs := clobbers 13)
    (lea_r64_effect_step 0x1009a4 0x4c
      (by unfold RexWPrefix; decide +kernel) 5 (.sib 2 (some 2) 3 .none)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by intro t; simp [leaR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r5 l5 hb (by exact e5.rip) o5
  obtain ⟨s7, h7, r7, l7, e7, o7, a7⟩ := advanceScalar
    (effect := subR64R64Effect 0x1009a8 12 13) (cs := clobbers 13)
    (sub_r64_r64_effect_step 0x1009a8 0x4d 0xec
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [subR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [subR64R64Effect, h.read_reg])
    (by intro t; simp [subR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r6 l6 hb (by exact e6.rip) o6
  have hv12 := (o7.read (Operand.reg 13 : Operand 64) trivial).symm
  have hv15 := (o7.read (Operand.reg 12 : Operand 64) trivial).symm
  x86_norm [movR64Imm64Effect, movR64R64Effect, mulR64Effect, shrR64Effect,
    andR64Imm8Effect, leaR64Effect, subR64R64Effect, gpr0_read] at hv12 hv15
  refine ⟨s7, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))),
    r7, l7, e7.rip, ?_, ?_, ?_⟩
  · simpa only [sha3_224_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8 by decide +kernel,
      BitVec.add_zero, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat] using hv12
  · simpa only [sha3_224_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8 by decide +kernel,
      BitVec.add_zero, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat] using hv15
  · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

private theorem scalar512 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x1000ec) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10010b ∧
      (Operand.reg 13 : Operand 64).read t =
        sha3_512_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      (Operand.reg 12 : Operand 64).read t =
        (Operand.reg 12 : Operand 64).read s -
          sha3_512_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨s1, h1, r1, l1, e1, o1, a1⟩ := advanceScalar
    (effect := movR64Imm64Effect 0x1000ec 1 0xe38e38e38e38e38f) (cs := clobbers 13)
    (mov_r64_imm64_effect_step 0x1000ec 0x48 0xb9
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xe38e38e38e38e38f)
    (by decide +kernel)
    (by intro t; simp [movR64Imm64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64Imm64Effect])
    (by intro t; simp [movR64Imm64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ready loaded hb ip (Obs.refl s)
  obtain ⟨s2, h2, r2, l2, e2, o2, a2⟩ := advanceScalar
    (effect := movR64R64Effect 0x1000f6 0 12) (cs := clobbers 13)
    (mov_r64_r64_effect_step 0x1000f6 0x4c 0xe0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r1 l1 hb (by exact e1.rip) o1
  obtain ⟨s3, h3, r3, l3, e3, o3, a3⟩ := advanceScalar
    (effect := mulR64Effect 0x1000f9 1) (cs := clobbers 13)
    (mul_r64_effect_step 0x1000f9 0x48 0xe1
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [mulR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [mulR64Effect, h.read_reg, h.gpr])
    (by intro t; simp [mulR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r2 l2 hb (by exact e2.rip) o2
  obtain ⟨s4, h4, r4, l4, e4, o4, a4⟩ := advanceScalar
    (effect := shrR64Effect 0x1000fc 4 2 3) (cs := clobbers 13)
    (shr_r64_imm8_effect_step 0x1000fc 0x48 0xea 3
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [shrR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [shrR64Effect, h.read_reg])
    (by intro t; simp [shrR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r3 l3 hb (by exact e3.rip) o3
  obtain ⟨s5, h5, r5, l5, e5, o5, a5⟩ := advanceScalar
    (effect := andR64Imm8Effect 0x100100 2 0xf8) (cs := clobbers 13)
    (and_r64_imm8_effect_step 0x100100 0x48 0xe2 0xf8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [andR64Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR64Imm8Effect, h.read_reg])
    (by intro t; simp [andR64Imm8Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r4 l4 hb (by exact e4.rip) o4
  obtain ⟨s6, h6, r6, l6, e6, o6, a6⟩ := advanceScalar
    (effect := leaR64Effect 0x100104 13 (.sib 2 (some 2) 3 .none)) (cs := clobbers 13)
    (lea_r64_effect_step 0x100104 0x4c
      (by unfold RexWPrefix; decide +kernel) 5 (.sib 2 (some 2) 3 .none)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by intro t; simp [leaR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r5 l5 hb (by exact e5.rip) o5
  obtain ⟨s7, h7, r7, l7, e7, o7, a7⟩ := advanceScalar
    (effect := subR64R64Effect 0x100108 12 13) (cs := clobbers 13)
    (sub_r64_r64_effect_step 0x100108 0x4d 0xec
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [subR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [subR64R64Effect, h.read_reg])
    (by intro t; simp [subR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r6 l6 hb (by exact e6.rip) o6
  have hv12 := (o7.read (Operand.reg 13 : Operand 64) trivial).symm
  have hv15 := (o7.read (Operand.reg 12 : Operand 64) trivial).symm
  x86_norm [movR64Imm64Effect, movR64R64Effect, mulR64Effect, shrR64Effect,
    andR64Imm8Effect, leaR64Effect, subR64R64Effect, gpr0_read] at hv12 hv15
  refine ⟨s7, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))),
    r7, l7, e7.rip, ?_, ?_, ?_⟩
  · simpa only [sha3_512_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8 by decide +kernel,
      BitVec.add_zero, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat] using hv12
  · simpa only [sha3_512_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8 by decide +kernel,
      BitVec.add_zero, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat] using hv15
  · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

private theorem scalar256 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x10066c) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10068e ∧
      (Operand.reg 13 : Operand 64).read t =
        sha3_256_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      (Operand.reg 12 : Operand 64).read t =
        (Operand.reg 12 : Operand 64).read s -
          sha3_256_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨s1, h1, r1, l1, e1, o1, a1⟩ := advanceScalar
    (effect := movR64Imm64Effect 0x10066c 1 0xf0f0f0f0f0f0f0f1) (cs := clobbers 13)
    (mov_r64_imm64_effect_step 0x10066c 0x48 0xb9
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xf0f0f0f0f0f0f0f1)
    (by decide +kernel)
    (by intro t; simp [movR64Imm64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64Imm64Effect])
    (by intro t; simp [movR64Imm64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ready loaded hb ip (Obs.refl s)
  obtain ⟨s2, h2, r2, l2, e2, o2, a2⟩ := advanceScalar
    (effect := movR64R64Effect 0x100676 0 12) (cs := clobbers 13)
    (mov_r64_r64_effect_step 0x100676 0x4c 0xe0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r1 l1 hb (by exact e1.rip) o1
  obtain ⟨s3, h3, r3, l3, e3, o3, a3⟩ := advanceScalar
    (effect := mulR64Effect 0x100679 1) (cs := clobbers 13)
    (mul_r64_effect_step 0x100679 0x48 0xe1
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [mulR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [mulR64Effect, h.read_reg, h.gpr])
    (by intro t; simp [mulR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r2 l2 hb (by exact e2.rip) o2
  obtain ⟨s4, h4, r4, l4, e4, o4, a4⟩ := advanceScalar
    (effect := movR64R64Effect 0x10067c 0 2) (cs := clobbers 13)
    (mov_r64_r64_effect_step 0x10067c 0x48 0xd0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r3 l3 hb (by exact e3.rip) o3
  obtain ⟨s5, h5, r5, l5, e5, o5, a5⟩ := advanceScalar
    (effect := shrR64Effect 0x10067f 4 0 7) (cs := clobbers 13)
    (shr_r64_imm8_effect_step 0x10067f 0x48 0xe8 7
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [shrR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [shrR64Effect, h.read_reg])
    (by intro t; simp [shrR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r4 l4 hb (by exact e4.rip) o4
  obtain ⟨s6, h6, r6, l6, e6, o6, a6⟩ := advanceScalar
    (effect := andR64Imm8Effect 0x100683 2 0x80) (cs := clobbers 13)
    (and_r64_imm8_effect_step 0x100683 0x48 0xe2 0x80
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [andR64Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR64Imm8Effect, h.read_reg])
    (by intro t; simp [andR64Imm8Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r5 l5 hb (by exact e5.rip) o5
  obtain ⟨s7, h7, r7, l7, e7, o7, a7⟩ := advanceScalar
    (effect := leaR64Effect 0x100687 13 (.sib 2 (some 0) 3 .none)) (cs := clobbers 13)
    (lea_r64_effect_step 0x100687 0x4c
      (by unfold RexWPrefix; decide +kernel) 5 (.sib 2 (some 0) 3 .none)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by intro t; simp [leaR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r6 l6 hb (by exact e6.rip) o6
  obtain ⟨s8, h8, r8, l8, e8, o8, a8⟩ := advanceScalar
    (effect := subR64R64Effect 0x10068b 12 13) (cs := clobbers 13)
    (sub_r64_r64_effect_step 0x10068b 0x4d 0xec
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [subR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [subR64R64Effect, h.read_reg])
    (by intro t; simp [subR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r7 l7 hb (by exact e7.rip) o7
  have hv12 := (o8.read (Operand.reg 13 : Operand 64) trivial).symm
  have hv15 := (o8.read (Operand.reg 12 : Operand 64) trivial).symm
  x86_norm [movR64Imm64Effect, movR64R64Effect, mulR64Effect, shrR64Effect,
    andR64Imm8Effect, leaR64Effect, subR64R64Effect, gpr0_read] at hv12 hv15
  refine ⟨s8, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8)))))),
    r8, l8, e8.rip, ?_, ?_, ?_⟩
  · simpa only [sha3_256_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8 by decide +kernel,
      BitVec.add_zero, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat] using hv12
  · simpa only [sha3_256_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8 by decide +kernel,
      BitVec.add_zero, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat] using hv15
  · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans a8))))))).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

private theorem scalar384 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x10039c) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1003b7 ∧
      (Operand.reg 13 : Operand 64).read t =
        sha3_384_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      (Operand.reg 12 : Operand 64).read t =
        (Operand.reg 12 : Operand 64).read s -
          sha3_384_fullBlockBytes ((Operand.reg 12 : Operand 64).read s) ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨s1, h1, r1, l1, e1, o1, a1⟩ := advanceScalar
    (effect := movR64Imm64Effect 0x10039c 1 0x4ec4ec4ec4ec4ec5) (cs := clobbers 13)
    (mov_r64_imm64_effect_step 0x10039c 0x48 0xb9
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0x4ec4ec4ec4ec4ec5)
    (by decide +kernel)
    (by intro t; simp [movR64Imm64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64Imm64Effect])
    (by intro t; simp [movR64Imm64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ready loaded hb ip (Obs.refl s)
  obtain ⟨s2, h2, r2, l2, e2, o2, a2⟩ := advanceScalar
    (effect := movR64R64Effect 0x1003a6 0 12) (cs := clobbers 13)
    (mov_r64_r64_effect_step 0x1003a6 0x4c 0xe0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r1 l1 hb (by exact e1.rip) o1
  obtain ⟨s3, h3, r3, l3, e3, o3, a3⟩ := advanceScalar
    (effect := mulR64Effect 0x1003a9 1) (cs := clobbers 13)
    (mul_r64_effect_step 0x1003a9 0x48 0xe1
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [mulR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [mulR64Effect, h.read_reg, h.gpr])
    (by intro t; simp [mulR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r2 l2 hb (by exact e2.rip) o2
  obtain ⟨s4, h4, r4, l4, e4, o4, a4⟩ := advanceScalar
    (effect := shrR64Effect 0x1003ac 4 2 5) (cs := clobbers 13)
    (shr_r64_imm8_effect_step 0x1003ac 0x48 0xea 5
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [shrR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [shrR64Effect, h.read_reg])
    (by intro t; simp [shrR64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r3 l3 hb (by exact e3.rip) o3
  obtain ⟨s5, h5, r5, l5, e5, o5, a5⟩ := advanceScalar
    (effect := imulR64Imm8Effect 0x1003b0 13 2 104) (cs := clobbers 13)
    (imul_r64_r64_imm8_effect_step 0x1003b0 0x4c 0xea 104
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [imulR64Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [imulR64Imm8Effect, h.read_reg])
    (by intro t; simp [imulR64Imm8Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r4 l4 hb (by exact e4.rip) o4
  obtain ⟨s6, h6, r6, l6, e6, o6, a6⟩ := advanceScalar
    (effect := subR64R64Effect 0x1003b4 12 13) (cs := clobbers 13)
    (sub_r64_r64_effect_step 0x1003b4 0x4d 0xec
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [subR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [subR64R64Effect, h.read_reg])
    (by intro t; simp [subR64R64Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    r5 l5 hb (by exact e5.rip) o5
  have hv12 := (o6.read (Operand.reg 13 : Operand 64) trivial).symm
  have hv15 := (o6.read (Operand.reg 12 : Operand 64) trivial).symm
  x86_norm [movR64Imm64Effect, movR64R64Effect, mulR64Effect, shrR64Effect,
    imulR64Imm8Effect, subR64R64Effect, gpr0_read] at hv12 hv15
  refine ⟨s6, h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))),
    r6, l6, e6.rip, ?_, ?_, ?_⟩
  · simpa only [sha3_384_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.reduceToNat, BitVec.ofNat_eq_ofNat,
      show (104 : UInt8).toBitVec.signExtend 64 = 104 by decide +kernel] using hv12
  · simpa only [sha3_384_fullBlockBytes, mulHigh64_eq, mul64Hi,
      BitVec.reduceToNat, BitVec.ofNat_eq_ofNat,
      show (104 : UInt8).toBitVec.signExtend 64 = 104 by decide +kernel] using hv15
  · apply (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6))))).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

structure Registers (rate : Nat) (dst : BitVec 5) (n : BitVec 64) (t : RamState) : Prop where
  full : (Operand.reg dst : Operand 64).read t = BitVec.ofNat 64 (rate * (n.toNat / rate))
  remaining : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (n.toNat % rate)
  comparison : (StatusFlagsOutcome.ofStatusFlags
    (cmpSpec (BitVec.ofNat 64 (rate * (n.toNat / rate))) (BitVec.ofNat 64 rate))).Allows
      (StatusFlags.ofRFLAGS t.RFLAGS)

theorem sha3_224_length_setup [Bindings] (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x10098c)
    (input : (Operand.reg 12 : Operand 64).read s = n) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1009b2 ∧ Registers 144 13 n t ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨u, hu, ru, lu, ipu, full, remaining, frame⟩ :=
    scalar224 boundary s ready loaded hb ip
  obtain ⟨t, ht, rt, lt, et, _, frameT⟩ := advanceScalar
    (effect := cmpR64Imm32Effect 0x1009ab 13 144) (cs := clobbers 13)
    (cmp_r64_imm32_effect_step 0x1009ab 0x49 0xfd 144
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [cmpR64Imm32Effect])
    (by intro a b h; rfl)
    (by intro t; simp [cmpR64Imm32Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ru lu hb ipu (Obs.refl u)
  have preserved (r : BitVec 5) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u :=
    et.agrees.read (by simp [cmpR64Imm32Effect_components])
  have hf : (Operand.reg 13 : Operand 64).read u =
      BitVec.ofNat 64 (144 * (n.toNat / 144)) := by
    rw [full, input, sha3_224_fullBlockBytes_eq n hn]
  refine ⟨t, hu.trans ht, rt, lt, et.rip, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (preserved 13).trans hf
  · rw [preserved, remaining, input, sha3_224_remaining n hn]
  · have flags : (StatusFlagsOutcome.ofStatusFlags
        (cmpSpec ((Operand.reg 13 : Operand 64).read u) 144)).Allows
          (StatusFlags.ofRFLAGS t.RFLAGS) := et.flags
    rw [hf] at flags
    exact flags
  · apply (frame.trans frameT).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

theorem sha3_256_length_setup [Bindings] (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x10066c)
    (input : (Operand.reg 12 : Operand 64).read s = n) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x100695 ∧ Registers 136 13 n t ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨u, hu, ru, lu, ipu, full, remaining, frame⟩ :=
    scalar256 boundary s ready loaded hb ip
  obtain ⟨t, ht, rt, lt, et, _, frameT⟩ := advanceScalar
    (effect := cmpR64Imm32Effect 0x10068e 13 136) (cs := clobbers 13)
    (cmp_r64_imm32_effect_step 0x10068e 0x49 0xfd 136
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [cmpR64Imm32Effect])
    (by intro a b h; rfl)
    (by intro t; simp [cmpR64Imm32Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ru lu hb ipu (Obs.refl u)
  have preserved (r : BitVec 5) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u :=
    et.agrees.read (by simp [cmpR64Imm32Effect_components])
  have hf : (Operand.reg 13 : Operand 64).read u =
      BitVec.ofNat 64 (136 * (n.toNat / 136)) := by
    rw [full, input, sha3_256_fullBlockBytes_eq n hn]
  refine ⟨t, hu.trans ht, rt, lt, et.rip, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (preserved 13).trans hf
  · rw [preserved, remaining, input, sha3_256_remaining n hn]
  · have flags : (StatusFlagsOutcome.ofStatusFlags
        (cmpSpec ((Operand.reg 13 : Operand 64).read u) 136)).Allows
          (StatusFlags.ofRFLAGS t.RFLAGS) := et.flags
    rw [hf] at flags
    exact flags
  · apply (frame.trans frameT).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

theorem sha3_384_length_setup [Bindings] (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x10039c)
    (input : (Operand.reg 12 : Operand 64).read s = n) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1003bb ∧ Registers 104 13 n t ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨u, hu, ru, lu, ipu, full, remaining, frame⟩ :=
    scalar384 boundary s ready loaded hb ip
  obtain ⟨t, ht, rt, lt, et, _, frameT⟩ := advanceScalar
    (effect := cmpR64Imm8Effect 0x1003b7 13 104) (cs := clobbers 13)
    (cmp_r64_imm8_effect_step 0x1003b7 0x49 0xfd 104
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [cmpR64Imm8Effect])
    (by intro a b h; rfl)
    (by intro t; simp [cmpR64Imm8Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ru lu hb ipu (Obs.refl u)
  have preserved (r : BitVec 5) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u :=
    et.agrees.read (by simp [cmpR64Imm8Effect_components])
  have hf : (Operand.reg 13 : Operand 64).read u =
      BitVec.ofNat 64 (104 * (n.toNat / 104)) := by
    rw [full, input, sha3_384_fullBlockBytes_eq n hn]
  refine ⟨t, hu.trans ht, rt, lt, et.rip, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (preserved 13).trans hf
  · rw [preserved, remaining, input, sha3_384_remaining n hn]
  · have flags : (StatusFlagsOutcome.ofStatusFlags
        (cmpSpec ((Operand.reg 13 : Operand 64).read u) 104)).Allows
          (StatusFlags.ofRFLAGS t.RFLAGS) := et.flags
    rw [hf] at flags
    exact flags
  · apply (frame.trans frameT).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

theorem sha3_512_length_setup [Bindings] (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = 0x1000ec)
    (input : (Operand.reg 12 : Operand 64).read s = n) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10010f ∧ Registers 72 13 n t ∧
      AgreesExcept (clobbers 13) s t := by
  obtain ⟨u, hu, ru, lu, ipu, full, remaining, frame⟩ :=
    scalar512 boundary s ready loaded hb ip
  obtain ⟨t, ht, rt, lt, et, _, frameT⟩ := advanceScalar
    (effect := cmpR64Imm8Effect 0x10010b 13 72) (cs := clobbers 13)
    (cmp_r64_imm8_effect_step 0x10010b 0x49 0xfd 72
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (by intro t; simp [cmpR64Imm8Effect])
    (by intro a b h; rfl)
    (by intro t; simp [cmpR64Imm8Effect, Effect.components, clobbers])
    (clobbers_nomem 13) (by
      intro t
      dsimp only [movR64Imm64Effect, movR64R64Effect, mulR64Effect,
      shrR64Effect, andR64Imm8Effect, leaR64Effect, subR64R64Effect, imulR64Imm8Effect,
      cmpR64Imm32Effect, cmpR64Imm8Effect]
      apply Permutation.inProgram_permutation_address <;> decide +kernel)
    ru lu hb ipu (Obs.refl u)
  have preserved (r : BitVec 5) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u :=
    et.agrees.read (by simp [cmpR64Imm8Effect_components])
  have hf : (Operand.reg 13 : Operand 64).read u =
      BitVec.ofNat 64 (72 * (n.toNat / 72)) := by
    rw [full, input, sha3_512_fullBlockBytes_eq n hn]
  refine ⟨t, hu.trans ht, rt, lt, et.rip, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (preserved 13).trans hf
  · rw [preserved, remaining, input, sha3_512_remaining n hn]
  · have flags : (StatusFlagsOutcome.ofStatusFlags
        (cmpSpec ((Operand.reg 13 : Operand 64).read u) 72)).Allows
          (StatusFlags.ofRFLAGS t.RFLAGS) := et.flags
    rw [hf] at flags
    exact flags
  · apply (frame.trans frameT).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

end Sha3.Proofs.Update.Division.Length
