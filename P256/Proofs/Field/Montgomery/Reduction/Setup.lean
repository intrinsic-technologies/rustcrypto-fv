import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] mulR64Effect_components

structure FirstSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x113c1b
  readable : MemReadable s ((Operand.reg 6 : Operand 64).read s + 0) 8

def firstSetupBytes : List UInt8 :=
  [0x48,0x89,0xd1,0x4c,0x8b,0x0e,0xbb,0xff,0xff,0xff,0xff,
   0x4c,0x89,0xc8,0x48,0xf7,0xe3,0x49,0x89,0xc0,0x45,0x31,0xf6]

def firstSetupEffect (s : RamState) : Effect :=
  let a := (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s
  { rip := 0x113c32
    writes := [⟨(.reg 1 : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 9 : Operand 64), a⟩, ⟨(.reg 3 : Operand 64), 0xffffffff⟩,
      ⟨(.reg 0 : Operand 64), a*0xffffffff⟩, ⟨(.reg 2 : Operand 64), mulHigh64 a 0xffffffff⟩,
      ⟨(.reg 8 : Operand 64), a*0xffffffff⟩, ⟨(.reg 14 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem first_setup [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FirstSetupPre (codeRange 0x113c1b firstSetupBytes)
      (Effect.post firstSetupEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113c1b firstSetupBytes offset len)
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_r64_effect_step 0x113c1b 0x48 0xd1 (by simp [RexWPrefix]) (by decide)).advances
      ready (code 0 3) pre.rip (next 0x13c1e (by decide))
  change (movR64R64Effect 0x113c1b 1 2 s).Holds s s1 at e1
  have m1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have b1 : (Operand.reg 6 : Operand 64).read s1 = (Operand.reg 6 : Operand 64).read s :=
    e1.agrees.read (by simp)
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_r64_m64_effect_step 0x113c1e 0x4c (by simp [RexWPrefix]) 1 (.base 6 .none)
      (by decide) rfl rfl).advances r1 ((code 3 3).of_external_eq m1)
      ⟨e1.rip, by
        change MemReadable s1 ((Operand.reg 6 : Operand 64).read s1 + 0) 8
        rw [b1]
        exact pre.readable.of_external_eq m1⟩ (next 0x13c21 (by decide))
  change (movR64M64Effect 0x113c1e 9 (.base 6 .none) s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external :=
    (e2.agrees.external (by simp [Component.Covers])).trans m1
  have v2 : (Operand.reg 9 : Operand 64).read s2 =
      (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s := by
    have h := e2.writes
    change (Operand.reg 9 : Operand 64).read s2 =
      memLoad s1.external ((Operand.reg 6 : Operand 64).read s1 + 0) 64 at h
    have b1' := b1
    simp only [BitVec.ofNat_eq_ofNat] at b1' h ⊢
    simpa only [b1', BitVec.add_zero, m1, memLoad_external] using h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r32_imm32_effect_step 0x113c21 0xbb (by decide) 0xffffffff).advances
      r2 ((code 6 5).of_external_eq m2) e2.rip (next 0x13c26 (by decide))
  change (movR32Imm32Effect 0x113c21 5 3 0xffffffff s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external :=
    (e3.agrees.external (by simp [Component.Covers])).trans m2
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_r64_r64_effect_step 0x113c26 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)).advances
      r3 ((code 11 3).of_external_eq m3) e3.rip (next 0x13c29 (by decide))
  change (movR64R64Effect 0x113c26 0 9 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external :=
    (e4.agrees.external (by simp [Component.Covers])).trans m3
  have v4 : (Operand.reg 0 : Operand 64).read s4 =
      (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s :=
    e4.writes.trans ((e3.agrees.read (by simp)).trans v2)
  have b4 : (Operand.reg 3 : Operand 64).read s4 = 0xffffffff :=
    (e4.agrees.read (by simp)).trans e3.writes
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mul_r64_effect_step 0x113c29 0x48 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances
      r4 ((code 14 3).of_external_eq m4) e4.rip (next 0x13c2c (by decide))
  change (mulR64Effect 0x113c29 3 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external :=
    (e5.agrees.external (by simp [Component.Covers])).trans m4
  have v5 := e5.writes
  change (Operand.reg 0 : Operand 64).read s5 =
    (Operand.reg 0 : Operand 64).read s4 * (Operand.reg 3 : Operand 64).read s4 ∧
    (Operand.reg 2 : Operand 64).read s5 =
      mulHigh64 ((Operand.reg 0 : Operand 64).read s4) ((Operand.reg 3 : Operand 64).read s4) at v5
  rw [v4, b4] at v5
  obtain ⟨s6, a6, r6, e6⟩ :=
    (mov_r64_r64_effect_step 0x113c2c 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances
      r5 ((code 17 3).of_external_eq m5) e5.rip (next 0x13c2f (by decide))
  change (movR64R64Effect 0x113c2c 8 0 s5).Holds s5 s6 at e6
  have m6 : s6.external = s.external :=
    (e6.agrees.external (by simp [Component.Covers])).trans m5
  obtain ⟨s7, a7, r7, e7⟩ :=
    (xor_r32_r32_rex_effect_step 0x113c2f 0x45 0xf6 (by simp [RexNoWPrefix]) (by decide)).advances
      r6 ((code 20 3).of_external_eq m6) e6.rip (next 0x13c32 (by decide))
  change (xorR32R32Effect 0x113c2f 3 14 14 s6).Holds s6 s7 at e7
  have m7 : s7.external = s.external :=
    (e7.agrees.external (by simp [Component.Covers])).trans m6
  refine ⟨7, s7, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7,
    r7, loaded.of_external_eq m7, ?_⟩
  refine ⟨e7.rip, ?_, ?_, ?_⟩
  · change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e7.agrees.read (by simp), e6.agrees.read (by simp), e5.agrees.read (by simp),
        e4.agrees.read (by simp), e3.agrees.read (by simp), e2.agrees.read (by simp)]
      exact e1.writes
    · rw [e7.agrees.read (by simp), e6.agrees.read (by simp), e5.agrees.read (by simp),
        e4.agrees.read (by simp), e3.agrees.read (by simp)]
      exact v2
    · rw [e7.agrees.read (by simp), e6.agrees.read (by simp), e5.agrees.read (by simp)]
      exact b4
    · rw [e7.agrees.read (by simp), e6.agrees.read (by simp)]
      exact v5.1
    · rw [e7.agrees.read (by simp), e6.agrees.read (by simp)]
      exact v5.2
    · rw [e7.agrees.read (by simp)]
      exact e6.writes.trans v5.1
    · simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using e7.writes
  · simpa only [firstSetupEffect, xorR32R32Effect, Effect.FlagsHold, BitVec.ofNat_eq_ofNat,
      BitVec.xor_self] using e7.flags
  · exact ((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).mono
      (by
        simp only [movR64R64Effect_components, movR64M64Effect_components,
          movR32Imm32Effect_components, mulR64Effect_components, xorR32R32Effect_components]
        simp [firstSetupEffect, Effect.components])

theorem firstSetup_bytes :
    Extracted.textBytes.toListFrom 0x13c1b firstSetupBytes.length = firstSetupBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
