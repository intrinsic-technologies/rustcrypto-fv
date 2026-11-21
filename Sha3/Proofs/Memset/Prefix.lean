import Sha3.Proofs.Memset.Basic
import Sha3.Proofs.Multiply
import Sha3.Proofs.Scalar.Move.Triple
import Sha3.Proofs.Scalar.Neg
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.Shr.Triple
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Sub.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Triple

namespace Sha3.Proofs.Memset

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

private theorem scalarClobbers_nomem :
    ∀ c ∈ scalarClobbers, ∀ x, ¬ c.Covers x := by
  simp [scalarClobbers, Component.Covers]

private theorem scalarClobbers_nosp : Component.reg 4 ∉ scalarClobbers := by
  decide +kernel

private theorem prefixAdvance [Bindings] {boundary : ReturnBoundary}
    {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect}
    {model s : RamState} {ws : List Write}
    (step : StepEffect (fun s ↦ s.RIP = p) (codeRange p bytes) effect)
    (hmem : (p, bytes) ∈ instructionBytes)
    (full : ∀ w ∈ ws, w.Full)
    (writes : (effect s).writes = ws)
    (frame : ∀ c ∈ (effect s).components, c ∈ scalarClobbers)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s)
    (sp : s.GPR[4] ≠ boundary.rsp) (ip : s.RIP = p) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.GPR[4] ≠ boundary.rsp ∧ (effect s).Holds s t ∧
      Obs (applyWrites model ws) t ∧ AgreesExcept scalarClobbers s t := by
  obtain ⟨t, ht, hr, he⟩ := step s ready (instruction_codeIn code hmem) ip
  have ha : AgreesExcept scalarClobbers s t := he.agrees.mono frame
  have hsp : t.GPR[4] = s.GPR[4] := ha.agree (.reg 4) scalarClobbers_nosp rfl
  have hcode : CodeIn Extracted.programImage t := code.of_external_eq (ha.external scalarClobbers_nomem)
  refine ⟨t, Advances.of_step ht (.inr (hsp ▸ sp)), hr, hcode, hsp ▸ sp, he, ?_, ha⟩
  rw [← writes]
  exact he.obs obs (by simpa only [writes] using full)

private theorem aligned_neg_mask (x : BitVec 64) (h : x.toNat % 8 = 0) :
    (-x.setWidth 32) &&& 7#32 = 0 := by
  have h3 : x.setWidth 3 = 0#3 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_setWidth, Nat.reducePow, BitVec.toNat_ofNat, Nat.zero_mod] using h
  have hn : (-x.setWidth 32).setWidth 3 = 0#3 := by
    rw [BitVec.setWidth_neg_of_le (by decide), BitVec.setWidth_setWidth (by decide), h3]
    rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (-x.setWidth 32).toNat &&& (2^3 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact congrArg BitVec.toNat hn


theorem prefix_steps_general [Bindings] {tail : Nat} (htail : tail ≤ 1) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = 0x106a20)
    (hrdx : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 (200 + tail))
    (hrsi : (Operand.reg 6 : Operand 64).read s = 0)
    (halign : ((Operand.reg 7 : Operand 64).read s).toNat % 8 = 0)
    (boundary : ReturnBoundary) (hsp : s.GPR[4] ≠ boundary.rsp) :
    ∃ t, Advances boundary 14 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ PrefixPost s t tail := by
  have hshift : BitVec.ofNat 64 (200 + tail) >>> 3 = 25 := by
    have : tail = 0 ∨ tail = 1 := by omega
    rcases this with rfl | rfl <;> decide +kernel
  have htailmask : ((BitVec.ofNat 64 (200 + tail)).setWidth 32 &&& 7#32).setWidth 64 =
      BitVec.ofNat 64 tail := by
    have : tail = 0 ∨ tail = 1 := by omega
    rcases this with rfl | rfl <;> decide +kernel
  have hsil : (Operand.reg 6 : Operand 8).read s = 0 := by
    change ((Operand.reg 6 : Operand 64).read s).setWidth 8 = 0
    rw [hrsi]
    rfl
  x86_norm at hsil
  obtain ⟨s1, a1, r1, c1, b1, e1, o1, f1⟩ := prefixAdvance
    (effect := movR64R64Effect 0x106a20 8 2)
    (ws := [⟨(Operand.reg 8 : Operand 64), BitVec.ofNat 64 (200 + tail)⟩])
    (mov_r64_r64_effect_step 0x106a20 0x49 0xd0
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [movR64R64Effect, hrdx])
    (by simp [movR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    hready hcode hsp hrip (Obs.refl s)
  obtain ⟨s2, a2, r2, c2, b2, e2, o2, f2⟩ := prefixAdvance
    (effect := movR64R64Effect 0x106a23 2 7)
    (ws := [⟨(Operand.reg 2 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩])
    (mov_r64_r64_effect_step 0x106a23 0x48 0xfa
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [movR64R64Effect]; rw [← o1.read (Operand.reg 7 : Operand 64) trivial]; x86_norm)
    (by simp [movR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r1 c1 b1 e1.rip o1
  obtain ⟨s3, a3, r3, c3, b3, e3, o3, f3⟩ := prefixAdvance
    (ws := [⟨(Operand.reg 1 : Operand 64), 0⟩])
    (movzx_ecx_sil_effect_step 0x106a26)
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [movzxR32R8Effect]; rw [← o2.read (Operand.reg 6 : Operand 8) trivial]; x86_norm [hsil, BitVec.setWidth_zero])
    (by simp [movzxR32R8Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r2 c2 b2 e2.rip o2
  obtain ⟨s4, a4, r4, c4, b4, e4, o4, f4⟩ := prefixAdvance
    (effect := movR64Imm64Effect 0x106a2a 0 0x0101010101010101)
    (ws := [⟨(Operand.reg 0 : Operand 64), 0x0101010101010101⟩])
    (mov_r64_imm64_effect_step 0x106a2a 0x48 0xb8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0x0101010101010101)
    (by decide +kernel) (by simp [Write.Full, Operand.Full]) rfl
    (by simp [movR64Imm64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r3 c3 b3 e3.rip o3
  obtain ⟨s5, a5, r5, c5, b5, e5, o5, f5⟩ := prefixAdvance
    (effect := imulR64R64Effect 0x106a34 0 1)
    (ws := [⟨(Operand.reg 0 : Operand 64), 0⟩])
    (imul_r64_r64_effect_step 0x106a34 0x48 0xc1
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [imulR64R64Effect]; rw [← o4.read (Operand.reg 0 : Operand 64) trivial, ← o4.read (Operand.reg 1 : Operand 64) trivial]; x86_norm [BitVec.mul_zero])
    (by simp [imulR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r4 c4 b4 e4.rip o4
  obtain ⟨s6, a6, r6, c6, b6, e6, o6, f6⟩ := prefixAdvance
    (effect := movR32R32Effect 0x106a38 2 1 2)
    (ws := [⟨(Operand.reg 1 : Operand 64), (((Operand.reg 7 : Operand 64).read s).setWidth 32).setWidth 64⟩])
    (mov_r32_r32_effect_step 0x106a38 0xd1 (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [movR32R32Effect]; rw [← o5.read (Operand.reg 2 : Operand 32) trivial]; x86_norm)
    (by simp [movR32R32Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r5 c5 b5 e5.rip o5
  obtain ⟨s7, a7, r7, c7, b7, e7, o7, f7⟩ := prefixAdvance
    (effect := negEcxEffect 0x106a3a)
    (ws := [⟨(Operand.reg 1 : Operand 64), (-((Operand.reg 7 : Operand 64).read s).setWidth 32).setWidth 64⟩])
    (neg_ecx_effect_step 0x106a3a)
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [negEcxEffect, negR32Effect]; rw [← o6.read (Operand.reg 1 : Operand 32) trivial]; x86_norm [BitVec.setWidth_setWidth_of_le])
    (by simp [negEcxEffect, negR32Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r6 c6 b6 e6.rip o6
  have hmask := aligned_neg_mask ((Operand.reg 7 : Operand 64).read s) halign
  x86_norm at hmask
  obtain ⟨s8, a8, r8, c8, b8, e8, o8, f8⟩ := prefixAdvance
    (effect := andR32Imm8Effect 0x106a3c 3 1 7)
    (ws := [⟨(Operand.reg 1 : Operand 64), 0⟩])
    (and_r32_imm8_effect_step 0x106a3c 0xe1 7 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [andR32Imm8Effect]; rw [← o7.read (Operand.reg 1 : Operand 32) trivial]; x86_norm [BitVec.setWidth_setWidth_of_le, hmask, BitVec.setWidth_zero])
    (by simp [andR32Imm8Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r7 c7 b7 e7.rip o7
  obtain ⟨s9, a9, r9, c9, b9, e9, o9, f9⟩ := prefixAdvance
    (effect := cmpR64R64Effect 0x106a3f 8 1) (ws := [])
    (cmp_r64_r64_effect_step 0x106a3f 0x49 0xc8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp) rfl
    (by simp [cmpR64R64Effect, Effect.components, scalarClobbers])
    r8 c8 b8 e8.rip o8
  have hcf : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = false := by
    have h := e9.flag .CF
    change (StatusFlags.ofRFLAGS s9.RFLAGS).CF =
      (cmpSpec ((Operand.reg 8 : Operand 64).read s8) ((Operand.reg 1 : Operand 64).read s8)).CF at h
    rw [← o8.read (Operand.reg 8 : Operand 64) trivial, ← o8.read (Operand.reg 1 : Operand 64) trivial] at h
    x86_norm [cmpSpec, subSpec] at h
    exact h
  obtain ⟨s10, a10, r10, c10, b10, e10, o10, f10⟩ := prefixAdvance
    (ws := [⟨(Operand.reg 1 : Operand 64), 0⟩])
    (cmovb_rcx_r8_effect_step 0x106a42)
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [cmovbR64R64Effect, hcf, Bool.false_eq_true, ↓reduceIte]; rw [← o9.read (Operand.reg 1 : Operand 64) trivial]; x86_norm)
    (by simp [cmovbR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r9 c9 b9 e9.rip o9
  obtain ⟨s11, a11, r11, c11, b11, e11, o11, f11⟩ := prefixAdvance
    (effect := subR64R64Effect 0x106a46 8 1)
    (ws := [⟨(Operand.reg 8 : Operand 64), BitVec.ofNat 64 (200 + tail)⟩])
    (sub_r64_r64_effect_step 0x106a46 0x49 0xc8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [subR64R64Effect]; rw [← o10.read (Operand.reg 8 : Operand 64) trivial, ← o10.read (Operand.reg 1 : Operand 64) trivial]; x86_norm [BitVec.sub_zero])
    (by simp [subR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r10 c10 b10 e10.rip o10
  obtain ⟨s12, a12, r12, c12, b12, e12, o12, f12⟩ := prefixAdvance
    (effect := movR64R64Effect 0x106a49 6 8)
    (ws := [⟨(Operand.reg 6 : Operand 64), BitVec.ofNat 64 (200 + tail)⟩])
    (mov_r64_r64_effect_step 0x106a49 0x4c 0xc6
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [movR64R64Effect]; rw [← o11.read (Operand.reg 8 : Operand 64) trivial]; x86_norm)
    (by simp [movR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r11 c11 b11 e11.rip o11
  obtain ⟨s13, a13, r13, c13, b13, e13, o13, f13⟩ := prefixAdvance
    (effect := shrR64Effect 0x106a4c 4 6 3)
    (ws := [⟨(Operand.reg 6 : Operand 64), 25⟩])
    (shr_r64_imm8_effect_step 0x106a4c 0x48 0xee 3
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [shrR64Effect]; rw [← o12.read (Operand.reg 6 : Operand 64) trivial]; x86_norm [hshift])
    (by simp [shrR64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r12 c12 b12 e12.rip o12
  obtain ⟨s14, a14, r14, c14, b14, e14, o14, f14⟩ := prefixAdvance
    (effect := andR32Imm8Effect 0x106a50 4 8 7)
    (ws := [⟨(Operand.reg 8 : Operand 64), BitVec.ofNat 64 tail⟩])
    (and_r32_imm8_rex_effect_step 0x106a50 0x41 0xe0 7
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by simp only [andR32Imm8Effect]; rw [← o13.read (Operand.reg 8 : Operand 32) trivial]; x86_norm [htailmask])
    (by simp [andR32Imm8Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r13 c13 b13 e13.rip o13
  refine ⟨s14, ?_, r14, c14, e14.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans
      (a9.trans (a10.trans (a11.trans (a12.trans (a13.trans a14))))))))))))
  · rw [← o14.read (Operand.reg 0 : Operand 64) trivial]; x86_norm
  · rw [← o14.read (Operand.reg 1 : Operand 64) trivial]; x86_norm
  · rw [← o14.read (Operand.reg 2 : Operand 64) trivial]; x86_norm
  · rw [← o14.read (Operand.reg 6 : Operand 64) trivial]; x86_norm
  · rw [← o14.read (Operand.reg 8 : Operand 64) trivial]; x86_norm
  · exact (f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (f6.trans (f7.trans (f8.trans
      (f9.trans (f10.trans (f11.trans (f12.trans (f13.trans f14))))))))))))).mono
      (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem prefix_steps [Bindings] (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = 0x106a20)
    (hrdx : (Operand.reg 2 : Operand 64).read s = 201)
    (hrsi : (Operand.reg 6 : Operand 64).read s = 0)
    (halign : ((Operand.reg 7 : Operand 64).read s).toNat % 8 = 0)
    (boundary : ReturnBoundary) (hsp : s.GPR[4] ≠ boundary.rsp) :
    ∃ t, Advances boundary 14 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ PrefixPost s t :=
  prefix_steps_general (tail := 1) (by decide) s hready hcode hrip hrdx hrsi halign boundary hsp

end Sha3.Proofs.Memset
