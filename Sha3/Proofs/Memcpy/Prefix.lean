import Sha3.Proofs.Memcpy.Basic
import Sha3.Proofs.Memcpy.Scalar
import Sha3.Proofs.Scalar.Move.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Triple

namespace Sha3.Proofs.Memcpy

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

theorem neg_mask (x : BitVec 64) :
    ((-x.setWidth 32) &&& 7#32).setWidth 64 = BitVec.ofNat 64 ((-x).toNat % 8) := by
  rw [← BitVec.setWidth_neg_of_le (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((-x).toNat % 2^32 &&& (2^3-1)) % 2^64 = (-x).toNat % 8 % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  exact Nat.mod_mod_of_dvd _ (by decide)

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


theorem prefix_steps_general [Bindings] {len lead : BitVec 64} (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = 0x106a70)
    (hrdx : (Operand.reg 2 : Operand 64).read s = len)
    (hmask : ((-((Operand.reg 7 : Operand 64).read s).setWidth 32) &&& 7#32).setWidth 64 = lead)
    (hle : lead.toNat ≤ len.toNat)
    (boundary : ReturnBoundary) (hsp : s.GPR[4] ≠ boundary.rsp) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ PrefixPost s t len lead := by
  obtain ⟨s1, a1, r1, c1, b1, e1, o1, f1⟩ := prefixAdvance
    (effect := movR64R64Effect 0x106a70 0 7)
    (ws := [⟨(Operand.reg 0 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩])
    (mov_r64_r64_effect_step 0x106a70 0x48 0xf8
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full]) rfl
    (by simp [movR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    hready hcode hsp hrip (Obs.refl s)
  obtain ⟨s2, a2, r2, c2, b2, e2, o2, f2⟩ := prefixAdvance
    (effect := movR32R32Effect 0x106a73 3 8 0)
    (ws := [⟨(Operand.reg 8 : Operand 64),
      (((Operand.reg 7 : Operand 64).read s).setWidth 32).setWidth 64⟩])
    (mov_r32_r32_rex_effect_step 0x106a73 0x41 0xc0
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by
      simp only [movR32R32Effect]
      rw [← o1.read (Operand.reg 0 : Operand 32) trivial]
      x86_norm)
    (by simp [movR32R32Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r1 c1 b1 e1.rip o1
  obtain ⟨s3, a3, r3, c3, b3, e3, o3, f3⟩ := prefixAdvance
    (effect := negR32RexEffect 0x106a76 8)
    (ws := [⟨(Operand.reg 8 : Operand 64),
      (-((Operand.reg 7 : Operand 64).read s).setWidth 32).setWidth 64⟩])
    (neg_r32_rex_effect_step 0x106a76 0x41 0xd8
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by
      simp only [negR32RexEffect, negR32Effect]
      rw [← o2.read (Operand.reg 8 : Operand 32) trivial]
      x86_norm [BitVec.setWidth_setWidth_of_le])
    (by simp [negR32RexEffect, negR32Effect, Effect.components, scalarClobbers,
      Write.component, Operand.component])
    r2 c2 b2 e2.rip o2
  x86_norm at hmask
  obtain ⟨s4, a4, r4, c4, b4, e4, o4, f4⟩ := prefixAdvance
    (effect := andR32Imm8Effect 0x106a79 4 8 7)
    (ws := [⟨(Operand.reg 8 : Operand 64), lead⟩])
    (and_r32_imm8_rex_effect_step 0x106a79 0x41 0xe0 7
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by
      simp only [andR32Imm8Effect]
      rw [← o3.read (Operand.reg 8 : Operand 32) trivial]
      x86_norm [BitVec.setWidth_setWidth_of_le, hmask, BitVec.setWidth_zero])
    (by simp [andR32Imm8Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r3 c3 b3 e3.rip o3
  obtain ⟨s5, a5, r5, c5, b5, e5, o5, f5⟩ := prefixAdvance
    (effect := cmpR64R64Effect 0x106a7d 2 8) (ws := [])
    (cmp_r64_r64_effect_step 0x106a7d 0x4c 0xc2
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp) rfl
    (by simp [cmpR64R64Effect, Effect.components, scalarClobbers])
    r4 c4 b4 e4.rip o4
  have hcf : (StatusFlags.ofRFLAGS s5.RFLAGS).CF = false := by
    have h := e5.flag .CF
    change (StatusFlags.ofRFLAGS s5.RFLAGS).CF =
      (cmpSpec ((Operand.reg 2 : Operand 64).read s4)
        ((Operand.reg 8 : Operand 64).read s4)).CF at h
    rw [← o4.read (Operand.reg 2 : Operand 64) trivial,
      ← o4.read (Operand.reg 8 : Operand 64) trivial] at h
    x86_norm [cmpSpec, subSpec] at h
    x86_norm at hrdx
    simpa only [hrdx, show ¬ len.toNat < lead.toNat from Nat.not_lt.mpr hle, decide_false] using h
  obtain ⟨s6, a6, r6, c6, b6, e6, o6, f6⟩ := prefixAdvance
    (effect := cmovbR64R64Effect 0x106a80 8 2)
    (ws := [⟨(Operand.reg 8 : Operand 64), lead⟩])
    (cmovb_r64_r64_effect_step 0x106a80 0x4c 0xc2
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by
      simp only [cmovbR64R64Effect, hcf, Bool.false_eq_true, ↓reduceIte]
      rw [← o5.read (Operand.reg 8 : Operand 64) trivial]
      x86_norm)
    (by simp [cmovbR64R64Effect, Effect.components, scalarClobbers,
      Write.component, Operand.component])
    r5 c5 b5 e5.rip o5
  obtain ⟨s7, a7, r7, c7, b7, e7, o7, f7⟩ := prefixAdvance
    (effect := movR64R64Effect 0x106a84 1 8)
    (ws := [⟨(Operand.reg 1 : Operand 64), lead⟩])
    (mov_r64_r64_effect_step 0x106a84 0x4c 0xc1
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp [Write.Full, Operand.Full])
    (by
      simp only [movR64R64Effect]
      rw [← o6.read (Operand.reg 8 : Operand 64) trivial]
      x86_norm)
    (by simp [movR64R64Effect, Effect.components, scalarClobbers, Write.component, Operand.component])
    r6 c6 b6 e6.rip o6
  refine ⟨s7, ?_, r7, c7, e7.rip, ?_, ?_, ?_, ?_, ?_⟩
  · exact a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))
  · rw [← o7.read (Operand.reg 0 : Operand 64) trivial]; x86_norm
  · rw [← o7.read (Operand.reg 1 : Operand 64) trivial]; x86_norm
  · rw [← o7.read (Operand.reg 8 : Operand 64) trivial]; x86_norm
  · rw [← o7.read (Operand.reg 2 : Operand 64) trivial]; x86_norm; exact hrdx
  · exact (f1.trans (f2.trans (f3.trans (f4.trans (f5.trans (f6.trans f7)))))).mono
      (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem prefix_steps [Bindings] (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = 0x106a70)
    (hrdx : (Operand.reg 2 : Operand 64).read s = 208)
    (halign : ((Operand.reg 7 : Operand 64).read s).toNat % 8 = 0)
    (boundary : ReturnBoundary) (hsp : s.GPR[4] ≠ boundary.rsp) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ PrefixPost s t := by
  apply prefix_steps_general s hready hcode hrip hrdx _ (by decide) boundary hsp
  rw [aligned_neg_mask _ halign]
  rfl

theorem neg_mask_nat (x : BitVec 64) :
    ((-x.setWidth 32) &&& 7#32).setWidth 64 =
      BitVec.ofNat 64 ((8 - x.toNat % 8) % 8) := by
  rw [neg_mask]
  congr 1
  rw [BitVec.toNat_neg]
  have hx := x.isLt
  omega

theorem add_lead_aligned (x : BitVec 64) :
    (x + BitVec.ofNat 64 ((8 - x.toNat % 8) % 8)).toNat % 8 = 0 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Sha3.Proofs.Memcpy
