import Sha3.Proofs.Update.Partial.ShortControl
import Sha3.Proofs.Update.Partial.CursorAdd

namespace Sha3.Proofs.Update.Partial.Short

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

private theorem dispatchAdvance [Bindings] {v : Variant} {boundary : ReturnBoundary} {s model : RamState}
    {p : BitVec 64} {bytes : List UInt8} {pre : RamState → Prop} {effect : RamState → Effect}
    (step : StepEffect pre (codeRange p bytes) effect)
    (image : (p, bytes) ∈ instructionBytes v)
    (full : ∀ t, ∀ w ∈ (effect t).writes, w.Full)
    (localWrites : ∀ a b, Obs a b → (effect a).writes = (effect b).writes)
    (frame : ∀ c ∈ (effect s).components, c ∈ clobbers)
    (next : 0x100000 ≤ (effect s).rip.toNat ∧ (effect s).rip.toNat ≤ 0x106222)
    (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (hp : pre s) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ (effect s).Holds s t ∧
      Obs (applyWrites model (effect model).writes) t ∧ AgreesExcept clobbers s t := by
  obtain ⟨t, ht, hr, hl, he, ho, hf⟩ := scalar_model_advance step image full localWrites frame
    clobbers_nomem (Permutation.inProgram_permutation_address next.1 next.2)
    ready loaded sp hp obs
  exact ⟨t, ht, hr, hl, sp, he, ho, hf⟩

def zeroDisp : Variant → BitVec 32
  | .sha224 | .sha256 => 0x2cf
  | .sha384 => 0x27f
  | .sha512 => 0x25f

def jaeDisp : Variant → BitVec 32
  | .sha224 | .sha256 => 0x244
  | .sha384 => 0x1f4
  | .sha512 => 0x1d4

def shortDisp : Variant → BitVec 32
  | .sha224 | .sha256 => 0x290
  | .sha384 => 0x240
  | .sha512 => 0x220

section TestBranch

variable [Bindings] {v : Variant} {boundary : ReturnBoundary} {p : BitVec 64}
    {reg : BitVec 5} {rex modrm : UInt8} {len : Nat} {bytes : List UInt8} {off : BitVec 64}

private theorem test_branch
    (testStep : StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0x85, modrm])
      (testR64R64Effect p reg reg))
    (image₁ : (p, [rex, 0x85, modrm]) ∈ instructionBytes v)
    (branchStep : StepEffect (fun s ↦ s.RIP = p + 3#64 ∧
      (condHolds 4 (StatusFlags.ofRFLAGS s.RFLAGS) = true →
        (branchTarget (p + 3#64) len off).toNat < 2^32))
      (codeRange (p + 3#64) bytes) (jccEffect (p + 3#64) len 4 off))
    (image₂ : (p + 3#64, bytes) ∈ instructionBytes v)
    (low : (branchTarget (p + 3#64) len off).toNat < 2^32)
    (next₁ : 0x100000 ≤ (p + 3#64).toNat ∧ (p + 3#64).toNat ≤ 0x106222)
    (next₂ : 0x100000 ≤ (p + 3#64 + BitVec.ofNat 64 len).toNat ∧
      (p + 3#64 + BitVec.ofNat 64 len).toNat ≤ 0x106222)
    (next₃ : 0x100000 ≤ (branchTarget (p + 3#64) len off).toNat ∧
      (branchTarget (p + 3#64) len off).toNat ≤ 0x106222)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = p) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if ((Operand.reg reg : Operand 64).read s == 0) then
        branchTarget (p + 3#64) len off else p + 3#64 + BitVec.ofNat 64 len) ∧
      Obs s t ∧ AgreesExcept [.flags, .rip] s t := by
  obtain ⟨s1, a1, r1, l1, b1, e1, o1, f1⟩ := dispatchAdvance testStep image₁
    (by intro t; simp [testR64R64Effect]) (by intro a b h; rfl)
    (by simp [clobbers]) next₁ ready loaded sp ip (Obs.refl s)
  have hz : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      ((Operand.reg reg : Operand 64).read s == 0) := by
    simpa only [testR64R64Effect, Effect.FlagsHold, testFlags, BitVec.and_self,
      StatusFlagsOutcome.Allows, FlagAllows] using e1.flags.2.2.2.1
  obtain ⟨s2, a2, r2, l2, b2, e2, o2, f2⟩ := dispatchAdvance branchStep image₂
    (by intro t; simp [jccEffect, branchEffect]) (by intro a b h; rfl)
    (by simp [jccEffect, clobbers]) (by
      dsimp only [jccEffect, branchEffect]
      split
      · exact next₃
      · exact next₂) r1 l1 b1 ⟨e1.rip, fun _ ↦ low⟩ o1
  refine ⟨s2, a1.trans a2, r2, l2, b2, ?_, o2, ?_⟩
  · simpa only [jccEffect, branchEffect, condHolds, BitVec.reduceToNat, hz] using e2.rip
  · apply (e1.agrees.trans e2.agrees).mono
    simp [testR64R64Effect, jccEffect, branchEffect, Effect.components]

end TestBranch

theorem entry_test [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = v.updateAddress + 0x29#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if ((Operand.reg 1 : Operand 64).read s == 0) then
        addPC v else v.updateAddress + 0x32#64) ∧
      Obs s t ∧ AgreesExcept [.flags, .rip] s t := by
  have target : branchTarget (v.updateAddress + 0x29#64 + 3#64) 6 ((zeroDisp v).signExtend 64) =
      addPC v := by cases v <;> decide +kernel
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at target
  have h := test_branch (v := v) (reg := 1)
    (test_r64_r64_effect_step (v.updateAddress + 0x29#64) 0x48 0xc9
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (jcc_rel32_effect_step _ 4 (zeroDisp v))
    (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) s ready loaded sp ip
  simpa only [target, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h

theorem postchunk_test [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = chunkSetupPC v + 78#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if ((Operand.reg 2 : Operand 64).read s == 0) then
        addPC v else byteSetupPC v) ∧
      Obs s t ∧ AgreesExcept [.flags, .rip] s t := by
  have target : branchTarget (chunkSetupPC v + 78#64 + 3#64) 2 (BitVec.signExtend 64 (0x29#8)) =
      addPC v := by cases v <;> decide +kernel
  have next : chunkSetupPC v + 78#64 + 3#64 + (2 : BitVec 64) = byteSetupPC v := by
    cases v <;> decide +kernel
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at target next
  have h := test_branch (v := v) (reg := 2)
    (test_r64_r64_effect_step (chunkSetupPC v + 78#64) 0x48 0xd2
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (jcc_rel8_effect_step _ 4 0x29)
    (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) s ready loaded sp ip
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, target, next] using h

private theorem mask_low (r : Fin 200) :
    (((BitVec.ofNat 64 r.val).setWidth 32).setWidth 64).setWidth 32 &&& (3 : BitVec 32) =
      BitVec.ofNat 32 (r.val % 4) := by
  revert r
  decide +kernel

set_option maxHeartbeats 600000 in
theorem dispatch_compare [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (r : Fin 200) (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = v.updateAddress + 0x32#64)
    (hr : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 r.val) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if 4 ≤ r.val then chunkSetupPC v else v.updateAddress + 0x41#64) ∧
      (Operand.reg 2 : Operand 64).read t = BitVec.ofNat 64 (r.val % 4) ∧
      AgreesExcept [.reg 2,.flags,.rip] s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := dispatchAdvance (v := v)
    (effect := movR32R32Effect (v.updateAddress + 0x32#64) 2 2 1)
    (mov_r32_r32_effect_step _ 0xca (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [movR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32R32Effect, h.read_reg])
    (by simp [clobbers]) (by short_next v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := dispatchAdvance (v := v)
    (effect := andR32Imm8Effect (v.updateAddress + 0x34#64) 3 2 3)
    (and_r32_imm8_effect_step _ 0xe2 3 (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [andR32Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR32Imm8Effect, h.read_reg])
    (by simp [clobbers]) (by short_next v) r1 l1 b1 (by simpa only [movR32R32Effect,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e1.rip) o1
  obtain ⟨s3,a3,r3,l3,b3,e3,o3,f3⟩ := dispatchAdvance (v := v)
    (effect := cmpR64Imm8Effect (v.updateAddress + 0x37#64) 1 4)
    (cmp_r64_imm8_effect_step _ 0x48 0xf9 4 (by unfold RexWPrefix; decide) (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [cmpR64Imm8Effect]) (by intro a b h; rfl)
    (by simp [clobbers]) (by short_next v) r2 l2 b2 (by simpa only [andR32Imm8Effect,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e2.rip) o2
  have hr2 : (Operand.reg 1 : Operand 64).read s2 = BitVec.ofNat 64 r.val := by
    first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect]
    exact hr
  have cf : (StatusFlags.ofRFLAGS s3.RFLAGS).CF = decide (r.val < 4) := by
    have hh := e3.flags.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).CF =
      decide (((Operand.reg 1 : Operand 64).read s2).toNat < 4) at hh
    rw [hr2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := r.isLt; omega)] at hh
    exact hh
  obtain ⟨s4,a4,r4,l4,b4,e4,o4,f4⟩ := dispatchAdvance (v := v)
    (jcc_rel32_effect_step (v.updateAddress + 0x3b#64) 3 (jaeDisp v))
    (by cases v <;> decide +kernel)
    (by intro t; simp [jccEffect, branchEffect]) (by intro a b h; rfl)
    (by simp [jccEffect, clobbers]) (by
      dsimp only [jccEffect, branchEffect]
      split <;> cases v <;> decide +kernel) r3 l3 b3
    ⟨by simpa only [cmpR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e3.rip, fun _ ↦ by cases v <;> decide +kernel⟩ o3
  refine ⟨s4,a1.trans (a2.trans (a3.trans a4)),r4,l4,b4,?_,?_,?_⟩
  · have target : branchTarget (v.updateAddress + 0x3b#64) 6 ((jaeDisp v).signExtend 64) =
        chunkSetupPC v := by cases v <;> decide +kernel
    have hh := e4.rip
    simp only [jccEffect, branchEffect, condHolds, BitVec.reduceToNat, cf, target,
      Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hh
    simpa only [BitVec.ofNat_eq_ofNat] using hh
  · first | rw [← o4.read_reg] | rw [← o4.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect, cmpR64Imm8Effect, jccEffect, branchEffect]
    have h32 := show (Operand.reg 1 : Operand 32).read s =
      ((Operand.reg 1 : Operand 64).read s).setWidth 32 from rfl
    simp only [BitVec.ofNat_eq_ofNat] at h32 hr
    have hm := mask_low r
    simp only [BitVec.ofNat_eq_ofNat] at hm
    rw [h32, hr, hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · apply ((e1.agrees.trans e2.agrees).trans (e3.agrees.trans e4.agrees)).mono
    simp only [movR32R32Effect_components, andR32Imm8Effect_components,
      cmpR64Imm8Effect_components, jccEffect, branchEffect_components]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ((rfl | rfl) | rfl | rfl | rfl) | (rfl | rfl) | rfl <;> simp

theorem short_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = v.updateAddress + 0x41#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = byteSetupPC v ∧
      (Operand.reg 6 : Operand 64).read t = 0 ∧ AgreesExcept [.reg 6,.flags,.rip] s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := dispatchAdvance (v := v)
    (effect := xorR32R32Effect (v.updateAddress + 0x41#64) 2 6 6)
    (xor_r32_r32_effect_step _ 0xf6 (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect,h.read_reg])
    (by simp [clobbers]) (by short_next v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := dispatchAdvance (v := v)
    (jmp_rel32_effect_step (v.updateAddress + 0x43#64) (shortDisp v) (by cases v <;> decide +kernel))
    (by cases v <;> decide +kernel)
    (by intro t; simp [jmpEffect]) (by intro a b h; rfl)
    (by simp [jmpEffect,Effect.components,clobbers]) (by short_next v) r1 l1 b1
    (by simpa only [xorR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e1.rip) o1
  refine ⟨s2,a1.trans a2,r2,l2,b2,?_,?_,?_⟩
  · have hh := e2.rip
    cases v <;> exact hh
  · first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [xorR32R32Effect,jmpEffect,branchEffect,BitVec.xor_self]
  · apply (e1.agrees.trans e2.agrees).mono
    simp [jmpEffect,Effect.components,xorR32R32Effect]
theorem byte_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = byteSetupPC v) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = bytePC v ∧
      AgreesExcept [.reg 15, .reg 3, .reg 6, .flags, .rip] s t ∧
      (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s +
        (Operand.reg 6 : Operand 64).read s + (Operand.reg 0 : Operand 64).read s ∧
      (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s +
        (Operand.reg 6 : Operand 64).read s ∧
      (Operand.reg 6 : Operand 64).read t = 0 := by
  obtain ⟨s1, a1, r1, l1, b1, e1, o1, f1⟩ := dispatchAdvance (v := v)
    (effect := addR64R64Effect (byteSetupPC v) 15 6)
    (add_r64_r64_effect_step _ 0x49 0xf7 (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg])
    (by simp [clobbers]) (by short_next v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2, a2, r2, l2, b2, e2, o2, f2⟩ := dispatchAdvance (v := v)
    (effect := addR64R64Effect (byteSetupPC v + 3#64) 15 0)
    (add_r64_r64_effect_step _ 0x49 0xc7 (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg])
    (by simp [clobbers]) (by short_next v) r1 l1 b1 e1.rip o1
  obtain ⟨s3, a3, r3, l3, b3, e3, o3, f3⟩ := dispatchAdvance (v := v)
    (effect := addR64R64Effect (byteSetupPC v + 6#64) 3 6)
    (add_r64_r64_effect_step _ 0x48 0xf3 (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg])
    (by simp [clobbers]) (by short_next v) r2 l2 b2
    (by simpa only [addR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e2.rip) o2
  obtain ⟨s4, a4, r4, l4, b4, e4, o4, f4⟩ := dispatchAdvance (v := v)
    (effect := xorR32R32Effect (byteSetupPC v + 9#64) 2 6 6)
    (xor_r32_r32_effect_step _ 0xf6 (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by simp [clobbers]) (by short_next v) r3 l3 b3
    (by simpa only [addR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e3.rip) o3
  obtain ⟨s5, a5, r5, l5, b5, e5, o5, f5⟩ := dispatchAdvance (v := v)
    (effect := fun _ ↦ nopEffect (byteSetupPC v + 11#64) 13)
    (nop_m_effect_step _ [0x66, 0x66, 0x66, 0x66, 0x2e] (by decide) (by decide)
      (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl)
    (by cases v <;> decide +kernel)
    (by intro t; simp [nopEffect]) (by intro a b h; rfl)
    (by simp [nopEffect, Effect.components, clobbers]) (by short_next v) r4 l4 b4
    (by simpa only [xorR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e4.rip) o4
  refine ⟨s5, a1.trans (a2.trans (a3.trans (a4.trans a5))), r5, l5, b5, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := e5.rip
    cases v <;> exact hh
  · apply (e1.agrees.trans (e2.agrees.trans (e3.agrees.trans
      (e4.agrees.trans e5.agrees)))).mono
    simp [addR64R64Effect, xorR32R32Effect, nopEffect, Effect.components]
  all_goals
    first | rw [← o5.read_reg] | rw [← o5.read_mem]
    x86_norm [leaR64Effect, addR64R64Effect, xorR32R32Effect, nopEffect,
      BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.xor_self]

def addClAlFullEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a := (Operand.reg 1 : Operand 8).read s
  let b := (Operand.reg 0 : Operand 8).read s
  { rip := p + 2
    writes := [⟨(Operand.reg 1 : Operand 64),
      mergeGPR 8 (a + b) ((Operand.reg 1 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

theorem add_cl_al_full_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x00, 0xc1]) (addClAlFullEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, add_cl_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [writeOutputs, Operand.read, Operand.write, setFlags, Fin.getElem_fin,
      Vector.getElem_set_self]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

private theorem cursor_merge (position count : Nat) (hsum : position + count < 200) :
    mergeGPR 8 ((BitVec.ofNat 64 count).setWidth 8 + (BitVec.ofNat 64 position).setWidth 8)
      (BitVec.ofNat 64 count) = BitVec.ofNat 64 (position + count) := by
  have hc : count < 256 := by omega
  have hs : position + count < 256 := by omega
  have hc64 : count < 2^64 := by omega
  simp only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), ← BitVec.ofNat_add]
  simp [mergeGPR, Runtime.setSlice, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64,
    Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hc, Nat.add_comm, Nat.mod_one]

theorem cursor_advance [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (position count : Nat) (hsum : position + count < 200)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = addPC v)
    (h0 : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 position)
    (h2 : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 count) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = cursorWriteAddress v ∧
      (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (position + count) ∧
      AgreesExcept [.reg 1, .flags, .rip] s t := by
  obtain ⟨t, ht, hr, hl, he⟩ := scalar_advance (v := v)
    (add_cl_al_full_effect_step (addPC v)) (by cases v <;> decide +kernel)
    ready loaded ip
    (by simp [addClAlFullEffect, Effect.components, Component.Covers])
    (by
      dsimp only [addClAlFullEffect]
      apply Permutation.inProgram_permutation_address <;>
        cases v <;> decide +kernel) sp
  refine ⟨t, ht, hr, hl, ?_, ?_, he.agrees⟩
  · have hh := he.rip
    cases v <;> exact hh
  · have hw := he.writes
    change (Operand.reg 1 : Operand 64).read t =
      mergeGPR 8 (((Operand.reg 1 : Operand 64).read s).setWidth 8 +
        ((Operand.reg 0 : Operand 64).read s).setWidth 8)
        ((Operand.reg 1 : Operand 64).read s) at hw
    rw [h0, h2, cursor_merge position count hsum] at hw
    exact hw

end Sha3.Proofs.Update.Partial.Short
