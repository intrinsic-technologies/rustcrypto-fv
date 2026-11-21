import Sha3.Proofs.Update.Partial.Control
import Sha3.Proofs.X86.Instructions.And.Triple
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import Sha3.Proofs.X86.Instructions.Add.Triple
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Sha3.Proofs.Update.Partial.Short

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def chunkSetupPC : Variant → BitVec 64
  | .sha224 => 0x100b25 | .sha256 => 0x100805
  | .sha384 => 0x1004e5 | .sha512 => 0x100215

def chunkPC (v : Variant) : BitVec 64 := chunkSetupPC v + 27

def byteSetupPC (v : Variant) : BitVec 64 := chunkSetupPC v + 83

def bytePC (v : Variant) : BitVec 64 := chunkSetupPC v + 107

def addPC (v : Variant) : BitVec 64 := chunkSetupPC v + 124

def clobbers : List Component :=
  [.reg 2, .reg 6, .reg 10, .reg 8, .reg 3, .reg 15, .flags, .rip]

theorem clobbers_nomem : ∀ c ∈ clobbers, ∀ a, ¬ c.Covers a := by
  simp [clobbers, Component.Covers]

theorem frame_trans {s t u : RamState} (h : AgreesExcept clobbers s t)
    (h' : AgreesExcept clobbers t u) : AgreesExcept clobbers s u :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

private theorem advance [Bindings] {v : Variant} {boundary : ReturnBoundary} {s model : RamState}
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

macro "short_next " v:term : tactic => `(tactic|
  cases ($v) <;> first
  | (try dsimp only [movR32R32Effect, movR64Imm64Effect, andR64R64Effect,
      andR32Imm8Effect, cmpR64Imm8Effect, xorR32R32Effect, leaR64Effect,
      addR64Imm8Effect, addR64R64Effect, jmpEffect, nopEffect]; decide +kernel)
  | (simp only [jccEffect, branchEffect]; split <;> decide +kernel))

private theorem chunk_mask (r : Fin 200) :
    0x7ffffffffffffffc#64 &&& BitVec.ofNat 64 r.val = BitVec.ofNat 64 (r.val / 4 * 4) := by
  revert r
  decide +kernel

theorem chunk_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (length : Fin 200) (s : RamState) (ready : ReadyToStep s)
    (loaded : CodeIn Extracted.programImage s) (sp : ¬ InProgram boundary.rip)
    (ip : s.RIP = chunkSetupPC v)
    (hlen : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 length.val) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = chunkPC v ∧
      (Operand.reg 10 : Operand 64).read t = BitVec.ofNat 64 (length.val / 4 * 4) ∧
      (Operand.reg 6 : Operand 64).read t = 0 ∧
      (Operand.reg 8 : Operand 64).read t =
        (Operand.reg 0 : Operand 64).read s + (Operand.reg 15 : Operand 64).read s + 3 ∧
      AgreesExcept [.reg 10, .reg 6, .reg 8, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, l1, b1, e1, o1, f1⟩ := advance (v := v)
    (effect := movR64Imm64Effect (chunkSetupPC v) 10 0x7ffffffffffffffc)
    (mov_r64_imm64_effect_step _ 0x49 0xba (by unfold RexWPrefix; decide) (by decide) 0x7ffffffffffffffc) (by cases v <;> decide +kernel)
    (by intro t; simp [movR64Imm64Effect, Write.Full, Operand.Full])
    (by intro a b h; rfl)
    (by simp [movR64Imm64Effect, Effect.components, clobbers]) (by short_next v)
    ready loaded sp ip (Obs.refl s)
  obtain ⟨s2, a2, r2, l2, b2, e2, o2, f2⟩ := advance (v := v)
    (effect := andR64R64Effect (chunkSetupPC v + 10) 10 1)
    (and_r64_r64_effect_step _ 0x49 0xca (by unfold RexWPrefix; decide) (by decide)) (by cases v <;> decide +kernel)
    (by intro t; simp [andR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR64R64Effect, h.read_reg])
    (by simp [andR64R64Effect, Effect.components, clobbers]) (by short_next v)
    r1 l1 b1 (by simpa only [movR64Imm64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e1.rip) o1
  obtain ⟨s3, a3, r3, l3, b3, e3, o3, f3⟩ := advance (v := v)
    (effect := leaR64Effect (chunkSetupPC v + 13) 8 (.sib 0 (some 15) 0 .none))
    (lea_r64_effect_step _ 0x4e (by unfold RexWPrefix; decide) 0 (.sib 0 (some 15) 0 .none) (by decide) (by decide) (by decide)) (by cases v <;> decide +kernel)
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by simp [leaR64Effect, Effect.components, clobbers]) (by short_next v)
    r2 l2 b2 (by simpa only [andR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e2.rip) o2
  obtain ⟨s4, a4, r4, l4, b4, e4, o4, f4⟩ := advance (v := v)
    (effect := addR64Imm8Effect (chunkSetupPC v + 17) 8 3)
    (add_r64_imm8_effect_step _ 0x49 0xc0 3 (by unfold RexWPrefix; decide) (by decide) (by decide)) (by cases v <;> decide +kernel)
    (by intro t; simp [addR64Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64Imm8Effect, h.read_reg])
    (by simp [addR64Imm8Effect, Effect.components, clobbers]) (by short_next v)
    r3 l3 b3 (by simpa only [leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e3.rip) o3
  obtain ⟨s5, a5, r5, l5, b5, e5, o5, f5⟩ := advance (v := v)
    (effect := xorR32R32Effect (chunkSetupPC v + 21) 2 6 6)
    (xor_r32_r32_effect_step _ 0xf6 (by decide)) (by cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by simp [xorR32R32Effect, Effect.components, clobbers]) (by short_next v)
    r4 l4 b4 (by simpa only [addR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e4.rip) o4
  obtain ⟨s6, a6, r6, l6, b6, e6, o6, f6⟩ := advance (v := v)
    (effect := fun _ => nopEffect (chunkSetupPC v + 23) 4)
    (nop_m_effect_step _ [] (by simp) (by decide) (.base 0 (.d8 0)) (by decide) rfl rfl) (by cases v <;> decide +kernel)
    (by intro t; simp [nopEffect, Write.Full, Operand.Full])
    (by intro a b h; rfl)
    (by simp [nopEffect, Effect.components, clobbers]) (by short_next v)
    r5 l5 b5 (by simpa only [xorR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e5.rip) o5
  refine ⟨s6, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6)))),
    r6, l6, b6, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := e6.rip
    cases v <;> exact hh
  · first | rw [← o6.read_reg] | rw [← o6.read_mem]
    x86_norm [movR64Imm64Effect, andR64R64Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect]
    have hm := chunk_mask length
    simp only [BitVec.ofNat_eq_ofNat] at hlen hm
    rw [hlen]
    exact hm
  · first | rw [← o6.read_reg] | rw [← o6.read_mem]
    x86_norm [movR64Imm64Effect, andR64R64Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect, BitVec.xor_self]
  · first | rw [← o6.read_reg] | rw [← o6.read_mem]
    x86_norm [movR64Imm64Effect, andR64R64Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · apply (e1.agrees.trans (e2.agrees.trans (e3.agrees.trans
      (e4.agrees.trans (e5.agrees.trans e6.agrees))))).mono
    simp [movR64Imm64Effect, andR64R64Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect, Effect.components]

end Sha3.Proofs.Update.Partial.Short
