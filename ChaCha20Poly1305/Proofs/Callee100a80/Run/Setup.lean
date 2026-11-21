import ChaCha20Poly1305.Proofs.Callee100a80.Run.Stepping
import X86Proofs.Instructions.Cmov.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple

namespace ChaCha20Poly1305.Proofs.Callee100a80.Run

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.ChaCha20

section SetupBlocks

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

theorem ap_code_n {base q : BitVec 64} {N : Nat}
    (hc : ∀ i < N, ¬ InProgram (base + BitVec.ofNat 64 i))
    (off len : Nat) (hn : off + len ≤ N) (ilen : Nat) (hq : 0x100000 ≤ q.toNat)
    (hq2 : q.toNat + ilen ≤ 0x1014bc) : RangeApart (base + BitVec.ofNat 64 off) len q ilen := by
  intro i hi j hj he
  apply hc (off + i) (by omega)
  have hk : q + BitVec.ofNat 64 j =
      Extracted.textAddress + BitVec.ofNat 64 (q.toNat - 0x100000 + j) := by
    apply BitVec.eq_of_toNat_eq
    have := q.isLt
    have ht : Extracted.textAddress.toNat = 0x100000 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_add, ht, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h1 : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
    have h2 : (q.toNat - 0x100000 + j) % 2 ^ 64 = q.toNat - 0x100000 + j :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    congr 1
    omega
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, he, hk]
  exact text_address_in_program _ (by rw [Cuts.Rounds.textBytes_size_eq]; omega)

theorem r_head {s : RamState} {a : BitVec 64} {n : Nat} (h : MemReadable s a n) (len : Nat)
    (hn : len ≤ n) : MemReadable s a len :=
  ⟨by have := h.low; omega, fun i hi => h.mem i (by omega)⟩

                                                                                             
                       
structure XFrame (sp st bf : BitVec 64) (s : RamState) : Prop where
  rsp : rspOf s = sp
  rdi : (Operand.reg 7 : Operand 64).read s = st
  rsi : (Operand.reg 6 : Operand 64).read s = bf
  stack : MemWritable s sp 0x170
  stackCode : ∀ i < 0x170, ¬ InProgram (sp + BitVec.ofNat 64 i)
  state : MemWritable s st 0x80
  stateCode : ∀ i < 0x80, ¬ InProgram (st + BitVec.ofNat 64 i)
  buf : MemReadable s bf 24

macro "xf_frame " hP:ident : tactic => `(tactic| (
  have hF := ($hP).2
  have hS := hF.rsp
  have hD := hF.rdi
  have hI := hF.rsi
  try x86_norm at hS hD hI
  try x86_norm
  try simp only [hS, hD, hI]
  first
  | exact (Cuts.Rounds.w_slice hF.stack _ _ (by decide)).readable
  | exact Cuts.Rounds.w_slice hF.stack _ _ (by decide)
  | exact ap_code_n hF.stackCode _ _ (by decide) _ (by decide) (by decide)
  | exact (Cuts.Rounds.w_slice hF.state _ _ (by decide)).readable
  | exact Cuts.Rounds.w_slice hF.state _ _ (by decide)
  | exact ap_code_n hF.stateCode _ _ (by decide) _ (by decide) (by decide)
  | exact Cuts.Tail.r_slice hF.buf _ _ (by decide)
  | exact r_head hF.buf _ (by decide)))

theorem gA1 : gprNumber 0 (rexR (UInt8.toBitVec 65)) 0 = 0 := by decide
theorem gA2 : gprNumber 0 (rexR (UInt8.toBitVec 72)) 3 = 3 := by decide
theorem gA3 : gprNumber 0 (rexR (UInt8.toBitVec 76)) 6 = 14 := by decide
theorem gA4 : gprNumber 0 (rexB (UInt8.toBitVec 77)) (modrmRm 211) = 11 := by decide
theorem gA5 : gprNumber 0 (rexR (UInt8.toBitVec 77)) (modrmReg 211) = 10 := by decide
theorem gA6 : gprNumber 0 (rexB (UInt8.toBitVec 76)) (modrmRm 216) = 0 := by decide
theorem gA7 : gprNumber 0 (rexR (UInt8.toBitVec 76)) (modrmReg 216) = 11 := by decide
theorem gA8 : gprNumber 0 (rexB (UInt8.toBitVec 72)) (modrmRm 232) = 0 := by decide
theorem gA9 : gprNumber 0 (rexR (UInt8.toBitVec 72)) 0 = 0 := by decide
theorem gA10 : gprNumber 0 (rexB (UInt8.toBitVec 69)) (modrmRm 223) = 15 := by decide
theorem gA11 : gprNumber 0 (rexR (UInt8.toBitVec 69)) (modrmReg 223) = 11 := by decide
theorem gA12 : gprNumber 0 (rexB (UInt8.toBitVec 65)) (modrmRm 231) = 15 := by decide
theorem gA13 : gprNumber 0 (rexB (UInt8.toBitVec 77)) (modrmRm 210) = 10 := by decide
theorem gA14 : gprNumber 0 (rexR (UInt8.toBitVec 77)) (modrmReg 210) = 10 := by decide

def blockABytes : List UInt8 :=
  [0x41, 0x8d, 0x04, 0x0a, 0x88, 0x47, 0x40, 0x48, 0x8b, 0x1e, 0x4c, 0x8b, 0x76, 0x08, 0x4d,
    0x29, 0xd3, 0x4c, 0x89, 0xd8, 0x48, 0xc1, 0xe8, 0x06, 0x48, 0x89, 0x44, 0x24, 0x50, 0x45,
    0x89, 0xdf, 0x41, 0x83, 0xe7, 0x3f, 0x4d, 0x85, 0xd2]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
theorem blockA [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st bf : BitVec 64) :
    ∃ eff, AdvancesBlock boundary (fun s => s.RIP = 0x100ad7 ∧ XFrame sp st bf s)
      (codeRange 0x100ad7 blockABytes) eff ∧
      ∀ (L I O : BitVec 64) s t, rspOf s = sp → (Operand.reg 7 : Operand 64).read s = st →
        (Operand.reg 6 : Operand 64).read s = bf →
        Cuts.Tail.StackStateApart sp st →
        (∀ (m : Ram) (v : BitVec 8), memLoad (memStore m (st + 0x40) v) (bf + 0) 64 =
            memLoad m (bf + 0) 64) →
        (∀ (m : Ram) (v : BitVec 8), memLoad (memStore m (st + 0x40) v) (bf + 8) 64 =
            memLoad m (bf + 8) 64) →
        (Operand.reg 11 : Operand 64).read s = L → (Operand.reg 10 : Operand 64).read s = 0 →
        (Operand.reg 1 : Operand 64).read s = 0x40 →
        (Operand.mem (bf + 0) : Operand 64).read s = I →
        (Operand.mem (bf + 8) : Operand 64).read s = O →
        (eff s).Holds s t →
        t.RIP = 0x100afe ∧ Write.AllHold t [⟨(Operand.reg 3 : Operand 64), I⟩, ⟨(Operand.reg 14 : Operand 64), O⟩,
          ⟨(Operand.reg 11 : Operand 64), L⟩, ⟨(Operand.reg 10 : Operand 64), 0⟩,
          ⟨(Operand.mem (sp + 0x50) : Operand 64), L >>> 6⟩,
          ⟨(Operand.reg 15 : Operand 64), (L.setWidth 32 &&& 0x3f).setWidth 64⟩] ∧
        AgreesExcept [.reg 0, .reg 3, .reg 14, .reg 11, .reg 15, .flags, .rip, .mem (st + 0x40) 1,
          .mem (sp + 0x50) 8] s t ∧
        (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true := by
  refine ⟨?eff, ?blk, ?post⟩
  case blk =>
    unfold blockABytes
    blk_begin (lea_r32_rex_effect_step 0x100ad7 0x41 (by unfold RexNoWPrefix; decide) 0
      (.sib 10 (some 1) 0 .none) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m8_r8_norex_effect_step 0x100adb 0 (.base 7 (.d8 0x40)) (by decide) (by decide)
      (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r64_m64_effect_step 0x100ade 0x48 (by unfold RexWPrefix; decide) 3 (.base 6 .none)
      (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r64_m64_effect_step 0x100ae1 0x4c (by unfold RexWPrefix; decide) 6
      (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (sub_r64_r64_effect_step 0x100ae5 0x4d 0xd3 (by unfold RexWPrefix; decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r64_r64_effect_step 0x100ae8 0x4c 0xd8 (by unfold RexWPrefix; decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (shr_r64_imm8_effect_step 0x100aeb 0x48 0xe8 0x06 (by unfold RexWPrefix; decide)
      (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100aef 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_r32_rex_effect_step 0x100af4 0x45 0xdf (by unfold RexNoWPrefix; decide)
      (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (and_r32_imm8_rex_effect_step 0x100af7 0x41 0xe7 0x3f (by unfold RexNoWPrefix; decide)
      (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (test_r64_r64_effect_step 0x100afb 0x4d 0xd2 (by unfold RexWPrefix; decide)
      (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_finish
  case post =>
    intro L I O s t hs hd hi hss hap0 hap8 h11 h10 h1 hI hO he
    refine ⟨by rw [he.rip]; first | rfl | x86_norm, ?_⟩
    simp only [gA1, gA2, gA3, gA4, gA5, gA6, gA7, gA8, gA9, gA10, gA11, gA12, gA13, gA14] at he
    have hfull : ∀ w ∈ (?eff s).writes, w.Full := by x86_norm
    have ho := he.obsAfter hfull true
    x86_norm at hs hd hi h11 h10 h1 hI hO hap0 hap8
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · have ha := he.agrees
      x86_norm [hs, hd] at ha
      exact ha.mono (by simp (config := {decide := true}))
    · have hz := he.flag .ZF
      x86_norm at hz
      simp only [h10] at hz
      exact hz
    simp only [Write.AllHold]
    simp only [← ho.read_reg, ← ho.read_mem]
    x86_norm [hs, hd, hi]
    unfold Cuts.Tail.StackStateApart at hss
    have hI' : memLoad s.external (bf + 0#64) 64 = I := hI
    have hO' : memLoad s.external (bf + 8#64) 64 = O := hO
    have hsc : shiftCount 64 (UInt8.toBitVec 6) = 6 := by decide
    have hlea : BitVec.setWidth 8 (BitVec.setWidth 64 (leaSpec 32 (0#64 + (64#64 <<< 0 + 0#64)))) =
        0x40 := by decide
    simp (config := {decide := true}) only [Cuts.Tail.write_reg_external,
      Cuts.Tail.write_mem_external, hap0, hap8, h11, h10, h1, hss, hI', hO', hsc, hlea,
      BitVec.sub_zero, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, and_true,
      memLoad_memStore_same]
    done

theorem gB1 : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 7 = 7 := by decide
theorem gB2 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 2 = 10 := by decide
theorem gB3 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 3 = 11 := by decide
theorem gB4 : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 3 = 3 := by decide
theorem gB5 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 6 = 14 := by decide
theorem gB6 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 7 = 15 := by decide

def blockBBytes : List UInt8 :=
  [0x48, 0x83, 0x7c, 0x24, 0x50, 0x00, 0x48, 0x89, 0x7c, 0x24, 0x48, 0x4c, 0x89, 0x94, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x4c, 0x89, 0x9c, 0x24, 0xa8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x9c,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xb4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4c, 0x89,
    0xbc, 0x24, 0xa0, 0x00, 0x00, 0x00]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
theorem blockB [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st bf : BitVec 64) :
    ∃ eff, AdvancesBlock boundary (fun s => s.RIP = 0x100ba5 ∧ XFrame sp st bf s)
      (codeRange 0x100ba5 blockBBytes) eff ∧
      ∀ (N R10 R11 RBX R14 R15 : BitVec 64) s t, rspOf s = sp →
        (Operand.reg 7 : Operand 64).read s = st →
        (Operand.mem (sp + 0x50) : Operand 64).read s = N →
        (Operand.reg 10 : Operand 64).read s = R10 → (Operand.reg 11 : Operand 64).read s = R11 →
        (Operand.reg 3 : Operand 64).read s = RBX → (Operand.reg 14 : Operand 64).read s = R14 →
        (Operand.reg 15 : Operand 64).read s = R15 →
        (eff s).Holds s t →
        t.RIP = 0x100bd8 ∧ Write.AllHold t [⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩,
          ⟨(Operand.mem (sp + 0x98) : Operand 64), R10⟩,
          ⟨(Operand.mem (sp + 0xa8) : Operand 64), R11⟩,
          ⟨(Operand.mem (sp + 0x90) : Operand 64), RBX⟩,
          ⟨(Operand.mem (sp + 0x88) : Operand 64), R14⟩,
          ⟨(Operand.mem (sp + 0xa0) : Operand 64), R15⟩] ∧
        AgreesExcept [.flags, .rip, .mem (sp + 0x48) 8, .mem (sp + 0x98) 8,
          .mem (sp + 0xa8) 8, .mem (sp + 0x90) 8, .mem (sp + 0x88) 8, .mem (sp + 0xa0) 8] s t ∧
        (StatusFlags.ofRFLAGS t.RFLAGS).ZF = (N == 0) := by
  refine ⟨?eff, ?blk, ?post⟩
  case blk =>
    unfold blockBBytes
    blk_begin (cmp_m64_imm8_effect_step 0x100ba5 0x48 (by unfold RexWPrefix; decide)
      (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100bab 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100bb0 0x4c (by unfold RexWPrefix; decide) 2
      (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100bb8 0x4c (by unfold RexWPrefix; decide) 3
      (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100bc0 0x48 (by unfold RexWPrefix; decide) 3
      (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100bc8 0x4c (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100bd0 0x4c (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) using hP => (xf_frame hP) (blk_boundary)
    blk_finish
  case post =>
    intro N R10 R11 RBX R14 R15 s t hs hd hN h10 h11 h3 h14 h15 he
    refine ⟨by rw [he.rip]; first | rfl | x86_norm, ?_⟩
    simp only [gB1, gB2, gB3, gB4, gB5, gB6] at he
    have hfull : ∀ w ∈ (?eff s).writes, w.Full := by x86_norm
    have ho := he.obsAfter hfull true
    x86_norm at hs hd hN h10 h11 h3 h14 h15
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · have ha := he.agrees
      x86_norm [hs, hd] at ha
      exact ha.mono (by simp (config := {decide := true}))
    · have hz := he.flag .ZF
      x86_norm [hs] at hz
      simp only [hN, FlagAllows, cmpSpec_ZF] at hz
      exact hz
    simp only [Write.AllHold]
    simp only [← ho.read_reg, ← ho.read_mem]
    x86_norm [hs, hd]
    simp (config := {decide := true}) only [Cuts.Tail.write_reg_external,
      Cuts.Tail.write_mem_external, hd, h10, h11, h3, h14, h15, and_true]
    done

theorem gC1 : gprNumber 0 (rexR (UInt8.toBitVec 0x4a)) 0 = 0 := by decide
theorem gC2 : gprNumber 0 (rexR (UInt8.toBitVec 0x4b)) 0 = 0 := by decide
theorem gC3 : gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 2 = 10 := by decide
theorem gC4 : gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 3 = 11 := by decide
theorem gC5 : gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 0 = 8 := by decide
theorem gC6 : gprNumber 0 0 (modrmRm 0xff) = 7 := by decide
theorem gC7 : gprNumber 0 0 (modrmReg 0xff) = 7 := by decide

def blockC1Bytes : List UInt8 :=
  [0x4a, 0x8d, 0x04, 0x13, 0x48, 0x89, 0x44, 0x24, 0x68, 0x4b, 0x8d, 0x04, 0x16, 0x48, 0x89,
    0x44, 0x24, 0x60, 0x8b, 0x07, 0x89, 0x44, 0x24, 0x58, 0x8b, 0x47, 0x04, 0x89, 0x44, 0x24,
    0x10, 0x8b, 0x47, 0x08, 0x89, 0x44, 0x24, 0x0c, 0x8b, 0x47, 0x0c, 0x89, 0x44, 0x24, 0x40,
    0x44, 0x8b, 0x57, 0x10]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem blockC1 [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st bf : BitVec 64) :
    ∃ eff, AdvancesBlock boundary (fun s => s.RIP = 0x100bde ∧ XFrame sp st bf s)
      (codeRange 0x100bde blockC1Bytes) eff ∧
      ∀ (I O : BitVec 64) (x : Vector UInt32 16) s t, rspOf s = sp →
        (Operand.reg 7 : Operand 64).read s = st → Cuts.Tail.StackStateApart sp st →
        (Operand.reg 3 : Operand 64).read s = I → (Operand.reg 14 : Operand 64).read s = O →
        (Operand.reg 10 : Operand 64).read s = 0 →
        Write.AllHold s (Cuts.Rounds.cut st Cuts.Tail.stL x) →
        (eff s).Holds s t →
        t.RIP = 0x100c0f ∧ Write.AllHold t [⟨(Operand.mem (sp + 0x68) : Operand 64), I⟩,
          ⟨(Operand.mem (sp + 0x60) : Operand 64), O⟩,
          ⟨(Operand.mem (sp + 0x58) : Operand 32), x[0].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x10) : Operand 32), x[1].toBitVec⟩,
          ⟨(Operand.mem (sp + 0xc) : Operand 32), x[2].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x40) : Operand 32), x[3].toBitVec⟩,
          ⟨(Operand.reg 10 : Operand 64), x[4].toBitVec.setWidth 64⟩] ∧
        AgreesExcept [.reg 0, .reg 10, .rip, .mem (sp + 0x68) 8, .mem (sp + 0x60) 8,
          .mem (sp + 0x58) 4, .mem (sp + 0x10) 4, .mem (sp + 0xc) 4, .mem (sp + 0x40) 4] s t := by
  refine ⟨?eff, ?blk, ?post⟩
  case blk =>
    unfold blockC1Bytes
    blk_begin (lea_r64_effect_step 0x100bde 0x4a (by unfold RexWPrefix; decide) 0 (.sib 3 (some 10) 0 .none) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100be2 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (lea_r64_effect_step 0x100be7 0x4b (by unfold RexWPrefix; decide) 0 (.sib 14 (some 10) 0 .none) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m64_r64_effect_step 0x100beb 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100bf0 0 (.base 7 .none) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100bf2 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100bf6 0 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100bf9 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100bfd 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c00 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c04 0 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c07 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_effect_step 0x100c0b 0x44 (by unfold RexNoWPrefix; decide) 2 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_finish
  case post =>
    intro I O x s t hs hd hss h3 h14 h10 hw he
    refine ⟨by rw [he.rip]; first | rfl | x86_norm, ?_⟩
    simp only [gC1, gC2, gC3] at he
    have hfull : ∀ w ∈ (?eff s).writes, w.Full := by x86_norm
    have ho := he.obsAfter hfull true
    x86_norm at hs hd h3 h14 h10
    refine ⟨?_, ?_⟩
    rotate_left
    · have ha := he.agrees
      x86_norm [hs, hd] at ha
      exact ha.mono (by simp (config := {decide := true}))
    simp only [Cuts.Rounds.cut, Cuts.Tail.stL, List.map, Cuts.Rounds.Loc.op, Write.AllHold] at hw
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hw
    simp only [Write.AllHold]
    simp only [← ho.read_reg, ← ho.read_mem]
    x86_norm [hs, hd]
    x86_norm at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
    simp only [BitVec.add_zero] at g0
    unfold Cuts.Tail.StackStateApart at hss
    simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      and_true, hss, Cuts.Tail.write_reg_external, Cuts.Tail.write_mem_external]
    x86_norm
    simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      h3, h14, h10, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero, g0, g1, g2, g3,
      g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, and_true, eq_self_iff_true]
    repeat' (first | exact trivial | exact rfl | apply And.intro)


def blockC2aBytes : List UInt8 :=
  [0x8b, 0x47, 0x14, 0x89, 0x44, 0x24, 0x34, 0x8b, 0x47, 0x18, 0x89, 0x44, 0x24, 0x30, 0x8b,
    0x47, 0x1c, 0x89, 0x44, 0x24, 0x2c, 0x44, 0x8b, 0x5f, 0x20, 0x8b, 0x47, 0x24, 0x89, 0x44,
    0x24, 0x28, 0x8b, 0x47, 0x28, 0x89, 0x44, 0x24, 0x24, 0x8b, 0x47, 0x2c, 0x89, 0x44, 0x24,
    0x20]

def blockC2bBytes : List UInt8 :=
  [0x44, 0x8b, 0x47, 0x34, 0x8b, 0x47, 0x38, 0x89, 0x44, 0x24, 0x1c, 0x8b, 0x47, 0x3c, 0x89,
    0x44, 0x24, 0x18, 0x31, 0xff, 0x44, 0x89, 0x54, 0x24, 0x38, 0x44, 0x89, 0x9c, 0x24, 0x84,
    0x00, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x66, 0x2e, 0x0f, 0x1f,
    0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem blockC2a [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st bf : BitVec 64) :
    ∃ eff, AdvancesBlock boundary (fun s => s.RIP = 0x100c0f ∧ XFrame sp st bf s)
      (codeRange 0x100c0f blockC2aBytes) eff ∧
      ∀ (x : Vector UInt32 16) s t, rspOf s = sp →
        (Operand.reg 7 : Operand 64).read s = st → Cuts.Tail.StackStateApart sp st →
        Write.AllHold s (Cuts.Rounds.cut st Cuts.Tail.stL x) →
        (eff s).Holds s t →
        t.RIP = 0x100c3d ∧ Write.AllHold t [⟨(Operand.mem (sp + 0x34) : Operand 32), x[5].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x30) : Operand 32), x[6].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x2c) : Operand 32), x[7].toBitVec⟩,
          ⟨(Operand.reg 11 : Operand 64), x[8].toBitVec.setWidth 64⟩,
          ⟨(Operand.mem (sp + 0x28) : Operand 32), x[9].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x24) : Operand 32), x[10].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x20) : Operand 32), x[11].toBitVec⟩] ∧
        AgreesExcept [.reg 0, .reg 11, .rip, .mem (sp + 0x34) 4, .mem (sp + 0x30) 4,
          .mem (sp + 0x2c) 4, .mem (sp + 0x28) 4, .mem (sp + 0x24) 4, .mem (sp + 0x20) 4] s t := by
  refine ⟨?eff, ?blk, ?post⟩
  case blk =>
    unfold blockC2aBytes
    blk_begin (mov_r32_m32_low_effect_step 0x100c0f 0 (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c12 0 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c16 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c19 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c1d 0 (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c20 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_effect_step 0x100c24 0x44 (by unfold RexNoWPrefix; decide) 3 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c28 0 (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c2b 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c2f 0 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c32 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c36 0 (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c39 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_finish
  case post =>
    intro x s t hs hd hss hw he
    refine ⟨by rw [he.rip]; first | rfl | x86_norm, ?_⟩
    simp only [gC3, gC4, gC5, gC6, gC7] at he
    have hfull : ∀ w ∈ (?eff s).writes, w.Full := by x86_norm
    have ho := he.obsAfter hfull true
    x86_norm at hs hd
    refine ⟨?_, ?_⟩
    rotate_left
    · have ha := he.agrees
      x86_norm [hs, hd] at ha
      exact ha.mono (by simp (config := {decide := true}))
    simp only [Cuts.Rounds.cut, Cuts.Tail.stL, List.map, Cuts.Rounds.Loc.op, Write.AllHold] at hw
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hw
    simp only [Write.AllHold]
    simp only [← ho.read_reg, ← ho.read_mem]
    x86_norm [hs, hd]
    x86_norm at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
    unfold Cuts.Tail.StackStateApart at hss
    simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      and_true, hss, Cuts.Tail.write_reg_external, Cuts.Tail.write_mem_external]
    x86_norm
    simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, and_true,
      eq_self_iff_true]
    try simp only [BitVec.xor_self, BitVec.setWidth_zero]
    repeat' (first | exact trivial | exact rfl | apply And.intro)

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
theorem blockC2b [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st bf : BitVec 64) :
    ∃ eff, AdvancesBlock boundary (fun s => s.RIP = 0x100c3d ∧ XFrame sp st bf s)
      (codeRange 0x100c3d blockC2bBytes) eff ∧
      ∀ (x : Vector UInt32 16) s t, rspOf s = sp →
        (Operand.reg 7 : Operand 64).read s = st → Cuts.Tail.StackStateApart sp st →
        (Operand.reg 10 : Operand 32).read s = x[4].toBitVec →
        (Operand.reg 11 : Operand 32).read s = x[8].toBitVec →
        Write.AllHold s (Cuts.Rounds.cut st Cuts.Tail.stL x) →
        (eff s).Holds s t →
        t.RIP = 0x100c70 ∧ Write.AllHold t [⟨(Operand.reg 8 : Operand 64), x[13].toBitVec.setWidth 64⟩,
          ⟨(Operand.mem (sp + 0x1c) : Operand 32), x[14].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x18) : Operand 32), x[15].toBitVec⟩,
          ⟨(Operand.reg 7 : Operand 64), 0⟩,
          ⟨(Operand.mem (sp + 0x38) : Operand 32), x[4].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x84) : Operand 32), x[8].toBitVec⟩,
          ⟨(Operand.mem (sp + 0x80) : Operand 32), x[13].toBitVec⟩] ∧
        AgreesExcept [.reg 8, .reg 0, .reg 7, .flags, .rip, .mem (sp + 0x1c) 4, .mem (sp + 0x18) 4,
          .mem (sp + 0x38) 4, .mem (sp + 0x84) 4, .mem (sp + 0x80) 4] s t := by
  refine ⟨?eff, ?blk, ?post⟩
  case blk =>
    unfold blockC2bBytes
    blk_begin (mov_r32_m32_effect_step 0x100c3d 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c41 0 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c44 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_r32_m32_low_effect_step 0x100c48 0 (.base 7 (.d8 0x3c)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_low_effect_step 0x100c4b 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (xor_r32_r32_effect_step 0x100c4f 0xff (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_effect_step 0x100c51 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_effect_step 0x100c56 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    blk_then (mov_m32_r32_effect_step 0x100c5e 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide))
      using hP => (xf_frame hP) (blk_boundary)
    refine AdvancesBlock.block_then ?k (nop_m_effect_step 0x100c66 [0x66, 0x2e] (by decide)
      (by decide) (.sib 0 (some 0) 0 (.d32 0)) (by decide) (by decide) (by decide)) ?loc ?sub ?full
      ?mid ?boundary
    case loc => x86_local
    case sub => first | x86_sub | code_sub
    case full =>
      first
      | (intro s _
         apply Effect.Local.full
         repeat' first
           | (solve | x86_local)
           | apply Effect.Local.seq
         done)
      | x86_full
    case mid =>
      intro s s' hP hH hO
      refine ⟨hH.rip_of (by first | rfl | x86_norm), ?_⟩
      exact Effect.Avoids.of_noMem
        (fun c hc x => by simp_all [nopEffect, Effect.components, Component.Covers]) _
    case boundary => blk_boundary
    case' k => skip
    blk_finish
  case post =>
    intro x s t hs hd hss h10 h11 hw he
    refine ⟨by rw [he.rip]; first | rfl | x86_norm, ?_⟩
    simp only [gC3, gC4, gC5, gC6, gC7] at he
    have hfull : ∀ w ∈ (?eff s).writes, w.Full := by x86_norm
    have ho := he.obsAfter hfull true
    x86_norm at hs hd h10 h11
    refine ⟨?_, ?_⟩
    rotate_left
    · have ha := he.agrees
      x86_norm [hs, hd] at ha
      exact ha.mono (by simp (config := {decide := true}))
    simp only [Cuts.Rounds.cut, Cuts.Tail.stL, List.map, Cuts.Rounds.Loc.op, Write.AllHold] at hw
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hw
    simp only [Write.AllHold]
    simp only [← ho.read_reg, ← ho.read_mem]
    x86_norm [hs, hd]
    x86_norm at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
    unfold Cuts.Tail.StackStateApart at hss
    simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      and_true, hss, Cuts.Tail.write_reg_external, Cuts.Tail.write_mem_external]
    x86_norm
    simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      h10, h11, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, and_true,
      eq_self_iff_true]
    try simp only [BitVec.xor_self, BitVec.setWidth_zero]
    repeat' (first | exact trivial | exact rfl | apply And.intro)

end SetupBlocks

section SetupHelpers

theorem StackLocal.monoF {b : BitVec 64} {F F' : Nat → Prop} {O : BitVec 64 → Prop}
    {L : List Component} (h : StackLocal b F O L) (hF : ∀ i, F i → F' i) :
    StackLocal b F' O L :=
  ⟨h.1, h.2.1, fun c hc x hx => (h.2.2 c hc x hx).imp (fun ⟨i, h1, h2, h3⟩ => ⟨i, hF i h1, h2, h3⟩) id⟩

macro "local_tac" : tactic => `(tactic| (
  refine ⟨by simp, fun c hc hm => ?_, fun c hc x hx => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    repeat' (rcases hc with he | hc)
    all_goals (try subst he)
    all_goals (try subst hc)
    all_goals first | (simp [Cuts.Rounds.regScratch]; done) | (simp [Component.isMem] at hm)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    repeat' (rcases hc with he | hc)
    all_goals (try subst he)
    all_goals (try subst hc)
    all_goals first
      | (simp [Component.Covers] at hx; done)
      | (obtain ⟨k, hk, he⟩ := hx
         subst he
         first
         | exact .inl ⟨_, by simp; omega, by simp; omega, Cuts.Tail.add_toNat _ _ _⟩
         | exact .inr ⟨k, hk, rfl⟩)))

def PosByte (st : BitVec 64) (x : BitVec 64) : Prop := ∃ k < 1, x = st + 0x40 + BitVec.ofNat 64 k

theorem localA (sp st : BitVec 64) :
    StackLocal sp (fun i => 0x50 ≤ i ∧ i < 0x58) (PosByte st)
      [.reg 0, .reg 3, .reg 14, .reg 11, .reg 15, .flags, .rip, .mem (st + 0x40) 1,
        .mem (sp + 0x50) 8] := by
  local_tac

theorem localB (sp : BitVec 64) :
    StackLocal sp (fun i => (0x48 ≤ i ∧ i < 0x50) ∨ (0x88 ≤ i ∧ i < 0xb0)) (fun _ => False)
      [.flags, .rip, .mem (sp + 0x48) 8, .mem (sp + 0x98) 8, .mem (sp + 0xa8) 8,
        .mem (sp + 0x90) 8, .mem (sp + 0x88) 8, .mem (sp + 0xa0) 8] := by
  local_tac

theorem localC1 (sp : BitVec 64) :
    StackLocal sp (fun i => (0x58 ≤ i ∧ i < 0x5c) ∨ (0x60 ≤ i ∧ i < 0x70) ∨
        (0xc ≤ i ∧ i < 0x14) ∨ (0x40 ≤ i ∧ i < 0x44)) (fun _ => False)
      [.reg 0, .reg 10, .rip, .mem (sp + 0x68) 8, .mem (sp + 0x60) 8,
        .mem (sp + 0x58) 4, .mem (sp + 0x10) 4, .mem (sp + 0xc) 4, .mem (sp + 0x40) 4] := by
  local_tac

theorem localC2a (sp : BitVec 64) :
    StackLocal sp (fun i => 0x20 ≤ i ∧ i < 0x38) (fun _ => False)
      [.reg 0, .reg 11, .rip, .mem (sp + 0x34) 4, .mem (sp + 0x30) 4,
        .mem (sp + 0x2c) 4, .mem (sp + 0x28) 4, .mem (sp + 0x24) 4, .mem (sp + 0x20) 4] := by
  local_tac

theorem localC2b (sp : BitVec 64) :
    StackLocal sp (fun i => (0x18 ≤ i ∧ i < 0x20) ∨ (0x38 ≤ i ∧ i < 0x3c) ∨ (0x80 ≤ i ∧ i < 0x88))
      (fun _ => False)
      [.reg 8, .reg 0, .reg 7, .flags, .rip, .mem (sp + 0x1c) 4, .mem (sp + 0x18) 4,
        .mem (sp + 0x38) 4, .mem (sp + 0x84) 4, .mem (sp + 0x80) 4] := by
  local_tac

theorem localRegs (sp : BitVec 64) (L : List Component) (h : ∀ c ∈ L, c ∈ Cuts.Rounds.regScratch) :
    StackLocal sp (fun _ => False) (fun _ => False) L := by
  refine ⟨fun h4 => by have := h _ h4; simp [Cuts.Rounds.regScratch] at this,
    fun c hc _ => h c hc, fun c hc x hx => ?_⟩
  have := h c hc
  simp only [Cuts.Rounds.regScratch, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [Component.Covers] at hx

end SetupHelpers

section SetupRun

theorem code_keep [Bindings] {s u w : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hg : ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome)
    {F : Nat → Prop} {O : BitVec 64 → Prop} {L : List Component}
    (hL : StackLocal (sp s) F O L) (hO : ∀ x, O x → ¬ InProgram x) (hag : AgreesExcept L u w)
    (hc : CodeIn Extracted.programImage u) : CodeIn Extracted.programImage w := by
  have hst := frame_stack_writable h hg 0 0x170 (by decide) (by decide)
  simp only [BitVec.add_zero] at hst
  refine CodeIn.of_agreesExcept hag (fun x hx c hc' hcov => ?_) hc
  rcases hL.2.2 c hc' _ hcov with ⟨i, -, hi, he⟩ | ho
  · exact hst.2 i hi (he ▸ MemoryRoutines.Machine.inProgram_of_mem hx)
  · exact hO _ ho (MemoryRoutines.Machine.inProgram_of_mem hx)

theorem chk_keep [Bindings] {s t : RamState} {counter : UInt32} {output : BitVec 64} {n : Nat}
    (hlow : frameBytes ≤ (stackPtr s).toNat) (hc : Checked s t counter output n) {x : BitVec 64}
    (hx : x.toNat < (stackPtr s).toNat - frameBytes ∨ (stackPtr s).toNat ≤ x.toNat) :
    t.external[x]? = s.external[x]? := by
  apply hc.agrees.byte
  intro c hc' hcov
  simp only [prologueChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals try exact hcov
  obtain ⟨j, hj, rfl⟩ := hcov
  simp only [frameBytes] at hlow hj hx
  bv_omega

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
theorem setup [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
    {s : RamState} {key : Vector UInt8 32} {counter : UInt32} {nonce : Vector UInt8 12}
    {input output : BitVec 64} {message : ByteArray} {t : RamState}
    (h : CallPre s key counter nonce input output message)
    (hacc : Accepted counter message.size) (hc : Checked s t counter output message.size) :
    ∃ fuel u, Advances boundary fuel t u ∧
      (if nblocks message.size = 0 then AtTail s key counter nonce input output message u
        else Head s key counter nonce input output message 0 u) := by
  have hb' := hb_cut hb
  have hf := hc.frame
  obtain ⟨hsp1, hsp2⟩ := sp_toNat h
  have hlow := h.stackLow
  have hsz := h.messageLow
  have hol := h.out.low
  simp only [outputRegion] at hol
  have hbl := h.buf.low
  have hcl := h.cipher.low
  simp only [cipherRegion, cipherBytes] at hcl
  have h7t : (Operand.reg 7 : Operand 64).read t = st s :=
    hc.agrees.read (by simp [prologueChanges])
  have h6t : (Operand.reg 6 : Operand 64).read t = rsi.read s :=
    hc.agrees.read (by simp [prologueChanges])
  have hspt : stackPtr t = sp s := hf.rsp
  have xf : ∀ w : RamState, (∀ x : BitVec 64, (s.external[x]?).isSome → (w.external[x]?).isSome) →
      stackPtr w = sp s → (Operand.reg 7 : Operand 64).read w = st s →
      (Operand.reg 6 : Operand 64).read w = rsi.read s →
      XFrame (sp s) (st s) (rsi.read s) w := by
    intro w hg hsw h7 h6
    have hst := frame_stack_writable h hg 0 0x170 (by decide) (by decide)
    simp only [BitVec.add_zero] at hst
    have hcw := region_writable h.cipher hg 0 0x80 (by decide) (by simp [cipherRegion, cipherBytes])
    rw [← st_eq] at hcw
    exact ⟨by rw [Cuts.Tail.rspOf_eq, hsw], h7, h6, hst.1, hst.2, hcw.1, hcw.2,
      ⟨h.buf.low, fun i hi => hg _ (h.buf.mem i hi)⟩⟩
  have hcode0 := region_writable h.cipher (fun x hx => hx) 0x40 1 (by decide)
    (by simp [cipherRegion, cipherBytes])
  have hposNC : ∀ x, PosByte (st s) x → ¬ InProgram x := by
    rintro x ⟨k, hk, rfl⟩
    have := hcode0.2 k hk
    have he : BitVec.ofNat 64 ((cipherRegion s).start + 0x40) = st s + 0x40 := by
      simp only [cipherRegion, st]
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    rwa [he] at this
                         
  obtain ⟨u1, a1, r1, c1, e1⟩ := Cuts.Tail.step (boundary := boundary)
    (cmp_r64_r64_effect_step 0x100ad0 0x4d 0xd3 (by unfold RexWPrefix; decide) (by decide))
    hf.ready hf.code (MemoryRoutines.Machine.program_text_slice hf.code 0xad0 3 (by decide +kernel))
    hc.rip
    (by
      intro he
      apply Cuts.Tail.ne_boundary hb' (p := 0x100ad3) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have g1 := e1.agrees
  simp only [cmpR64R64Effect_components] at g1
  have hCF : condHolds 2 (StatusFlags.ofRFLAGS u1.RFLAGS) = false := by
    have hz := e1.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect, StatusFlagsOutcome.Allows,
      StatusFlagsOutcome.ofStatusFlags, FlagAllows] at hz
    rw [condHolds_2, hz.1, show gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xd3) = 10 from
      by decide, hc.consumed]
    simp [cmpSpec, subSpec]
                                       
  obtain ⟨u2, a2, r2, c2, e2⟩ := Cuts.Tail.step (boundary := boundary)
    (cmov_r64_r64_effect_step 0x100ad3 2 0x4d (by unfold RexWPrefix; decide) 0xd3 (by decide) false)
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0xad3 4 (by decide +kernel))
    ⟨e1.rip.trans rfl, hCF⟩
    (by
      intro he
      apply Cuts.Tail.ne_boundary hb' (p := 0x100ad7) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have g2 := e2.agrees
  simp only [cmovR64R64Effect_components,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xd3) = 10 from by decide] at g2
  have h10u2 : (Operand.reg 10 : Operand 64).read u2 = 0 := by
    have hw := e2.writes
    simp only [cmovR64R64Effect, Write.AllHold,
      show gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xd3) = 10 from by decide] at hw
    rw [hw]
    simp only [Bool.false_eq_true, ite_false]
    rw [g1.read (by simp)]
    exact hc.consumed
  have g12 := g1.trans g2
  have hext2 : u2.external = t.external := g12.external (by simp [Component.Covers])
  have hgt : ∀ x : BitVec 64, (s.external[x]?).isSome → (t.external[x]?).isSome :=
    fun x hx => hf.agrees.grow x hx
  have hg2 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u2.external[x]?).isSome :=
    fun x hx => g12.grow x (hgt x hx)
  have hss : Cuts.Tail.StackStateApart (sp s) (st s) :=
    Cuts.Tail.stackStateApart (space_of h hgt hspt).stateStack
  have hbufk : ∀ i < 24, t.external[rsi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
    intro i hi
    apply chk_keep hlow hc
    have := h.bufStack ((rsi.read s).toNat + i) (by simp only [bufRegion, MemoryRegion.Contains]; omega)
    simp only [stackRegion, MemoryRegion.Contains] at this
    rw [add_toNat_lt (by omega)]; unfold frameBytes at *; omega
  have hword (o : Nat) (ho : o ≤ 16) (v : BitVec 64)
      (hv : (⟨(rsi.read s).toNat + o, 8⟩ : MemoryRegion).Word64At s.external v) :
      (Operand.mem (rsi.read s + BitVec.ofNat 64 o) : Operand 64).read u2 = v := by
    change memLoad u2.external _ 64 = v
    rw [hext2, ← ChaCha20Poly1305.Proofs.Refine.memLoad_of_word64At hv]
    rw [show BitVec.ofNat 64 ((rsi.read s).toNat + o) = rsi.read s + BitVec.ofNat 64 o by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    apply memLoad_congr
    intro i hi
    simp only [memByte, PhysicalMemory.read]
    rw [Cuts.Tail.tail_add, hbufk (o + i) (by omega)]
  have hapB (o : Nat) (ho : o ≤ 16) (m : Ram) (v : BitVec 8) :
      memLoad (memStore m (st s + 0x40) v) (rsi.read s + BitVec.ofNat 64 o) 64 =
        memLoad m (rsi.read s + BitVec.ofNat 64 o) 64 := by
    apply memLoad_memStore_of_rangeApart
    apply rangeApart_of (by unfold st; bv_omega) (by bv_omega)
    intro i hi j hj he
    have ht : (st s + 0x40).toNat = (st s).toNat + 0x40 := by unfold st at *; bv_omega
    rw [ht, add_toNat_lt (by omega)] at he
    exact h.cipherBuf ((st s).toNat + 0x40 + i)
      (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st]; omega)
      (by simp only [bufRegion, MemoryRegion.Contains]; omega)
            
  obtain ⟨effA, hBA, hPA⟩ := blockA boundary hb' (sp s) (st s) (rsi.read s)
  have hcA : CodeIn (codeRange 0x100ad7 blockABytes) u2 := by
    have h' := MemoryRoutines.Machine.program_text_slice c2 0xad7 39
      (by rw [Cuts.Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xad7 39 = blockABytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xad7 = 0x100ad7 from by decide] at h'
  have hsp2' : stackPtr u2 = sp s := (Cuts.Tail.stackPtr_agrees g12 (by simp)).trans hspt
  have h7u2 : (Operand.reg 7 : Operand 64).read u2 = st s := (g12.read (by simp)).trans h7t
  have h6u2 : (Operand.reg 6 : Operand 64).read u2 = rsi.read s := (g12.read (by simp)).trans h6t
  obtain ⟨fA, u3, aA, r3, -, heA⟩ := hBA u2 r2 hcA ⟨e2.rip.trans rfl, xf u2 hg2 hsp2' h7u2 h6u2⟩
  obtain ⟨ipA, wA, gA, zA⟩ := hPA (BitVec.ofNat 64 message.size) input output u2 u3
    (by rw [Cuts.Tail.rspOf_eq, hsp2']) h7u2 h6u2 hss
    (fun m v => by simpa using hapB 0 (by decide) m v) (fun m v => hapB 8 (by decide) m v)
    ((g12.read (by simp)).trans hc.length) h10u2 ((g12.read (by simp)).trans hc.position)
    (by simpa using hword 0 (by decide) input (by simpa [inPtrSlot, rsi] using h.inPtr))
    (hword 8 (by decide) output (by simpa [outPtrSlot, rsi] using h.outPtr)) heA
  have hspu3 : stackPtr u3 = sp s := (Cuts.Tail.stackPtr_agrees gA (by simp)).trans hsp2'
  have h7u3 : (Operand.reg 7 : Operand 64).read u3 = st s := (gA.read (by simp)).trans h7u2
  have h6u3 : (Operand.reg 6 : Operand 64).read u3 = rsi.read s := (gA.read (by simp)).trans h6u2
  have hg3 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u3.external[x]?).isSome :=
    fun x hx => gA.grow x (hg2 x hx)
  have c3 := code_keep h hg2 (localA (sp s) (st s)) hposNC gA c2
                                 
  obtain ⟨u4, a4, r4, c4, e4⟩ := Cuts.Tail.step (boundary := boundary)
    (jcc_rel32_effect_step 0x100afe 4 0xa1) r3 c3
    (MemoryRoutines.Machine.program_text_slice c3 0xafe 6 (by decide +kernel))
    ⟨ipA, fun _ => by decide⟩
    (by
      simp only [jccEffect, branchEffect, condHolds_4, zA, ite_true]
      exact Cuts.Tail.ne_boundary hb' (by decide) (by decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g4 := e4.agrees
  simp only [jccEffect, branchEffect_components] at g4
  have hip4 : u4.RIP = 0x100ba5 := by
    rw [e4.rip]; simp only [jccEffect, branchEffect, condHolds_4, zA, ite_true]; decide
  have hext4 : u4.external = u3.external := g4.external (by simp [Component.Covers])
  have rd4 (r : BitVec 5) : (Operand.reg r : Operand 64).read u4 = (Operand.reg r : Operand 64).read u3 :=
    g4.read (by simp)
  have hspu4 : stackPtr u4 = sp s := (Cuts.Tail.stackPtr_agrees g4 (by simp)).trans hspu3
  have hg4 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u4.external[x]?).isSome :=
    fun x hx => g4.grow x (hg3 x hx)
  simp only [Write.AllHold] at wA
  obtain ⟨wA3, wA14, wA11, wA10, wA50, wA15⟩ := wA
            
  obtain ⟨effB, hBB, hPB⟩ := blockB boundary hb' (sp s) (st s) (rsi.read s)
  have hcB : CodeIn (codeRange 0x100ba5 blockBBytes) u4 := by
    have h' := MemoryRoutines.Machine.program_text_slice c4 0xba5 51
      (by rw [Cuts.Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xba5 51 = blockBBytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xba5 = 0x100ba5 from by decide] at h'
  obtain ⟨fB, u5, aB, r5, -, heB⟩ := hBB u4 r4 hcB
    ⟨hip4, xf u4 hg4 hspu4 ((rd4 7).trans h7u3) ((rd4 6).trans h6u3)⟩
  have h50u4 : (Operand.mem (sp s + 0x50) : Operand 64).read u4 =
      BitVec.ofNat 64 message.size >>> 6 := by
    change memLoad u4.external _ 64 = _
    rw [hext4]; exact wA50
  obtain ⟨ipB, wB, gB, zB⟩ := hPB _ _ _ _ _ _ u4 u5 (by rw [Cuts.Tail.rspOf_eq, hspu4])
    ((rd4 7).trans h7u3) h50u4 ((rd4 10).trans wA10) ((rd4 11).trans wA11)
    ((rd4 3).trans wA3) ((rd4 14).trans wA14) ((rd4 15).trans wA15) heB
  have hspu5 : stackPtr u5 = sp s := (Cuts.Tail.stackPtr_agrees gB (by simp)).trans hspu4
  have hg5 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u5.external[x]?).isSome :=
    fun x hx => gB.grow x (hg4 x hx)
  have c5 := code_keep h hg4 (localB (sp s)) (fun _ h => h.elim) gB
    (code_keep h hg3 (localRegs (sp s) [.rip] (by simp [Cuts.Rounds.regScratch]))
      (fun _ h => h.elim) g4 c3)
  have hnb0 : (BitVec.ofNat 64 message.size >>> 6 == 0) = decide (nblocks message.size = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq]
    unfold nblocks
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow] at this
      simpa using this
    · intro he
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
      simpa using he
  rw [hnb0] at zB
                                            
  have hjr : (jccEffect 0x100bd8 6 4 ((0x4ee : BitVec 32).signExtend 64) u5).rip =
      if nblocks message.size = 0 then 0x1010cc else 0x100bde := by
    by_cases hq : nblocks message.size = 0
    · simp only [hq, ↓reduceIte]
      simp only [jccEffect, branchEffect, condHolds_4, zB, hq, decide_true, ite_true]
      decide
    · simp only [hq, ↓reduceIte]
      simp only [jccEffect, branchEffect, condHolds_4, zB, hq, decide_false, Bool.false_eq_true,
        ite_false]
      decide
  obtain ⟨u6, a6, r6, c6, e6⟩ := Cuts.Tail.step (boundary := boundary)
    (jcc_rel32_effect_step 0x100bd8 4 0x4ee) r5 c5
    (MemoryRoutines.Machine.program_text_slice c5 0xbd8 6 (by decide +kernel))
    ⟨ipB, fun _ => by decide⟩
    (by
      rw [hjr]
      split
      · exact Cuts.Tail.ne_boundary hb' (by decide) (by decide)
      · exact Cuts.Tail.ne_boundary hb' (by decide) (by decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g6 := e6.agrees
  simp only [jccEffect, branchEffect_components] at g6
  have hip6 := e6.rip.trans hjr
  have hext6 : u6.external = u5.external := g6.external (by simp [Component.Covers])
  have rd6 (r : BitVec 5) : (Operand.reg r : Operand 64).read u6 = (Operand.reg r : Operand 64).read u5 :=
    g6.read (by simp)
  have rdB (r : BitVec 5) (hr : r ≠ 4) :
      (Operand.reg r : Operand 64).read u5 = (Operand.reg r : Operand 64).read u4 :=
    gB.read (by simp)
  have hspu6 : stackPtr u6 = sp s := (Cuts.Tail.stackPtr_agrees g6 (by simp)).trans hspu5
  have hg6 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u6.external[x]?).isSome :=
    fun x hx => g6.grow x (hg5 x hx)
  have posO : ∀ x, PosByte (st s) x → (∃ c ∈ callChanges s output message.size, c.Covers x) ∧
      (x.toNat < (sp s).toNat ∨ (sp s).toNat + frameBytes ≤ x.toNat) := by
    rintro x ⟨k, hk, rfl⟩
    refine ⟨⟨.mem (rdi.read s + 0x40) 0x40, by simp [callChanges], k, by omega, rfl⟩, ?_⟩
    have ht : (st s + 0x40 + BitVec.ofNat 64 k).toNat = (st s).toNat + 0x40 + k := by
      unfold st at *; bv_omega
    have := h.cipherStack ((st s).toNat + 0x40 + k)
      (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st]; omega)
    rw [ht, hsp1]
    simp only [stackRegion, MemoryRegion.Contains] at this ⊢
    unfold frameBytes at *
    omega
  have ft : ∀ {u w : RamState} {F : Nat → Prop} {O : BitVec 64 → Prop} {L : List Component},
      Frame s u output message.size → StackLocal (sp s) F O L → (∀ x, O x → PosByte (st s) x) →
      AgreesExcept L u w → ReadyToStep w → CodeIn Extracted.programImage w →
      Frame s w output message.size :=
    fun hfu hL hO hag hr hc => frame_transfer h hfu hL (fun x hx => posO x (hO x hx)) hag hr hc
  have kp : ∀ {u w : RamState} {F : Nat → Prop} {O : BitVec 64 → Prop} {L : List Component},
      StackLocal (sp s) F O L → (∀ x, O x → PosByte (st s) x) → AgreesExcept L u w →
      ∀ {r : MemoryRegion}, r.Disjoint (stackRegion s) → ∀ {x : BitVec 64}, r.Contains x.toNat →
      ¬ PosByte (st s) x → w.external[x]? = u.external[x]? :=
    fun hL hO hag _ hd _ hx hnp => keep_far h hL hag hd hx (fun ho => hnp (hO _ ho))
  have regsL (L : List Component) (hL : ∀ c ∈ L, c ∈ Cuts.Rounds.regScratch) :=
    localRegs (sp s) L hL
  have hfr6 : Frame s u6 output message.size :=
    ft (ft (ft (ft (ft (ft hf (regsL _ (by simp [Cuts.Rounds.regScratch])) (fun _ h => h.elim) g1 r1 c1)
      (regsL _ (by simp [Cuts.Rounds.regScratch])) (fun _ h => h.elim) g2 r2 c2)
      (localA (sp s) (st s)) (fun _ h => h) gA r3 c3)
      (regsL _ (by simp [Cuts.Rounds.regScratch])) (fun _ h => h.elim) g4 r4 c4)
      (localB (sp s)) (fun _ h => h.elim) gB r5 c5)
      (regsL _ (by simp [Cuts.Rounds.regScratch])) (fun _ h => h.elim) g6 r6 c6
  have chain6 : ∀ {r : MemoryRegion}, r.Disjoint (stackRegion s) → ∀ {x : BitVec 64},
      r.Contains x.toNat → ¬ PosByte (st s) x → u6.external[x]? = s.external[x]? := by
    intro r hd x hx hnp
    rw [hext6, kp (localB (sp s)) (fun _ h => h.elim) gB hd hx hnp, hext4,
      kp (localA (sp s) (st s)) (fun _ h => h) gA hd hx hnp, hext2]
    apply chk_keep hlow hc
    have := hd _ hx
    simp only [stackRegion, MemoryRegion.Contains] at this
    unfold frameBytes at *
    omega
  have words_nP : ∀ i < 0x40, ¬ PosByte (st s) (st s + BitVec.ofNat 64 i) := by
    rintro i hi ⟨k, hk, he⟩
    have := congrArg BitVec.toNat he
    have ht : (st s + 0x40 + BitVec.ofNat 64 k).toNat = (st s).toNat + 0x40 + k := by
      unfold st at *; bv_omega
    rw [add_toNat_lt (by unfold st at *; omega), ht] at this
    omega
  have in_nP : ∀ i < message.size, ¬ PosByte (st s) (input + BitVec.ofNat 64 i) := by
    rintro i hi ⟨k, hk, he⟩
    have := congrArg BitVec.toNat he
    have ht : (st s + 0x40 + BitVec.ofNat 64 k).toNat = (st s).toNat + 0x40 + k := by
      unfold st at *; bv_omega
    rw [add_toNat_lt (by omega), ht] at this
    exact h.inputCipher (input.toNat + i)
      (by simp only [inputRegion, MemoryRegion.Contains]; omega)
      (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st] at this ⊢; omega)
  have hstate6 : (wordsRegion s).HasBytes u6.external (stateBytes key counter nonce) :=
    hasBytes_keep h.words fun i hi => chain6 h.cipherStack (by
      simp only [cipherRegion, cipherBytes, MemoryRegion.Contains]
      rw [add_toNat_lt (by unfold st at *; omega)]; unfold st; omega) (words_nP i hi)
  have hrest6 : ∀ i < message.size, u6.external[input + BitVec.ofNat 64 i]? = some (msg message i) := by
    intro i hi
    rw [chain6 h.inputStack (by
      simp only [inputRegion, MemoryRegion.Contains]; rw [add_toNat_lt (by omega)]; omega) (in_nP i hi)]
    have := h.messageBytes.2 ⟨i, hi⟩
    simp only [inputRegion] at this
    rw [show input + BitVec.ofNat 64 i = BitVec.ofNat 64 (input.toNat + i) by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq], this]
    simp [msg, getElem!_pos message i hi]
  simp only [Write.AllHold] at wB
  obtain ⟨wB48, wB98, wBa8, wB90, wB88, wBa0⟩ := wB
  have htail : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 message.size) &&& 63) =
      BitVec.ofNat 64 (Cuts.Tail.tail message.size) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Cuts.Tail.tail]
    rw [show BitVec.toNat (63 : BitVec 32) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hslot6 (o : Nat) (v : BitVec 64) (hv : memLoad u5.external (sp s + o) 64 = v) :
      Cuts.Tail.slot64 u6 (sp s) o = v := by
    unfold Cuts.Tail.slot64 Cuts.Tail.slot; rw [hext6]; exact hv
  have hslots6 : Cuts.Tail.Slots (sp s) (st s) input output message.size u6 :=
    ⟨hslot6 0x48 _ wB48, hslot6 0x88 _ wB88, hslot6 0x90 _ wB90, hslot6 0x98 _ wB98,
      by rw [hslot6 0xa0 _ wBa0, htail], hslot6 0xa8 _ wBa8⟩
  by_cases hq : nblocks message.size = 0
  · simp only [hq, ↓reduceIte] at hip6 ⊢
    refine ⟨_, u6, ((((a1.trans a2).trans aA).trans a4).trans aB).trans a6, ?_⟩
    have hbase : Cuts.Tail.base message.size = 0 := by
      unfold Cuts.Tail.base; unfold nblocks at hq; rw [hq]
    exact { frame := hfr6
            cut := { rip := hip6
                     space := space_of h hg6 hspu6
                     slots := hslots6
                     state := (rd6 7).trans ((rdB 7 (by decide)).trans ((rd4 7).trans h7u3))
                     length := (rd6 11).trans ((rdB 11 (by decide)).trans ((rd4 11).trans wA11))
                     tail := by
                       rw [show Cuts.Tail.reg64 u6 15 = (Operand.reg 15 : Operand 64).read u6
                         from rfl, rd6, rdB 15 (by decide), rd4, wA15, htail]
                     words := by
                       rw [hq, words_zero]
                       exact fun i => state_bytesAt hstate6 i
                     rest := by
                       rw [hbase]
                       intro i _ hi
                       exact hrest6 i hi }
            wrote := by rw [hq]; intro i hi; omega }
  · simp only [hq, ↓reduceIte] at hip6 ⊢
    have hx0 : ∀ w : RamState, (wordsRegion s).HasBytes w.external (stateBytes key counter nonce) →
        Write.AllHold w (Cuts.Rounds.cut (st s) Cuts.Tail.stL (words key counter nonce 0)) := by
      intro w hw
      have hb := Cuts.Tail.load_word (fun i => state_bytesAt hw i)
      rw [← words_zero] at hb
      simp only [Cuts.Rounds.cut, Cuts.Tail.stL, List.map, Cuts.Rounds.Loc.op, Write.AllHold]
      exact ⟨hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
        hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide), hb 9 (by decide),
        hb 10 (by decide), hb 11 (by decide), hb 12 (by decide), hb 13 (by decide),
        hb 14 (by decide), hb 15 (by decide)⟩
    have hsst : ∀ {u w : RamState} {F : Nat → Prop} {L : List Component},
        StackLocal (sp s) F (fun _ => False) L → AgreesExcept L u w →
        (wordsRegion s).HasBytes u.external (stateBytes key counter nonce) →
        (wordsRegion s).HasBytes w.external (stateBytes key counter nonce) :=
      fun hL hag hu => hasBytes_keep hu fun i hi => kp hL (fun _ h => h.elim) hag h.cipherStack (by
        simp only [cipherRegion, cipherBytes, MemoryRegion.Contains]
        rw [add_toNat_lt (by unfold st at *; omega)]; unfold st; omega) (words_nP i hi)
               
    obtain ⟨effC1, hBC1, hPC1⟩ := blockC1 boundary hb' (sp s) (st s) (rsi.read s)
    have hcC1 : CodeIn (codeRange 0x100bde blockC1Bytes) u6 := by
      have h' := MemoryRoutines.Machine.program_text_slice c6 0xbde 49
        (by rw [Cuts.Rounds.textBytes_size_eq]; omega)
      rwa [show Extracted.textBytes.toListFrom 0xbde 49 = blockC1Bytes from by decide +kernel,
        show Extracted.textAddress + BitVec.ofNat 64 0xbde = 0x100bde from by decide] at h'
    have h7u6 : (Operand.reg 7 : Operand 64).read u6 = st s :=
      (rd6 7).trans ((rdB 7 (by decide)).trans ((rd4 7).trans h7u3))
    have h6u6 : (Operand.reg 6 : Operand 64).read u6 = rsi.read s :=
      (rd6 6).trans ((rdB 6 (by decide)).trans ((rd4 6).trans h6u3))
    obtain ⟨fC1, u7, aC1, r7, -, heC1⟩ := hBC1 u6 r6 hcC1 ⟨hip6, xf u6 hg6 hspu6 h7u6 h6u6⟩
    obtain ⟨ip7, wC1, gC1⟩ := hPC1 input output (words key counter nonce 0) u6 u7
      (by rw [Cuts.Tail.rspOf_eq, hspu6]) h7u6 hss
      ((rd6 3).trans ((rdB 3 (by decide)).trans ((rd4 3).trans wA3)))
      ((rd6 14).trans ((rdB 14 (by decide)).trans ((rd4 14).trans wA14)))
      ((rd6 10).trans ((rdB 10 (by decide)).trans ((rd4 10).trans wA10)))
      (hx0 u6 hstate6) heC1
    have hspu7 : stackPtr u7 = sp s := (Cuts.Tail.stackPtr_agrees gC1 (by simp)).trans hspu6
    have hg7 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u7.external[x]?).isSome :=
      fun x hx => gC1.grow x (hg6 x hx)
    have c7 := code_keep h hg6 (localC1 (sp s)) (fun _ h => h.elim) gC1 c6
    have hstate7 := hsst (localC1 (sp s)) gC1 hstate6
    have h7u7 : (Operand.reg 7 : Operand 64).read u7 = st s := (gC1.read (by simp)).trans h7u6
    have h6u7 : (Operand.reg 6 : Operand 64).read u7 = rsi.read s := (gC1.read (by simp)).trans h6u6
    simp only [Write.AllHold] at wC1
    obtain ⟨wC68, wC60, wC58, wC10, wC0c, wC40, wC10r⟩ := wC1
                
    obtain ⟨effC2a, hBC2a, hPC2a⟩ := blockC2a boundary hb' (sp s) (st s) (rsi.read s)
    have hcC2a : CodeIn (codeRange 0x100c0f blockC2aBytes) u7 := by
      have h' := MemoryRoutines.Machine.program_text_slice c7 0xc0f 46
        (by rw [Cuts.Rounds.textBytes_size_eq]; omega)
      rwa [show Extracted.textBytes.toListFrom 0xc0f 46 = blockC2aBytes from by decide +kernel,
        show Extracted.textAddress + BitVec.ofNat 64 0xc0f = 0x100c0f from by decide] at h'
    obtain ⟨fC2a, u8, aC2a, r8, -, heC2a⟩ := hBC2a u7 r7 hcC2a ⟨ip7, xf u7 hg7 hspu7 h7u7 h6u7⟩
    obtain ⟨ip8, wC2a, gC2a⟩ := hPC2a (words key counter nonce 0) u7 u8
      (by rw [Cuts.Tail.rspOf_eq, hspu7]) h7u7 hss (hx0 u7 hstate7) heC2a
    have hspu8 : stackPtr u8 = sp s := (Cuts.Tail.stackPtr_agrees gC2a (by simp)).trans hspu7
    have hg8 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u8.external[x]?).isSome :=
      fun x hx => gC2a.grow x (hg7 x hx)
    have c8 := code_keep h hg7 (localC2a (sp s)) (fun _ h => h.elim) gC2a c7
    have hstate8 := hsst (localC2a (sp s)) gC2a hstate7
    have h7u8 : (Operand.reg 7 : Operand 64).read u8 = st s := (gC2a.read (by simp)).trans h7u7
    have h6u8 : (Operand.reg 6 : Operand 64).read u8 = rsi.read s := (gC2a.read (by simp)).trans h6u7
    simp only [Write.AllHold] at wC2a
    obtain ⟨wC34, wC30, wC2c, wC11r, wC28, wC24, wC20⟩ := wC2a
                
    obtain ⟨effC2b, hBC2b, hPC2b⟩ := blockC2b boundary hb' (sp s) (st s) (rsi.read s)
    have hcC2b : CodeIn (codeRange 0x100c3d blockC2bBytes) u8 := by
      have h' := MemoryRoutines.Machine.program_text_slice c8 0xc3d 51
        (by rw [Cuts.Rounds.textBytes_size_eq]; omega)
      rwa [show Extracted.textBytes.toListFrom 0xc3d 51 = blockC2bBytes from by decide +kernel,
        show Extracted.textAddress + BitVec.ofNat 64 0xc3d = 0x100c3d from by decide] at h'
    obtain ⟨fC2b, u9, aC2b, r9, -, heC2b⟩ := hBC2b u8 r8 hcC2b ⟨ip8, xf u8 hg8 hspu8 h7u8 h6u8⟩
    have h10u8 : (Operand.reg 10 : Operand 64).read u8 =
        (words key counter nonce 0)[4].toBitVec.setWidth 64 := (gC2a.read (by simp)).trans wC10r
    obtain ⟨ip9, wC2b, gC2b⟩ := hPC2b (words key counter nonce 0) u8 u9
      (by rw [Cuts.Tail.rspOf_eq, hspu8]) h7u8 hss
      (by rw [reg32_of_64 h10u8])
      (by rw [reg32_of_64 wC11r])
      (hx0 u8 hstate8) heC2b
    have hspu9 : stackPtr u9 = sp s := (Cuts.Tail.stackPtr_agrees gC2b (by simp)).trans hspu8
    have c9 := code_keep h hg8 (localC2b (sp s)) (fun _ h => h.elim) gC2b c8
    have hfr9 : Frame s u9 output message.size :=
      ft (ft (ft hfr6 (localC1 (sp s)) (fun _ h => h.elim) gC1 r7 c7)
        (localC2a (sp s)) (fun _ h => h.elim) gC2a r8 c8) (localC2b (sp s)) (fun _ h => h.elim) gC2b r9 c9
    simp only [Write.AllHold] at wC2b
    obtain ⟨wC8r, wC1c, wC18, wC7r, wC38, wC84, wC80⟩ := wC2b
    have k9 (n o : Nat) (ho : o + n / 8 < 0x100)
        (hF : ∀ i < n / 8, ¬ ((0x18 ≤ o + i ∧ o + i < 0x20) ∨ (0x38 ≤ o + i ∧ o + i < 0x3c) ∨
          (0x80 ≤ o + i ∧ o + i < 0x88))) :
        memLoad u9.external (sp s + BitVec.ofNat 64 o) n = memLoad u8.external (sp s + BitVec.ofNat 64 o) n :=
      (localC2b (sp s)).load gC2b n o (by omega) hF (fun _ _ h => h)
    have k8 (n o : Nat) (ho : o + n / 8 < 0x100) (hF : ∀ i < n / 8, ¬ (0x20 ≤ o + i ∧ o + i < 0x38)) :
        memLoad u8.external (sp s + BitVec.ofNat 64 o) n = memLoad u7.external (sp s + BitVec.ofNat 64 o) n :=
      (localC2a (sp s)).load gC2a n o (by omega) hF (fun _ _ h => h)
    have k7 (n o : Nat) (ho : o + n / 8 < 0x100)
        (hF : ∀ i < n / 8, ¬ ((0x58 ≤ o + i ∧ o + i < 0x5c) ∨ (0x60 ≤ o + i ∧ o + i < 0x70) ∨
          (0xc ≤ o + i ∧ o + i < 0x14) ∨ (0x40 ≤ o + i ∧ o + i < 0x44))) :
        memLoad u7.external (sp s + BitVec.ofNat 64 o) n = memLoad u6.external (sp s + BitVec.ofNat 64 o) n :=
      (localC1 (sp s)).load gC1 n o (by omega) hF (fun _ _ h => h)
    have k5 (n o : Nat) (ho : o + n / 8 < 0x100)
        (hF : ∀ i < n / 8, ¬ ((0x48 ≤ o + i ∧ o + i < 0x50) ∨ (0x88 ≤ o + i ∧ o + i < 0xb0))) :
        memLoad u5.external (sp s + BitVec.ofNat 64 o) n = memLoad u4.external (sp s + BitVec.ofNat 64 o) n :=
      (localB (sp s)).load gB n o (by omega) hF (fun _ _ h => h.elim)
    have kall (o : Nat) (ho : o + 8 < 0x100)
        (h1 : ∀ i < 8, ¬ ((0x18 ≤ o + i ∧ o + i < 0x20) ∨ (0x38 ≤ o + i ∧ o + i < 0x3c) ∨
          (0x80 ≤ o + i ∧ o + i < 0x88)))
        (h2 : ∀ i < 8, ¬ (0x20 ≤ o + i ∧ o + i < 0x38))
        (h3 : ∀ i < 8, ¬ ((0x58 ≤ o + i ∧ o + i < 0x5c) ∨ (0x60 ≤ o + i ∧ o + i < 0x70) ∨
          (0xc ≤ o + i ∧ o + i < 0x14) ∨ (0x40 ≤ o + i ∧ o + i < 0x44))) :
        memLoad u9.external (sp s + BitVec.ofNat 64 o) 64 = memLoad u6.external (sp s + BitVec.ofNat 64 o) 64 := by
      rw [k9 64 o (by omega) h1, k8 64 o (by omega) h2, k7 64 o (by omega) h3]
    have hrest9 : ∀ i < message.size, u9.external[input + BitVec.ofNat 64 i]? = some (msg message i) := by
      intro i hi
      have hx : (inputRegion input message.size).Contains (input + BitVec.ofNat 64 i).toNat := by
        simp only [inputRegion, MemoryRegion.Contains]; rw [add_toNat_lt (by omega)]; omega
      rw [kp (localC2b (sp s)) (fun _ h => h.elim) gC2b h.inputStack hx (in_nP i hi),
        kp (localC2a (sp s)) (fun _ h => h.elim) gC2a h.inputStack hx (in_nP i hi),
        kp (localC1 (sp s)) (fun _ h => h.elim) gC1 h.inputStack hx (in_nP i hi)]
      exact hrest6 i hi
    have hr12 : Cuts.Xor.reg64 u9 12 = (words key counter nonce 0)[12].toBitVec.setWidth 64 := by
      have hz : counter + (0 : Nat).toUInt32 = counter := by
        apply UInt32.toNat_inj.mp; simp
      rw [words_12, hz]
      change (Operand.reg 12 : Operand 64).read u9 = _
      rw [gC2b.read (by simp), gC2a.read (by simp), gC1.read (by simp), rd6, rdB 12 (by decide), rd4,
        gA.read (by simp), g12.read (by simp)]
      exact hc.counter
    refine ⟨_, u9, (((((((a1.trans a2).trans aA).trans a4).trans aB).trans a6).trans aC1).trans aC2a).trans aC2b, ?_⟩
    refine { frame := hfr9, rip := ip9, lt := by omega, rdi := wC7r, r12 := hr12,
             r10 := (gC2b.read (by simp)).trans h10u8, r11 := (gC2b.read (by simp)).trans wC11r,
             r8 := wC8r, inits := ?_, inSlot := ?_, outSlot := ?_, count := ?_, slots := ?_,
             state := hsst (localC2b (sp s)) gC2b hstate8,
             rest := fun i _ hi => hrest9 i hi, wrote := fun i hi => by omega }
    · intro e he h12
      simp only [Cuts.Xor.initSlot, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x58 (by omega) (by intro i hi; omega), k8 32 0x58 (by omega) (by intro i hi; omega)]; exact wC58
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x10 (by omega) (by intro i hi; omega), k8 32 0x10 (by omega) (by intro i hi; omega)]; exact wC10
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0xc (by omega) (by intro i hi; omega), k8 32 0xc (by omega) (by intro i hi; omega)]; exact wC0c
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x40 (by omega) (by intro i hi; omega), k8 32 0x40 (by omega) (by intro i hi; omega)]; exact wC40
      · rw [slot32_read hspu9]; exact wC38
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x34 (by omega) (by intro i hi; omega)]; exact wC34
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x30 (by omega) (by intro i hi; omega)]; exact wC30
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x2c (by omega) (by intro i hi; omega)]; exact wC2c
      · rw [slot32_read hspu9]; exact wC84
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x28 (by omega) (by intro i hi; omega)]; exact wC28
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x24 (by omega) (by intro i hi; omega)]; exact wC24
      · rw [slot32_read hspu9]; change memLoad _ _ 32 = _; rw [k9 32 0x20 (by omega) (by intro i hi; omega)]; exact wC20
      · exact absurd rfl h12
      · rw [slot32_read hspu9]; exact wC80
      · rw [slot32_read hspu9]; exact wC1c
      · rw [slot32_read hspu9]; exact wC18
    · rw [slot64_read hspu9]; change memLoad _ _ 64 = _
      rw [k9 64 0x68 (by omega) (by intro i hi; omega), k8 64 0x68 (by omega) (by intro i hi; omega)]
      exact wC68
    · rw [slot64_read hspu9]; change memLoad _ _ 64 = _
      rw [k9 64 0x60 (by omega) (by intro i hi; omega), k8 64 0x60 (by omega) (by intro i hi; omega)]
      exact wC60
    · rw [slot64_read hspu9]; change memLoad _ _ 64 = _
      rw [kall 0x50 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega),
        hext6, k5 64 0x50 (by omega) (by intro i hi; omega), hext4]
      have hshift : BitVec.ofNat 64 message.size >>> 6 = BitVec.ofNat 64 (nblocks message.size) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, nblocks]
        rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
      exact wA50.trans hshift
    · have hs6 := hslots6
      exact ⟨(kall 0x48 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)).trans hs6.state,
        (kall 0x88 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)).trans hs6.output,
        (kall 0x90 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)).trans hs6.input,
        (kall 0x98 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)).trans hs6.head,
        (kall 0xa0 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)).trans hs6.tail,
        (kall 0xa8 (by omega) (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)).trans hs6.length⟩

end SetupRun

end ChaCha20Poly1305.Proofs.Callee100a80.Run
