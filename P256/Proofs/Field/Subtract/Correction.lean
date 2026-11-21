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
import P256.Proofs.Field.Montgomery.Reduction.TailCorrespondence
import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.AddByte
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.Instructions.Neg64
import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction (adc carry)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adcSpec_cf adcSpec_result adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Subtract

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem register_after {s t : RamState} {p : BitVec 64} {dst : BitVec 5}
    {value : BitVec 64} {flags : Option StatusFlagsOutcome}
    (h : ({rip := p, writes := [⟨(Operand.reg dst : Operand 64), value⟩], flags := flags} : Effect).Holds s t)
    (r : BitVec 5) :
    (Operand.reg r : Operand 64).read t =
      if r = dst then value else (Operand.reg r : Operand 64).read s := by
  by_cases he : r = dst
  · subst r
    exact (show (Operand.reg dst : Operand 64).read t = value from h.writes).trans
      (by simp)
  · rw [ite_eq_right he]
    apply h.agrees.read
    cases flags <;> simp [Effect.components, he]

theorem read32_eq_read64 (s : RamState) (r : BitVec 5) :
    (Operand.reg r : Operand 32).read s = ((Operand.reg r : Operand 64).read s).setWidth 32 := by
  simp [Operand.read]

theorem carryFlag_eq (s : RamState) :
    s.RFLAGS.extractLsb' 0 1 = BitVec.ofBool (StatusFlags.ofRFLAGS s.RFLAGS).CF :=
  extractLsb'_one_eq_ofBool _ _

theorem setb_zero_value (b : Bool) :
    mergeGPR 8 (if b then 1#8 else 0#8) 0#64 = BitVec.ofNat 64 b.toNat := by
  cases b <;> decide +kernel

structure CorrectionPre (s : RamState) (r : Limbs) (q : BitVec 64) : Prop where
  rip : s.RIP = 0x11400a
  r0 : (Operand.reg 0 : Operand 64).read s = r.l0
  r1 : (Operand.reg 2 : Operand 64).read s = r.l1
  r2 : (Operand.reg 8 : Operand 64).read s = r.l2
  r3 : (Operand.reg 10 : Operand 64).read s = r.l3
  qValue : (Operand.reg 1 : Operand 64).read s = q

def correctionEffect (s : RamState) (r : Limbs) (q : BitVec 64) : Effect :=
  { rip := 0x11403d
    writes := [⟨(Operand.reg 6 : Operand 64), (correct r q).l0⟩,
      ⟨(Operand.reg 1 : Operand 64), -q⟩,
      ⟨(Operand.reg 9 : Operand 64), (correct r q).l1⟩,
      ⟨(Operand.reg 11 : Operand 64), (correct r q).l2⟩,
      ⟨(Operand.reg 2 : Operand 64), (correct r q).l3⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem correction_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {r : Limbs} {q : BitVec 64} (h : CorrectionPre s r q)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (hout : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 14 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (correctionEffect s r q).Holds s t := by
  let k := ((-q).setWidth 32).setWidth 64
  let u := k + r.l1
  let c1 := carry k r.l1 false
  let c0 := decide (r.l0 - q < r.l0)
  let c2 := carry u 0 c0
  let c3 := carry (BitVec.ofNat 64 c1.toNat) r.l2 c2
  have hr0 := h.r0
  have hr1 := h.r1
  have hr2 := h.r2
  have hr3 := h.r3
  have hq := h.qValue
  simp only [BitVec.ofNat_eq_ofNat] at hr0 hr1 hr2 hr3 hq
  have hc0 := programLoaded_codeIn loaded
  obtain ⟨s1, a1, ready1, e1⟩ := (mov_r64_r64_effect_step 0x11400a 0x48 0xc6 (by simp [RexWPrefix]) rfl).advances
    ready (programText_slice hc0 0x1400a [0x48, 0x89, 0xc6] (by decide) (by decide +kernel))
    h.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1400d (by decide)))
  change (movR64R64Effect 0x11400a 6 0 s).Holds s s1 at e1
  have hc1 := e1.codeIn (Effect.Avoids.of_noMem
    (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hc0
  have g1 (v : BitVec 5) : (Operand.reg v : Operand 64).read s1 =
      if v = 6 then r.l0 else (Operand.reg v : Operand 64).read s := by
    have hg := register_after e1 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s2, a2, ready2, e2⟩ := (sub_r64_r64_effect_step 0x11400d 0x48 0xce (by simp [RexWPrefix]) rfl).advances
    ready1 (programText_slice hc1 0x1400d [0x48, 0x29, 0xce] (by decide) (by decide +kernel))
    e1.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14010 (by decide)))
  change (subR64R64Effect 0x11400d 6 1 s1).Holds s1 s2 at e2
  have hc2 := e2.codeIn (Effect.Avoids.of_noMem
    (by simp [subR64R64Effect, Effect.components, Component.Covers]) _) hc1
  have g2 (v : BitVec 5) : (Operand.reg v : Operand 64).read s2 =
      if v = 6 then r.l0 - q else (Operand.reg v : Operand 64).read s1 := by
    have hg := register_after e2 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g1, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s3, a3, ready3, e3⟩ := (P256.Proofs.Common.Instructions.Neg64.neg_rcx_effect_step 0x114010).advances
    ready2 (programText_slice hc2 0x14010 [0x48, 0xf7, 0xd9] (by decide) (by decide +kernel))
    e2.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14013 (by decide)))
  change (P256.Proofs.Common.Instructions.Neg64.negR64Effect 0x114010 1 s2).Holds s2 s3 at e3
  have hc3 := e3.codeIn (Effect.Avoids.of_noMem
    (by simp [P256.Proofs.Common.Instructions.Neg64.negR64Effect, Effect.components, Component.Covers]) _) hc2
  have g3 (v : BitVec 5) : (Operand.reg v : Operand 64).read s3 =
      if v = 1 then -q else (Operand.reg v : Operand 64).read s2 := by
    have hg := register_after e3 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g2, g1, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s4, a4, ready4, e4⟩ := (mov_r32_r32_rex_effect_step 0x114013 0x41 0xc9 (by simp [RexNoWPrefix]) rfl).advances
    ready3 (programText_slice hc3 0x14013 [0x41, 0x89, 0xc9] (by decide) (by decide +kernel))
    e3.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14016 (by decide)))
  change (movR32R32Effect 0x114013 3 9 1 s3).Holds s3 s4 at e4
  have hc4 := e4.codeIn (Effect.Avoids.of_noMem
    (by simp [movR32R32Effect, Effect.components, Component.Covers]) _) hc3
  have g4 (v : BitVec 5) : (Operand.reg v : Operand 64).read s4 =
      if v = 9 then k else (Operand.reg v : Operand 64).read s3 := by
    have hg := register_after e4 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g3, g2, g1, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s5, a5, ready5, e5⟩ := (xor_r32_r32_rex_effect_step 0x114016 0x45 0xdb (by simp [RexNoWPrefix]) rfl).advances
    ready4 (programText_slice hc4 0x14016 [0x45, 0x31, 0xdb] (by decide) (by decide +kernel))
    e4.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14019 (by decide)))
  change (xorR32R32Effect 0x114016 3 11 11 s4).Holds s4 s5 at e5
  have hc5 := e5.codeIn (Effect.Avoids.of_noMem
    (by simp [xorR32R32Effect, Effect.components, Component.Covers]) _) hc4
  have g5 (v : BitVec 5) : (Operand.reg v : Operand 64).read s5 =
      if v = 11 then 0 else (Operand.reg v : Operand 64).read s4 := by
    have hg := register_after e5 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g4, g3, g2, g1, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s6, a6, ready6, e6⟩ := (add_r64_r64_effect_step 0x114019 0x49 0xd1 (by simp [RexWPrefix]) rfl).advances
    ready5 (programText_slice hc5 0x14019 [0x49, 0x1, 0xd1] (by decide) (by decide +kernel))
    e5.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1401c (by decide)))
  change (addR64R64Effect 0x114019 9 2 s5).Holds s5 s6 at e6
  have hc6 := e6.codeIn (Effect.Avoids.of_noMem
    (by simp [addR64R64Effect, Effect.components, Component.Covers]) _) hc5
  have g6 (v : BitVec 5) : (Operand.reg v : Operand 64).read s6 =
      if v = 9 then u else (Operand.reg v : Operand 64).read s5 := by
    have hg := register_after e6 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g5, g4, g3, g2, g1, k, u, c0, c1, c2, c3] using hg
  have cf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = c1 := by
    have hf : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read s5) ((Operand.reg 2 : Operand 64).read s5)).2.CF := e6.flags.1
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, addSpec_cf_carry, cmpSpec, subSpec, carryFlag_eq, adcSpec_cf_ofBool,
      read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g5, g4, g3, g2, g1, k, u, c0, c1, c2, c3] using hf
  obtain ⟨s7, a7, ready7, e7⟩ := (P256.Proofs.Common.Instructions.Setb.setcc_r8_rex_effect_step 0x11401c 0x41 0x92 0xc3 (by simp [RexPrefix]) (.inl rfl) rfl).advances
    ready6 (programText_slice hc6 0x1401c [0x41, 0xf, 0x92, 0xc3] (by decide) (by decide +kernel))
    e6.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14020 (by decide)))
  change (P256.Proofs.Common.Instructions.Setb.setccR8Effect 0x11401c 4 11 2 s6).Holds s6 s7 at e7
  have hc7 := e7.codeIn (Effect.Avoids.of_noMem
    (by simp [P256.Proofs.Common.Instructions.Setb.setccR8Effect, Effect.components, Component.Covers]) _) hc6
  have g7 (v : BitVec 5) : (Operand.reg v : Operand 64).read s7 =
      if v = 11 then BitVec.ofNat 64 c1.toNat else (Operand.reg v : Operand 64).read s6 := by
    have hg := register_after e7 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, P256.Proofs.Common.Instructions.Setb.setccValue, condHolds, ← Operand.read_reg64, setb_zero_value, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g6, g5, g4, g3, g2, g1, cf6, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s8, a8, ready8, e8⟩ := (mov_r64_imm64_effect_step 0x114020 0x48 0xba (by simp [RexWPrefix]) (by decide) 0xffffffff00000001).advances
    ready7 (programText_slice hc7 0x14020 [0x48, 0xba, 0x1, 0x0, 0x0, 0x0, 0xff, 0xff, 0xff, 0xff] (by decide) (by decide +kernel))
    e7.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1402a (by decide)))
  change (movR64Imm64Effect 0x114020 2 0xffffffff00000001 s7).Holds s7 s8 at e8
  have hc8 := e8.codeIn (Effect.Avoids.of_noMem
    (by simp [movR64Imm64Effect, Effect.components, Component.Covers]) _) hc7
  have g8 (v : BitVec 5) : (Operand.reg v : Operand 64).read s8 =
      if v = 2 then 0xffffffff00000001 else (Operand.reg v : Operand 64).read s7 := by
    have hg := register_after e8 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g7, g6, g5, g4, g3, g2, g1, cf6, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s9, a9, ready9, e9⟩ := (and_r64_r64_effect_step 0x11402a 0x48 0xca (by simp [RexWPrefix]) rfl).advances
    ready8 (programText_slice hc8 0x1402a [0x48, 0x21, 0xca] (by decide) (by decide +kernel))
    e8.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1402d (by decide)))
  change (andR64R64Effect 0x11402a 2 1 s8).Holds s8 s9 at e9
  have hc9 := e9.codeIn (Effect.Avoids.of_noMem
    (by simp [andR64R64Effect, Effect.components, Component.Covers]) _) hc8
  have g9 (v : BitVec 5) : (Operand.reg v : Operand 64).read s9 =
      if v = 2 then 0xffffffff00000001 &&& -q else (Operand.reg v : Operand 64).read s8 := by
    have hg := register_after e9 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g8, g7, g6, g5, g4, g3, g2, g1, cf6, k, u, c0, c1, c2, c3] using hg
  obtain ⟨s10, a10, ready10, e10⟩ := (cmp_r64_r64_effect_step 0x11402d 0x48 0xc6 (by simp [RexWPrefix]) rfl).advances
    ready9 (programText_slice hc9 0x1402d [0x48, 0x39, 0xc6] (by decide) (by decide +kernel))
    e9.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14030 (by decide)))
  change (cmpR64R64Effect 0x11402d 6 0 s9).Holds s9 s10 at e10
  have hc10 := e10.codeIn (Effect.Avoids.of_noMem
    (by simp [cmpR64R64Effect, Effect.components, Component.Covers]) _) hc9
  have g10 (v : BitVec 5) : (Operand.reg v : Operand 64).read s10 =
      (Operand.reg v : Operand 64).read s9 := e10.agrees.read (by simp)
  have cf10 : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = c0 := by
    have hf : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = (cmpSpec ((Operand.reg 6 : Operand 64).read s9) ((Operand.reg 0 : Operand 64).read s9)).CF := e10.flags.1
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, addSpec_cf_carry, cmpSpec, subSpec, carryFlag_eq, adcSpec_cf_ofBool,
      read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, k, u, c0, c1, c2, c3] using hf
  obtain ⟨s11, a11, ready11, e11⟩ := (adc_r64_imm8_effect_step 0x114030 0x49 0xd1 0 (by simp [RexWPrefix]) rfl rfl).advances
    ready10 (programText_slice hc10 0x14030 [0x49, 0x83, 0xd1, 0x0] (by decide) (by decide +kernel))
    e10.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14034 (by decide)))
  change (adcR64Imm8Effect 0x114030 9 0 s10).Holds s10 s11 at e11
  have hc11 := e11.codeIn (Effect.Avoids.of_noMem
    (by simp [adcR64Imm8Effect, Effect.components, Component.Covers]) _) hc10
  have g11 (v : BitVec 5) : (Operand.reg v : Operand 64).read s11 =
      if v = 9 then adc u 0 c0 else (Operand.reg v : Operand 64).read s10 := by
    have hg := register_after e11 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, carryFlag_eq, adcSpec_ofBool, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, cf10, k, u, c0, c1, c2, c3] using hg
  have cf11 : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = c2 := by
    have hf : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read s10) 0 (s10.RFLAGS.extractLsb' 0 1)).2.CF := e11.flags.1
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, addSpec_cf_carry, cmpSpec, subSpec, carryFlag_eq, adcSpec_cf_ofBool,
      read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, cf10, k, u, c0, c1, c2, c3] using hf
  obtain ⟨s12, a12, ready12, e12⟩ := (adc_r64_r64_effect_step 0x114034 0x4d 0xc3 (by simp [RexWPrefix]) rfl).advances
    ready11 (programText_slice hc11 0x14034 [0x4d, 0x11, 0xc3] (by decide) (by decide +kernel))
    e11.rip (boundary_ne_program hout (inProgram_of_textOffset 0x14037 (by decide)))
  change (adcR64R64Effect 0x114034 11 8 s11).Holds s11 s12 at e12
  have hc12 := e12.codeIn (Effect.Avoids.of_noMem
    (by simp [adcR64R64Effect, Effect.components, Component.Covers]) _) hc11
  have g12 (v : BitVec 5) : (Operand.reg v : Operand 64).read s12 =
      if v = 11 then adc (BitVec.ofNat 64 c1.toNat) r.l2 c2 else (Operand.reg v : Operand 64).read s11 := by
    have hg := register_after e12 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, carryFlag_eq, adcSpec_ofBool, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, cf10, cf11, k, u, c0, c1, c2, c3] using hg
  have cf12 : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = c3 := by
    have hf : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = (adcSpec ((Operand.reg 11 : Operand 64).read s11) ((Operand.reg 8 : Operand 64).read s11) (s11.RFLAGS.extractLsb' 0 1)).2.CF := e12.flags.1
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, addSpec_cf_carry, cmpSpec, subSpec, carryFlag_eq, adcSpec_cf_ofBool,
      read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, cf10, cf11, k, u, c0, c1, c2, c3] using hf
  obtain ⟨s13, a13, ready13, e13⟩ := (mov_r64_r64_effect_step 0x114037 0x48 0xf8 (by simp [RexWPrefix]) rfl).advances
    ready12 (programText_slice hc12 0x14037 [0x48, 0x89, 0xf8] (by decide) (by decide +kernel))
    e12.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1403a (by decide)))
  change (movR64R64Effect 0x114037 0 7 s12).Holds s12 s13 at e13
  have hc13 := e13.codeIn (Effect.Avoids.of_noMem
    (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hc12
  have g13 (v : BitVec 5) : (Operand.reg v : Operand 64).read s13 =
      if v = 0 then (Operand.reg 7 : Operand 64).read s else (Operand.reg v : Operand 64).read s12 := by
    have hg := register_after e13 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, cf10, cf11, cf12, k, u, c0, c1, c2, c3] using hg
  have cf13 : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = c3 := by
    have hf : s13.RFLAGS = s12.RFLAGS := e13.agrees.rflags (by simp) (by simp)
    rw [hf, cf12]
  obtain ⟨s14, a14, ready14, e14⟩ := (adc_r64_r64_effect_step 0x11403a 0x4c 0xd2 (by simp [RexWPrefix]) rfl).advances
    ready13 (programText_slice hc13 0x1403a [0x4c, 0x11, 0xd2] (by decide) (by decide +kernel))
    e13.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1403d (by decide)))
  change (adcR64R64Effect 0x11403a 2 10 s13).Holds s13 s14 at e14
  have hc14 := e14.codeIn (Effect.Avoids.of_noMem
    (by simp [adcR64R64Effect, Effect.components, Component.Covers]) _) hc13
  have g14 (v : BitVec 5) : (Operand.reg v : Operand 64).read s14 =
      if v = 2 then adc (0xffffffff00000001 &&& -q) r.l3 c3 else (Operand.reg v : Operand 64).read s13 := by
    have hg := register_after e14 v
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, BitVec.reduceSignExtend, BitVec.lt_def, carryFlag_eq, adcSpec_ofBool, read32_eq_read64, hr0, hr1, hr2, hr3, hq, BitVec.reduceEq, ite_true, ite_false, BitVec.xor_self, BitVec.setWidth_zero, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, cf6, cf10, cf11, cf12, cf13, k, u, c0, c1, c2, c3] using hg
  refine ⟨s14, (((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14), ready14, ?_, e14.rip, ?_, ?_, ?_⟩
  · have hext : s14.external = s.external := (((((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).external (by
      simp [movR64R64Effect, subR64R64Effect, movR32R32Effect, xorR32R32Effect, addR64R64Effect, movR64Imm64Effect, andR64R64Effect, cmpR64R64Effect, Effect.components, P256.Proofs.Common.Instructions.Neg64.negR64Effect,
        P256.Proofs.Common.Instructions.Setb.setccR8Effect, adcR64Imm8Effect, adcR64R64Effect,
        Component.Covers])
    intro addr byte hf
    rw [hext]
    exact loaded addr byte hf
  · dsimp only [correctionEffect, Write.AllHold]
    simp only [g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, correct,
      BitVec.reduceEq, ite_true, ite_false, k, u, c0, c1, c2, c3, and_self]
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (((((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).mono
    simp [correctionEffect, movR64R64Effect, subR64R64Effect, movR32R32Effect, xorR32R32Effect, addR64R64Effect, movR64Imm64Effect, andR64R64Effect, cmpR64R64Effect, Effect.components, P256.Proofs.Common.Instructions.Neg64.negR64Effect,
      P256.Proofs.Common.Instructions.Setb.setccR8Effect, adcR64Imm8Effect, adcR64R64Effect]

end P256.Proofs.Field.Subtract
