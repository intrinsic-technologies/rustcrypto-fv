import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthLower

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthRound

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Field.Montgomery (add64 adc64 product64)
open FirstRound (after_store input_readable imulR64R64Effect_components)

attribute [local irreducible] add64 adc64 product64

set_option maxRecDepth 16384 in
set_option exponentiation.threshold 512 in
set_option maxHeartbeats 1800000 in
theorem machine [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Third s t v)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256))) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ Output s t u v := by
  let a := inputWords t
  let extra := BitVec.ofNat 64 (v / 2^384)
  let input7 := BitVec.ofNat 64 (v / 2^448)
  let carry := (carryByte s t).setWidth 64
  let p0 := product64 a.l0 0xffffffffffffffff
  let p1 := product64 0xffffffff a.l0
  let z := add64 p0.1 a.l0
  let y := adc64 p0.2 a.l1 z.2
  let x := add64 y.1 p1.1
  let k := adc64 (BitVec.ofNat 64 y.2.toNat) p1.2 x.2
  let middle := add64 k.1 a.l2
  let d := add64 a.l3 extra
  let p3 := product64 0xffffffff00000001 a.l0
  let q := add64 (BitVec.ofNat 64 middle.2.toNat) d.1
  let r := add64 q.1 p3.1
  let rh := adc64 (BitVec.ofNat 64 q.2.toNat) p3.2 r.2
  let top := adc64 carry rh.1 d.2
  let last := add64 top.1 input7
  let lasthi := adc64 (BitVec.ofNat 64 top.2.toNat) 0 last.2

  obtain ⟨u21, runPrefix, f21, ip21, mem21, g21r7, g21r11, g21r6, g21r5, g21r1, g21r9, g21r10, g21r13, g21r14, g21r0, g21r2, g21r8, g21r3⟩ := lower pre state input
  change ((Operand.reg 7 : Operand 64).read u21) = s.regValue .rdi at g21r7
  change ((Operand.reg 11 : Operand 64).read u21) = 0xffffffffffffffff at g21r11
  change ((Operand.reg 6 : Operand 64).read u21) = s.regValue .rsi at g21r6
  change ((Operand.reg 5 : Operand 64).read u21) = 0xffffffff00000001 at g21r5
  change ((Operand.reg 1 : Operand 64).read u21) = k.1 at g21r1
  change ((Operand.reg 9 : Operand 64).read u21) = a.l3 at g21r9
  change ((Operand.reg 10 : Operand 64).read u21) = a.l0 at g21r10
  change ((Operand.reg 13 : Operand 64).read u21) = a.l2 at g21r13
  change ((Operand.reg 14 : Operand 64).read u21) = extra at g21r14
  change ((Operand.reg 0 : Operand 64).read u21) = 0 at g21r0
  change ((Operand.reg 2 : Operand 64).read u21) = 0 at g21r2
  change ((Operand.reg 8 : Operand 64).read u21) = 0 at g21r8
  change ((Operand.reg 3 : Operand 64).read u21) = x.1 at g21r3
  obtain ⟨u22, run22, ready22, e22⟩ :=
    (add_r64_r64_effect_step 0x1135d6 0x4c 0xe9 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f21.machine f21.bindingsSupported)
      (programText_slice (programLoaded_codeIn f21.loaded) 0x135d6 _ (by decide) (by decide +kernel))
      ip21
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135d9 (by decide)))
  change (addR64R64Effect 0x1135d6 1 13 u21).Holds u21 u22 at e22
  have f22 : ScalarFrame.FrameState s u22 32 112 112 := by
    as_aux_lemma =>
      exact f21.after_registers ready22 e22.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem22 : u22.external = t.external := (e22.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem21
  have g22r1 : ((Operand.reg 1 : Operand 64).read u22) = middle.1 := by
    as_aux_lemma =>
      have h := e22.writes
      change ((Operand.reg 1 : Operand 64).read u22) = (addSpec ((Operand.reg 1 : Operand 64).read u21) ((Operand.reg 13 : Operand 64).read u21)).1 at h
      rw [g21r13, g21r1] at h
      simpa only [middle, add64] using h
  have cf22 : (StatusFlags.ofRFLAGS u22.RFLAGS).CF = middle.2 := by
    as_aux_lemma =>
      have h := e22.flags.1
      change (StatusFlags.ofRFLAGS u22.RFLAGS).CF = (addSpec ((Operand.reg 1 : Operand 64).read u21) ((Operand.reg 13 : Operand 64).read u21)).2.CF at h
      rw [g21r13, g21r1] at h
      simpa only [middle, add64] using h
  have g22r9 : ((Operand.reg 9 : Operand 64).read u22) = a.l3 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r9
  have g22r14 : ((Operand.reg 14 : Operand 64).read u22) = extra := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r14
  obtain ⟨u23, run23, ready23, e23⟩ :=
    (lea_r64_effect_step 0x1135d9 0x4f (by simp [RexWPrefix]) 7 (.sib 9 (some 14) 0 .none) (by decide) rfl rfl).advances (readyToStep f22.machine f22.bindingsSupported)
      (programText_slice (programLoaded_codeIn f22.loaded) 0x135d9 _ (by decide) (by decide +kernel))
      e22.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135dd (by decide)))
  change (leaR64Effect 0x1135d9 15 (.sib 9 (some 14) 0 .none) u22).Holds u22 u23 at e23
  have f23 : ScalarFrame.FrameState s u23 32 112 112 := by
    as_aux_lemma =>
      exact f22.after_registers ready23 e23.agrees (by simp [leaR64Effect_components, Component.Covers]) (by simp [leaR64Effect_components])
  have mem23 : u23.external = t.external := (e23.agrees.external (by simp [leaR64Effect_components, Component.Covers])).trans mem22
  have g23r15 : ((Operand.reg 15 : Operand 64).read u23) = d.1 := by
    as_aux_lemma =>
      have h := e23.writes
      change ((Operand.reg 15 : Operand 64).read u23) = ((Operand.reg 9 : Operand 64).read u22) + (((Operand.reg 14 : Operand 64).read u22) <<< 0) + 0 at h
      rw [g22r9, g22r14] at h
      simpa only [d, add64, addSpec, BitVec.shiftLeft_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add] using h
  have g22r8 : ((Operand.reg 8 : Operand 64).read u22) = 0 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r8
  have g23r8 : ((Operand.reg 8 : Operand 64).read u23) = 0 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r8
  have cf23 : (StatusFlags.ofRFLAGS u23.RFLAGS).CF = middle.2 := (congrArg StatusFlags.CF (e23.agrees.statusFlags (by simp [leaR64Effect_components]))).trans cf22
  obtain ⟨u24, run24, ready24, e24⟩ :=
    (setcc_r8_rex_effect_step 0x1135dd 0x41 0x92 0xc0 (by simp [RexPrefix]) (by simp [SupportedOpcode]) (by decide)).advances (readyToStep f23.machine f23.bindingsSupported)
      (programText_slice (programLoaded_codeIn f23.loaded) 0x135dd _ (by decide) (by decide +kernel))
      e23.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135e1 (by decide)))
  change (setccR8Effect 0x1135dd 4 8 2 u23).Holds u23 u24 at e24
  have f24 : ScalarFrame.FrameState s u24 32 112 112 := by
    as_aux_lemma =>
      exact f23.after_registers ready24 e24.agrees (by simp [setccR8Effect_components, Component.Covers]) (by simp [setccR8Effect_components])
  have mem24 : u24.external = t.external := (e24.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem23
  have g24r8 : ((Operand.reg 8 : Operand 64).read u24) = BitVec.ofNat 64 middle.2.toNat := by
    as_aux_lemma =>
      have h := e24.writes
      change ((Operand.reg 8 : Operand 64).read u24) = mergeGPR 8 (if (StatusFlags.ofRFLAGS u23.RFLAGS).CF then 1 else 0) ((Operand.reg 8 : Operand 64).read u23) at h
      rw [g23r8, cf23] at h
      simpa only [bool_merge] using h
  have g22r0 : ((Operand.reg 0 : Operand 64).read u22) = 0 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r0
  have g23r0 : ((Operand.reg 0 : Operand 64).read u23) = 0 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r0
  have g24r0 : ((Operand.reg 0 : Operand 64).read u24) = 0 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r0
  have g23r1 : ((Operand.reg 1 : Operand 64).read u23) = middle.1 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r1
  have g24r1 : ((Operand.reg 1 : Operand 64).read u24) = middle.1 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r1
  obtain ⟨u25, run25, ready25, e25⟩ :=
    (add_r64_r64_effect_step 0x1135e1 0x48 0xc1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f24.machine f24.bindingsSupported)
      (programText_slice (programLoaded_codeIn f24.loaded) 0x135e1 _ (by decide) (by decide +kernel))
      e24.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135e4 (by decide)))
  change (addR64R64Effect 0x1135e1 1 0 u24).Holds u24 u25 at e25
  have f25 : ScalarFrame.FrameState s u25 32 112 112 := by
    as_aux_lemma =>
      exact f24.after_registers ready25 e25.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem25 : u25.external = t.external := (e25.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem24
  have g25r1 : ((Operand.reg 1 : Operand 64).read u25) = middle.1 := by
    as_aux_lemma =>
      have h := e25.writes
      change ((Operand.reg 1 : Operand 64).read u25) = (addSpec ((Operand.reg 1 : Operand 64).read u24) ((Operand.reg 0 : Operand 64).read u24)).1 at h
      rw [g24r0, g24r1] at h
      simpa only [addSpec, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  have cf25 : (StatusFlags.ofRFLAGS u25.RFLAGS).CF = false := by
    as_aux_lemma =>
      have h := e25.flags.1
      change (StatusFlags.ofRFLAGS u25.RFLAGS).CF = (addSpec ((Operand.reg 1 : Operand 64).read u24) ((Operand.reg 0 : Operand 64).read u24)).2.CF at h
      rw [g24r0, g24r1] at h
      simpa [addSpec, BitVec.carry] using h
  have g22r2 : ((Operand.reg 2 : Operand 64).read u22) = 0 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r2
  have g23r2 : ((Operand.reg 2 : Operand 64).read u23) = 0 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r2
  have g24r2 : ((Operand.reg 2 : Operand 64).read u24) = 0 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r2
  have g25r2 : ((Operand.reg 2 : Operand 64).read u25) = 0 := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r2
  have g25r8 : ((Operand.reg 8 : Operand 64).read u25) = BitVec.ofNat 64 middle.2.toNat := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r8
  obtain ⟨u26, run26, ready26, e26⟩ :=
    (adc_r64_r64_effect_step 0x1135e4 0x49 0xd0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f25.machine f25.bindingsSupported)
      (programText_slice (programLoaded_codeIn f25.loaded) 0x135e4 _ (by decide) (by decide +kernel))
      e25.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135e7 (by decide)))
  change (adcR64R64Effect 0x1135e4 8 2 u25).Holds u25 u26 at e26
  have f26 : ScalarFrame.FrameState s u26 32 112 112 := by
    as_aux_lemma =>
      exact f25.after_registers ready26 e26.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have mem26 : u26.external = t.external := (e26.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem25
  have g26r8 : ((Operand.reg 8 : Operand 64).read u26) = BitVec.ofNat 64 middle.2.toNat := by
    as_aux_lemma =>
      have h := e26.writes
      change ((Operand.reg 8 : Operand 64).read u26) = (adcSpec ((Operand.reg 8 : Operand 64).read u25) ((Operand.reg 2 : Operand 64).read u25) (u25.RFLAGS.extractLsb' 0 1)).1 at h
      rw [g25r2, g25r8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf25] at h
      simpa only [adc_zero_false_word] using h
  have g22r5 : ((Operand.reg 5 : Operand 64).read u22) = 0xffffffff00000001 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r5
  have g23r5 : ((Operand.reg 5 : Operand 64).read u23) = 0xffffffff00000001 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r5
  have g24r5 : ((Operand.reg 5 : Operand 64).read u24) = 0xffffffff00000001 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r5
  have g25r5 : ((Operand.reg 5 : Operand 64).read u25) = 0xffffffff00000001 := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r5
  have g26r5 : ((Operand.reg 5 : Operand 64).read u26) = 0xffffffff00000001 := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r5
  obtain ⟨u27, run27, ready27, e27⟩ :=
    (mov_r64_r64_effect_step 0x1135e7 0x48 0xe8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f26.machine f26.bindingsSupported)
      (programText_slice (programLoaded_codeIn f26.loaded) 0x135e7 _ (by decide) (by decide +kernel))
      e26.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135ea (by decide)))
  change (movR64R64Effect 0x1135e7 0 5 u26).Holds u26 u27 at e27
  have f27 : ScalarFrame.FrameState s u27 32 112 112 := by
    as_aux_lemma =>
      exact f26.after_registers ready27 e27.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have mem27 : u27.external = t.external := (e27.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem26
  have g27r0 : ((Operand.reg 0 : Operand 64).read u27) = 0xffffffff00000001 := by
    as_aux_lemma =>
      have h := e27.writes
      change ((Operand.reg 0 : Operand 64).read u27) = ((Operand.reg 5 : Operand 64).read u26) at h
      rw [g26r5] at h
      exact h
  have g22r10 : ((Operand.reg 10 : Operand 64).read u22) = a.l0 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r10
  have g23r10 : ((Operand.reg 10 : Operand 64).read u23) = a.l0 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r10
  have g24r10 : ((Operand.reg 10 : Operand 64).read u24) = a.l0 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r10
  have g25r10 : ((Operand.reg 10 : Operand 64).read u25) = a.l0 := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r10
  have g26r10 : ((Operand.reg 10 : Operand 64).read u26) = a.l0 := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r10
  have g27r10 : ((Operand.reg 10 : Operand 64).read u27) = a.l0 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r10
  obtain ⟨u28, run28, ready28, e28⟩ :=
    (mul_r64_effect_step 0x1135ea 0x49 0xe2 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f27.machine f27.bindingsSupported)
      (programText_slice (programLoaded_codeIn f27.loaded) 0x135ea _ (by decide) (by decide +kernel))
      e27.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135ed (by decide)))
  change (mulR64Effect 0x1135ea 10 u27).Holds u27 u28 at e28
  have f28 : ScalarFrame.FrameState s u28 32 112 112 := by
    as_aux_lemma =>
      exact f27.after_registers ready28 e28.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have mem28 : u28.external = t.external := (e28.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem27
  have g28r0 : ((Operand.reg 0 : Operand 64).read u28) = p3.1 := by
    as_aux_lemma =>
      have h := e28.writes.1
      change ((Operand.reg 0 : Operand 64).read u28) = ((Operand.reg 0 : Operand 64).read u27) * ((Operand.reg 10 : Operand 64).read u27) at h
      rw [g27r10, g27r0] at h
      simpa only [p3, product64] using h
  have g28r2 : ((Operand.reg 2 : Operand 64).read u28) = p3.2 := by
    as_aux_lemma =>
      have h := e28.writes.2
      change ((Operand.reg 2 : Operand 64).read u28) = mulHigh64 ((Operand.reg 0 : Operand 64).read u27) ((Operand.reg 10 : Operand 64).read u27) at h
      rw [g27r10, g27r0] at h
      simpa only [p3, product64] using h
  have g28r10 : ((Operand.reg 10 : Operand 64).read u28) = a.l0 := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r10
  obtain ⟨u29, run29, ready29, e29⟩ :=
    (xor_r32_r32_rex_effect_step 0x1135ed 0x45 0xd2 (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f28.machine f28.bindingsSupported)
      (programText_slice (programLoaded_codeIn f28.loaded) 0x135ed _ (by decide) (by decide +kernel))
      e28.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135f0 (by decide)))
  change (xorR32R32Effect 0x1135ed 3 10 10 u28).Holds u28 u29 at e29
  have f29 : ScalarFrame.FrameState s u29 32 112 112 := by
    as_aux_lemma =>
      exact f28.after_registers ready29 e29.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have mem29 : u29.external = t.external := (e29.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans mem28
  have g29r10 : ((Operand.reg 10 : Operand 64).read u29) = 0 := by
    as_aux_lemma =>
      have h := e29.writes
      change ((Operand.reg 10 : Operand 64).read u29) = (((((Operand.reg 10 : Operand 64).read u28)).setWidth 32 ^^^ (((Operand.reg 10 : Operand 64).read u28)).setWidth 32).setWidth 64) at h
      rw [g28r10] at h
      simpa using h
  have g24r15 : ((Operand.reg 15 : Operand 64).read u24) = d.1 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r15
  have g25r15 : ((Operand.reg 15 : Operand 64).read u25) = d.1 := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r15
  have g26r15 : ((Operand.reg 15 : Operand 64).read u26) = d.1 := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r15
  have g27r15 : ((Operand.reg 15 : Operand 64).read u27) = d.1 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r15
  have g28r15 : ((Operand.reg 15 : Operand 64).read u28) = d.1 := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r15
  have g29r15 : ((Operand.reg 15 : Operand 64).read u29) = d.1 := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r15
  have g27r8 : ((Operand.reg 8 : Operand 64).read u27) = BitVec.ofNat 64 middle.2.toNat := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r8
  have g28r8 : ((Operand.reg 8 : Operand 64).read u28) = BitVec.ofNat 64 middle.2.toNat := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r8
  have g29r8 : ((Operand.reg 8 : Operand 64).read u29) = BitVec.ofNat 64 middle.2.toNat := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r8
  obtain ⟨u30, run30, ready30, e30⟩ :=
    (add_r64_r64_effect_step 0x1135f0 0x4d 0xf8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f29.machine f29.bindingsSupported)
      (programText_slice (programLoaded_codeIn f29.loaded) 0x135f0 _ (by decide) (by decide +kernel))
      e29.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135f3 (by decide)))
  change (addR64R64Effect 0x1135f0 8 15 u29).Holds u29 u30 at e30
  have f30 : ScalarFrame.FrameState s u30 32 112 112 := by
    as_aux_lemma =>
      exact f29.after_registers ready30 e30.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem30 : u30.external = t.external := (e30.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem29
  have g30r8 : ((Operand.reg 8 : Operand 64).read u30) = q.1 := by
    as_aux_lemma =>
      have h := e30.writes
      change ((Operand.reg 8 : Operand 64).read u30) = (addSpec ((Operand.reg 8 : Operand 64).read u29) ((Operand.reg 15 : Operand 64).read u29)).1 at h
      rw [g29r15, g29r8] at h
      simpa only [q, add64] using h
  have cf30 : (StatusFlags.ofRFLAGS u30.RFLAGS).CF = q.2 := by
    as_aux_lemma =>
      have h := e30.flags.1
      change (StatusFlags.ofRFLAGS u30.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read u29) ((Operand.reg 15 : Operand 64).read u29)).2.CF at h
      rw [g29r15, g29r8] at h
      simpa only [q, add64] using h
  have g30r10 : ((Operand.reg 10 : Operand 64).read u30) = 0 := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r10
  obtain ⟨u31, run31, ready31, e31⟩ :=
    (setcc_r8_rex_effect_step 0x1135f3 0x41 0x92 0xc2 (by simp [RexPrefix]) (by simp [SupportedOpcode]) (by decide)).advances (readyToStep f30.machine f30.bindingsSupported)
      (programText_slice (programLoaded_codeIn f30.loaded) 0x135f3 _ (by decide) (by decide +kernel))
      e30.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135f7 (by decide)))
  change (setccR8Effect 0x1135f3 4 10 2 u30).Holds u30 u31 at e31
  have f31 : ScalarFrame.FrameState s u31 32 112 112 := by
    as_aux_lemma =>
      exact f30.after_registers ready31 e31.agrees (by simp [setccR8Effect_components, Component.Covers]) (by simp [setccR8Effect_components])
  have mem31 : u31.external = t.external := (e31.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem30
  have g31r10 : ((Operand.reg 10 : Operand 64).read u31) = BitVec.ofNat 64 q.2.toNat := by
    as_aux_lemma =>
      have h := e31.writes
      change ((Operand.reg 10 : Operand 64).read u31) = mergeGPR 8 (if (StatusFlags.ofRFLAGS u30.RFLAGS).CF then 1 else 0) ((Operand.reg 10 : Operand 64).read u30) at h
      rw [g30r10, cf30] at h
      simpa only [bool_merge] using h
  have g29r0 : ((Operand.reg 0 : Operand 64).read u29) = p3.1 := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r0
  have g30r0 : ((Operand.reg 0 : Operand 64).read u30) = p3.1 := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r0
  have g31r0 : ((Operand.reg 0 : Operand 64).read u31) = p3.1 := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r0
  have g31r8 : ((Operand.reg 8 : Operand 64).read u31) = q.1 := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r8
  obtain ⟨u32, run32, ready32, e32⟩ :=
    (add_r64_r64_effect_step 0x1135f7 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f31.machine f31.bindingsSupported)
      (programText_slice (programLoaded_codeIn f31.loaded) 0x135f7 _ (by decide) (by decide +kernel))
      e31.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135fa (by decide)))
  change (addR64R64Effect 0x1135f7 8 0 u31).Holds u31 u32 at e32
  have f32 : ScalarFrame.FrameState s u32 32 112 112 := by
    as_aux_lemma =>
      exact f31.after_registers ready32 e32.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem32 : u32.external = t.external := (e32.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem31
  have g32r8 : ((Operand.reg 8 : Operand 64).read u32) = r.1 := by
    as_aux_lemma =>
      have h := e32.writes
      change ((Operand.reg 8 : Operand 64).read u32) = (addSpec ((Operand.reg 8 : Operand 64).read u31) ((Operand.reg 0 : Operand 64).read u31)).1 at h
      rw [g31r0, g31r8] at h
      simpa only [r, add64] using h
  have cf32 : (StatusFlags.ofRFLAGS u32.RFLAGS).CF = r.2 := by
    as_aux_lemma =>
      have h := e32.flags.1
      change (StatusFlags.ofRFLAGS u32.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read u31) ((Operand.reg 0 : Operand 64).read u31)).2.CF at h
      rw [g31r0, g31r8] at h
      simpa only [r, add64] using h
  have g29r2 : ((Operand.reg 2 : Operand 64).read u29) = p3.2 := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r2
  have g30r2 : ((Operand.reg 2 : Operand 64).read u30) = p3.2 := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r2
  have g31r2 : ((Operand.reg 2 : Operand 64).read u31) = p3.2 := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r2
  have g32r2 : ((Operand.reg 2 : Operand 64).read u32) = p3.2 := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r2
  have g32r10 : ((Operand.reg 10 : Operand 64).read u32) = BitVec.ofNat 64 q.2.toNat := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r10
  obtain ⟨u33, run33, ready33, e33⟩ :=
    (adc_r64_r64_effect_step 0x1135fa 0x49 0xd2 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f32.machine f32.bindingsSupported)
      (programText_slice (programLoaded_codeIn f32.loaded) 0x135fa _ (by decide) (by decide +kernel))
      e32.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135fd (by decide)))
  change (adcR64R64Effect 0x1135fa 10 2 u32).Holds u32 u33 at e33
  have f33 : ScalarFrame.FrameState s u33 32 112 112 := by
    as_aux_lemma =>
      exact f32.after_registers ready33 e33.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have mem33 : u33.external = t.external := (e33.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem32
  have g33r10 : ((Operand.reg 10 : Operand 64).read u33) = rh.1 := by
    as_aux_lemma =>
      have h := e33.writes
      change ((Operand.reg 10 : Operand 64).read u33) = (adcSpec ((Operand.reg 10 : Operand 64).read u32) ((Operand.reg 2 : Operand 64).read u32) (u32.RFLAGS.extractLsb' 0 1)).1 at h
      rw [g32r2, g32r10, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf32] at h
      simpa only [rh, adc64] using h
  have g23r14 : ((Operand.reg 14 : Operand 64).read u23) = extra := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r14
  have g24r14 : ((Operand.reg 14 : Operand 64).read u24) = extra := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r14
  have g25r14 : ((Operand.reg 14 : Operand 64).read u25) = extra := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r14
  have g26r14 : ((Operand.reg 14 : Operand 64).read u26) = extra := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r14
  have g27r14 : ((Operand.reg 14 : Operand 64).read u27) = extra := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r14
  have g28r14 : ((Operand.reg 14 : Operand 64).read u28) = extra := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r14
  have g29r14 : ((Operand.reg 14 : Operand 64).read u29) = extra := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r14
  have g30r14 : ((Operand.reg 14 : Operand 64).read u30) = extra := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r14
  have g31r14 : ((Operand.reg 14 : Operand 64).read u31) = extra := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r14
  have g32r14 : ((Operand.reg 14 : Operand 64).read u32) = extra := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r14
  have g33r14 : ((Operand.reg 14 : Operand 64).read u33) = extra := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r14
  have g23r9 : ((Operand.reg 9 : Operand 64).read u23) = a.l3 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r9
  have g24r9 : ((Operand.reg 9 : Operand 64).read u24) = a.l3 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r9
  have g25r9 : ((Operand.reg 9 : Operand 64).read u25) = a.l3 := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r9
  have g26r9 : ((Operand.reg 9 : Operand 64).read u26) = a.l3 := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r9
  have g27r9 : ((Operand.reg 9 : Operand 64).read u27) = a.l3 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r9
  have g28r9 : ((Operand.reg 9 : Operand 64).read u28) = a.l3 := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r9
  have g29r9 : ((Operand.reg 9 : Operand 64).read u29) = a.l3 := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r9
  have g30r9 : ((Operand.reg 9 : Operand 64).read u30) = a.l3 := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r9
  have g31r9 : ((Operand.reg 9 : Operand 64).read u31) = a.l3 := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r9
  have g32r9 : ((Operand.reg 9 : Operand 64).read u32) = a.l3 := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r9
  have g33r9 : ((Operand.reg 9 : Operand 64).read u33) = a.l3 := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r9
  obtain ⟨u34, run34, ready34, e34⟩ :=
    (add_r64_r64_effect_step 0x1135fd 0x4d 0xf1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f33.machine f33.bindingsSupported)
      (programText_slice (programLoaded_codeIn f33.loaded) 0x135fd _ (by decide) (by decide +kernel))
      e33.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13600 (by decide)))
  change (addR64R64Effect 0x1135fd 9 14 u33).Holds u33 u34 at e34
  have f34 : ScalarFrame.FrameState s u34 32 112 112 := by
    as_aux_lemma =>
      exact f33.after_registers ready34 e34.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem34 : u34.external = t.external := (e34.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem33
  have g34r9 : ((Operand.reg 9 : Operand 64).read u34) = d.1 := by
    as_aux_lemma =>
      have h := e34.writes
      change ((Operand.reg 9 : Operand 64).read u34) = (addSpec ((Operand.reg 9 : Operand 64).read u33) ((Operand.reg 14 : Operand 64).read u33)).1 at h
      rw [g33r14, g33r9] at h
      simpa only [d, add64] using h
  have cf34 : (StatusFlags.ofRFLAGS u34.RFLAGS).CF = d.2 := by
    as_aux_lemma =>
      have h := e34.flags.1
      change (StatusFlags.ofRFLAGS u34.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read u33) ((Operand.reg 14 : Operand 64).read u33)).2.CF at h
      rw [g33r14, g33r9] at h
      simpa only [d, add64] using h
  obtain ⟨u35, run35, ready35, e35⟩ :=
    (movzx_r32_m8_effect_step 0x113600 2 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl).advances (readyToStep f34.machine f34.bindingsSupported)
      (programText_slice (programLoaded_codeIn f34.loaded) 0x13600 _ (by decide) (by decide +kernel))
      ⟨e34.rip, ScalarFrame.stack_readable pre.toCalleePre f34 (offset := 7) (len := 1) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13605 (by decide)))
  change (movzxR32M8Effect 0x113600 5 2 (.sib 4 none 0 (.d8 7)) u34).Holds u34 u35 at e35
  have f35 : ScalarFrame.FrameState s u35 32 112 112 := by
    as_aux_lemma =>
      exact f34.after_registers ready35 e35.agrees (by simp [movzxR32M8Effect_components, Component.Covers]) (by simp [movzxR32M8Effect_components])
  have mem35 : u35.external = t.external := (e35.agrees.external (by simp [movzxR32M8Effect_components, Component.Covers])).trans mem34
  have load35 : memLoad u34.external (((Operand.reg 4 : Operand 64).read u34) + 7) 8 = carryByte s t := by
    as_aux_lemma =>
      change memLoad u34.external (stackPtr u34 + 7) 8 = _
      rw [f34.rsp, mem34]
  have g35r2 : ((Operand.reg 2 : Operand 64).read u35) = carry := by
    as_aux_lemma =>
      have h := e35.writes
      change ((Operand.reg 2 : Operand 64).read u35) = (memLoad u34.external (((Operand.reg 4 : Operand 64).read u34) + 7) 8).setWidth 64 at h
      rw [load35] at h
      exact h
  have g34r10 : ((Operand.reg 10 : Operand 64).read u34) = rh.1 := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r10
  have g35r10 : ((Operand.reg 10 : Operand 64).read u35) = rh.1 := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r10
  have cf35 : (StatusFlags.ofRFLAGS u35.RFLAGS).CF = d.2 := (congrArg StatusFlags.CF (e35.agrees.statusFlags (by simp [movzxR32M8Effect_components]))).trans cf34
  obtain ⟨u36, run36, ready36, e36⟩ :=
    (adc_r64_r64_effect_step 0x113605 0x4c 0xd2 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f35.machine f35.bindingsSupported)
      (programText_slice (programLoaded_codeIn f35.loaded) 0x13605 _ (by decide) (by decide +kernel))
      e35.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13608 (by decide)))
  change (adcR64R64Effect 0x113605 2 10 u35).Holds u35 u36 at e36
  have f36 : ScalarFrame.FrameState s u36 32 112 112 := by
    as_aux_lemma =>
      exact f35.after_registers ready36 e36.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have mem36 : u36.external = t.external := (e36.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem35
  have g36r2 : ((Operand.reg 2 : Operand 64).read u36) = top.1 := by
    as_aux_lemma =>
      have h := e36.writes
      change ((Operand.reg 2 : Operand 64).read u36) = (adcSpec ((Operand.reg 2 : Operand 64).read u35) ((Operand.reg 10 : Operand 64).read u35) (u35.RFLAGS.extractLsb' 0 1)).1 at h
      rw [g35r10, g35r2, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf35] at h
      simpa only [top, adc64] using h
  have cf36 : (StatusFlags.ofRFLAGS u36.RFLAGS).CF = top.2 := by
    as_aux_lemma =>
      have h := e36.flags.1
      change (StatusFlags.ofRFLAGS u36.RFLAGS).CF = (adcSpec ((Operand.reg 2 : Operand 64).read u35) ((Operand.reg 10 : Operand 64).read u35) (u35.RFLAGS.extractLsb' 0 1)).2.CF at h
      rw [g35r10, g35r2, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf35] at h
      simpa only [top, adc64] using h
  have g32r0 : ((Operand.reg 0 : Operand 64).read u32) = p3.1 := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r0
  have g33r0 : ((Operand.reg 0 : Operand 64).read u33) = p3.1 := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r0
  have g34r0 : ((Operand.reg 0 : Operand 64).read u34) = p3.1 := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r0
  have g35r0 : ((Operand.reg 0 : Operand 64).read u35) = p3.1 := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r0
  have g36r0 : ((Operand.reg 0 : Operand 64).read u36) = p3.1 := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r0
  obtain ⟨u37, run37, ready37, e37⟩ :=
    (setcc_r8_effect_step 0x113608 0x92 0xc0 (by simp [SupportedOpcode]) (by decide) (by decide)).advances (readyToStep f36.machine f36.bindingsSupported)
      (programText_slice (programLoaded_codeIn f36.loaded) 0x13608 _ (by decide) (by decide +kernel))
      e36.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1360b (by decide)))
  change (setccR8Effect 0x113608 3 0 2 u36).Holds u36 u37 at e37
  have f37 : ScalarFrame.FrameState s u37 32 112 112 := by
    as_aux_lemma =>
      exact f36.after_registers ready37 e37.agrees (by simp [setccR8Effect_components, Component.Covers]) (by simp [setccR8Effect_components])
  have mem37 : u37.external = t.external := (e37.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem36
  have g37r0 : ((Operand.reg 0 : Operand 64).read u37) = (mergeGPR 8 (if top.2 then 1 else 0) (p3.1)) := by
    as_aux_lemma =>
      have h := e37.writes
      change ((Operand.reg 0 : Operand 64).read u37) = mergeGPR 8 (if (StatusFlags.ofRFLAGS u36.RFLAGS).CF then 1 else 0) ((Operand.reg 0 : Operand 64).read u36) at h
      rw [g36r0, cf36] at h
      exact h
  obtain ⟨u38, run38, ready38, e38⟩ :=
    (movzx_r32_r8_rex_effect_step 0x11360b 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f37.machine f37.bindingsSupported)
      (programText_slice (programLoaded_codeIn f37.loaded) 0x1360b _ (by decide) (by decide +kernel))
      e37.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1360f (by decide)))
  change (movzxR32R8Effect 0x11360b 4 12 0 u37).Holds u37 u38 at e38
  have f38 : ScalarFrame.FrameState s u38 32 112 112 := by
    as_aux_lemma =>
      exact f37.after_registers ready38 e38.agrees (by simp [movzxR32R8Effect_components, Component.Covers]) (by simp [movzxR32R8Effect_components])
  have mem38 : u38.external = t.external := (e38.agrees.external (by simp [movzxR32R8Effect_components, Component.Covers])).trans mem37
  have g38r12 : ((Operand.reg 12 : Operand 64).read u38) = BitVec.ofNat 64 top.2.toNat := by
    as_aux_lemma =>
      have h := e38.writes
      change ((Operand.reg 12 : Operand 64).read u38) = (((Operand.reg 0 : Operand 64).read u37).setWidth 8).setWidth 64 at h
      rw [g37r0] at h
      simpa only [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, bool_byte] using h
  obtain ⟨u39, run39, ready39, e39⟩ :=
    (mov_m64_r64_effect_step_any 0x11360f 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f38.machine f38.bindingsSupported)
      (programText_slice (programLoaded_codeIn f38.loaded) 0x1360f _ (by decide) (by decide +kernel))
      ⟨e38.rip, ScalarFrame.stack_writable pre.toCalleePre f38 (offset := 16) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f38 (offset := 16) (len := 8) (codeOffset := 0x1360f) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13614 (by decide)))
  change (movM64R64Effect 0x11360f 12 (.sib 4 none 0 (.d8 16)) u38).Holds u38 u39 at e39
  have ag39 : AgreesExcept [.mem (stackPtr u38 + 16) 8, .rip] u38 u39 := by
    as_aux_lemma =>
      simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e39.agrees
  have f39 : ScalarFrame.FrameState s u39 32 112 112 := by
    as_aux_lemma =>
      exact after_store pre f38 ready39 (offset := 16) (by decide) ag39
  have wr39 : slot s u39 16 = BitVec.ofNat 64 top.2.toNat := by
    as_aux_lemma =>
      have h := e39.writes
      change memLoad u39.external (stackPtr u38 + 16) 64 = ((Operand.reg 12 : Operand 64).read u38) at h
      rw [f38.rsp, g38r12] at h
      exact h
  have g22r6 : ((Operand.reg 6 : Operand 64).read u22) = s.regValue .rsi := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r6
  have g23r6 : ((Operand.reg 6 : Operand 64).read u23) = s.regValue .rsi := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r6
  have g24r6 : ((Operand.reg 6 : Operand 64).read u24) = s.regValue .rsi := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r6
  have g25r6 : ((Operand.reg 6 : Operand 64).read u25) = s.regValue .rsi := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r6
  have g26r6 : ((Operand.reg 6 : Operand 64).read u26) = s.regValue .rsi := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r6
  have g27r6 : ((Operand.reg 6 : Operand 64).read u27) = s.regValue .rsi := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r6
  have g28r6 : ((Operand.reg 6 : Operand 64).read u28) = s.regValue .rsi := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r6
  have g29r6 : ((Operand.reg 6 : Operand 64).read u29) = s.regValue .rsi := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r6
  have g30r6 : ((Operand.reg 6 : Operand 64).read u30) = s.regValue .rsi := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r6
  have g31r6 : ((Operand.reg 6 : Operand 64).read u31) = s.regValue .rsi := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r6
  have g32r6 : ((Operand.reg 6 : Operand 64).read u32) = s.regValue .rsi := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r6
  have g33r6 : ((Operand.reg 6 : Operand 64).read u33) = s.regValue .rsi := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r6
  have g34r6 : ((Operand.reg 6 : Operand 64).read u34) = s.regValue .rsi := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r6
  have g35r6 : ((Operand.reg 6 : Operand 64).read u35) = s.regValue .rsi := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r6
  have g36r6 : ((Operand.reg 6 : Operand 64).read u36) = s.regValue .rsi := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r6
  have g37r6 : ((Operand.reg 6 : Operand 64).read u37) = s.regValue .rsi := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r6
  have g38r6 : ((Operand.reg 6 : Operand 64).read u38) = s.regValue .rsi := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r6
  have g39r6 : ((Operand.reg 6 : Operand 64).read u39) = s.regValue .rsi := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r6
  obtain ⟨u40, run40, ready40, e40⟩ :=
    (mov_r64_m64_effect_step 0x113614 0x48 (by simp [RexWPrefix]) 6 (.base 6 (.d8 56)) (by decide) rfl rfl).advances (readyToStep f39.machine f39.bindingsSupported)
      (programText_slice (programLoaded_codeIn f39.loaded) 0x13614 _ (by decide) (by decide +kernel))
      ⟨e39.rip, by
        change MemReadable u39 (((Operand.reg 6 : Operand 64).read u39) + 56) 8
        rw [g39r6]
        exact input_readable pre f39 (j := 7) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13618 (by decide)))
  change (movR64M64Effect 0x113614 6 (.base 6 (.d8 56)) u39).Holds u39 u40 at e40
  have f40 : ScalarFrame.FrameState s u40 32 112 112 := by
    as_aux_lemma =>
      exact f39.after_registers ready40 e40.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load40 : memLoad u39.external (((Operand.reg 6 : Operand 64).read u39) + 56) 64 = input7 := by
    as_aux_lemma =>
      rw [g39r6]
      exact input_limb pre f39 input 7 (by decide)
  have g40r6 : ((Operand.reg 6 : Operand 64).read u40) = input7 := by
    as_aux_lemma =>
      have h := e40.writes
      change ((Operand.reg 6 : Operand 64).read u40) = memLoad u39.external (((Operand.reg 6 : Operand 64).read u39) + 56) 64 at h
      rw [load40] at h
      exact h
  obtain ⟨u41, run41, ready41, e41⟩ :=
    (mov_m64_r64_effect_step_any 0x113618 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances (readyToStep f40.machine f40.bindingsSupported)
      (programText_slice (programLoaded_codeIn f40.loaded) 0x13618 _ (by decide) (by decide +kernel))
      ⟨e40.rip, ScalarFrame.stack_writable pre.toCalleePre f40 (offset := 24) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f40 (offset := 24) (len := 8) (codeOffset := 0x13618) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1361d (by decide)))
  change (movM64R64Effect 0x113618 6 (.sib 4 none 0 (.d8 24)) u40).Holds u40 u41 at e41
  have ag41 : AgreesExcept [.mem (stackPtr u40 + 24) 8, .rip] u40 u41 := by
    as_aux_lemma =>
      simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e41.agrees
  have f41 : ScalarFrame.FrameState s u41 32 112 112 := by
    as_aux_lemma =>
      exact after_store pre f40 ready41 (offset := 24) (by decide) ag41
  have wr41 : slot s u41 24 = input7 := by
    as_aux_lemma =>
      have h := e41.writes
      change memLoad u41.external (stackPtr u40 + 24) 64 = ((Operand.reg 6 : Operand 64).read u40) at h
      rw [f40.rsp, g40r6] at h
      exact h
  have g37r2 : ((Operand.reg 2 : Operand 64).read u37) = top.1 := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r2
  have g38r2 : ((Operand.reg 2 : Operand 64).read u38) = top.1 := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r2
  have g39r2 : ((Operand.reg 2 : Operand 64).read u39) = top.1 := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r2
  have g40r2 : ((Operand.reg 2 : Operand 64).read u40) = top.1 := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r2
  have g41r2 : ((Operand.reg 2 : Operand 64).read u41) = top.1 := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r2
  obtain ⟨u42, run42, ready42, e42⟩ :=
    (mov_r64_r64_effect_step 0x11361d 0x48 0xd0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f41.machine f41.bindingsSupported)
      (programText_slice (programLoaded_codeIn f41.loaded) 0x1361d _ (by decide) (by decide +kernel))
      e41.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13620 (by decide)))
  change (movR64R64Effect 0x11361d 0 2 u41).Holds u41 u42 at e42
  have f42 : ScalarFrame.FrameState s u42 32 112 112 := by
    as_aux_lemma =>
      exact f41.after_registers ready42 e42.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g42r0 : ((Operand.reg 0 : Operand 64).read u42) = top.1 := by
    as_aux_lemma =>
      have h := e42.writes
      change ((Operand.reg 0 : Operand 64).read u42) = ((Operand.reg 2 : Operand 64).read u41) at h
      rw [g41r2] at h
      simpa only [top, adc64] using h
  have g41r6 : ((Operand.reg 6 : Operand 64).read u41) = input7 := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r6
  have g42r6 : ((Operand.reg 6 : Operand 64).read u42) = input7 := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r6
  obtain ⟨u43, run43, ready43, e43⟩ :=
    (add_r64_r64_effect_step 0x113620 0x48 0xf0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f42.machine f42.bindingsSupported)
      (programText_slice (programLoaded_codeIn f42.loaded) 0x13620 _ (by decide) (by decide +kernel))
      e42.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13623 (by decide)))
  change (addR64R64Effect 0x113620 0 6 u42).Holds u42 u43 at e43
  have f43 : ScalarFrame.FrameState s u43 32 112 112 := by
    as_aux_lemma =>
      exact f42.after_registers ready43 e43.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g43r0 : ((Operand.reg 0 : Operand 64).read u43) = last.1 := by
    as_aux_lemma =>
      have h := e43.writes
      change ((Operand.reg 0 : Operand 64).read u43) = (addSpec ((Operand.reg 0 : Operand 64).read u42) ((Operand.reg 6 : Operand 64).read u42)).1 at h
      rw [g42r6, g42r0] at h
      simpa only [last, add64] using h
  have cf43 : (StatusFlags.ofRFLAGS u43.RFLAGS).CF = last.2 := by
    as_aux_lemma =>
      have h := e43.flags.1
      change (StatusFlags.ofRFLAGS u43.RFLAGS).CF = (addSpec ((Operand.reg 0 : Operand 64).read u42) ((Operand.reg 6 : Operand 64).read u42)).2.CF at h
      rw [g42r6, g42r0] at h
      simpa only [last, add64] using h
  have g39r12 : ((Operand.reg 12 : Operand 64).read u39) = BitVec.ofNat 64 top.2.toNat := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r12
  have g40r12 : ((Operand.reg 12 : Operand 64).read u40) = BitVec.ofNat 64 top.2.toNat := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r12
  have g41r12 : ((Operand.reg 12 : Operand 64).read u41) = BitVec.ofNat 64 top.2.toNat := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r12
  have g42r12 : ((Operand.reg 12 : Operand 64).read u42) = BitVec.ofNat 64 top.2.toNat := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r12
  have g43r12 : ((Operand.reg 12 : Operand 64).read u43) = BitVec.ofNat 64 top.2.toNat := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r12
  obtain ⟨u44, run44, ready44, e44⟩ :=
    (adc_r64_imm8_effect_step 0x113623 0x49 0xd4 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f43.machine f43.bindingsSupported)
      (programText_slice (programLoaded_codeIn f43.loaded) 0x13623 _ (by decide) (by decide +kernel))
      e43.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13627 (by decide)))
  change (adcR64Imm8Effect 0x113623 12 0 u43).Holds u43 u44 at e44
  have f44 : ScalarFrame.FrameState s u44 32 112 112 := by
    as_aux_lemma =>
      exact f43.after_registers ready44 e44.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g44r12 : ((Operand.reg 12 : Operand 64).read u44) = lasthi.1 := by
    as_aux_lemma =>
      have h := e44.writes
      change ((Operand.reg 12 : Operand 64).read u44) = (adcSpec ((Operand.reg 12 : Operand 64).read u43) 0 (u43.RFLAGS.extractLsb' 0 1)).1 at h
      rw [g43r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf43] at h
      simpa only [lasthi, adc64] using h
  have g22r7 : ((Operand.reg 7 : Operand 64).read u22) = s.regValue .rdi := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r7
  have g23r7 : ((Operand.reg 7 : Operand 64).read u23) = s.regValue .rdi := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r7
  have g24r7 : ((Operand.reg 7 : Operand 64).read u24) = s.regValue .rdi := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r7
  have g25r7 : ((Operand.reg 7 : Operand 64).read u25) = s.regValue .rdi := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r7
  have g26r7 : ((Operand.reg 7 : Operand 64).read u26) = s.regValue .rdi := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r7
  have g27r7 : ((Operand.reg 7 : Operand 64).read u27) = s.regValue .rdi := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r7
  have g28r7 : ((Operand.reg 7 : Operand 64).read u28) = s.regValue .rdi := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r7
  have g29r7 : ((Operand.reg 7 : Operand 64).read u29) = s.regValue .rdi := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r7
  have g30r7 : ((Operand.reg 7 : Operand 64).read u30) = s.regValue .rdi := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r7
  have g31r7 : ((Operand.reg 7 : Operand 64).read u31) = s.regValue .rdi := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r7
  have g32r7 : ((Operand.reg 7 : Operand 64).read u32) = s.regValue .rdi := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r7
  have g33r7 : ((Operand.reg 7 : Operand 64).read u33) = s.regValue .rdi := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r7
  have g34r7 : ((Operand.reg 7 : Operand 64).read u34) = s.regValue .rdi := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r7
  have g35r7 : ((Operand.reg 7 : Operand 64).read u35) = s.regValue .rdi := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r7
  have g36r7 : ((Operand.reg 7 : Operand 64).read u36) = s.regValue .rdi := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r7
  have g37r7 : ((Operand.reg 7 : Operand 64).read u37) = s.regValue .rdi := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r7
  have g38r7 : ((Operand.reg 7 : Operand 64).read u38) = s.regValue .rdi := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r7
  have g39r7 : ((Operand.reg 7 : Operand 64).read u39) = s.regValue .rdi := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r7
  have g40r7 : ((Operand.reg 7 : Operand 64).read u40) = s.regValue .rdi := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r7
  have g41r7 : ((Operand.reg 7 : Operand 64).read u41) = s.regValue .rdi := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r7
  have g42r7 : ((Operand.reg 7 : Operand 64).read u42) = s.regValue .rdi := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r7
  have g43r7 : ((Operand.reg 7 : Operand 64).read u43) = s.regValue .rdi := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r7
  have g44r7 : ((Operand.reg 7 : Operand 64).read u44) = s.regValue .rdi := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r7
  have g22r11 : ((Operand.reg 11 : Operand 64).read u22) = 0xffffffffffffffff := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r11
  have g23r11 : ((Operand.reg 11 : Operand 64).read u23) = 0xffffffffffffffff := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r11
  have g24r11 : ((Operand.reg 11 : Operand 64).read u24) = 0xffffffffffffffff := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r11
  have g25r11 : ((Operand.reg 11 : Operand 64).read u25) = 0xffffffffffffffff := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r11
  have g26r11 : ((Operand.reg 11 : Operand 64).read u26) = 0xffffffffffffffff := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r11
  have g27r11 : ((Operand.reg 11 : Operand 64).read u27) = 0xffffffffffffffff := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r11
  have g28r11 : ((Operand.reg 11 : Operand 64).read u28) = 0xffffffffffffffff := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r11
  have g29r11 : ((Operand.reg 11 : Operand 64).read u29) = 0xffffffffffffffff := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r11
  have g30r11 : ((Operand.reg 11 : Operand 64).read u30) = 0xffffffffffffffff := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r11
  have g31r11 : ((Operand.reg 11 : Operand 64).read u31) = 0xffffffffffffffff := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r11
  have g32r11 : ((Operand.reg 11 : Operand 64).read u32) = 0xffffffffffffffff := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r11
  have g33r11 : ((Operand.reg 11 : Operand 64).read u33) = 0xffffffffffffffff := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r11
  have g34r11 : ((Operand.reg 11 : Operand 64).read u34) = 0xffffffffffffffff := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r11
  have g35r11 : ((Operand.reg 11 : Operand 64).read u35) = 0xffffffffffffffff := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r11
  have g36r11 : ((Operand.reg 11 : Operand 64).read u36) = 0xffffffffffffffff := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r11
  have g37r11 : ((Operand.reg 11 : Operand 64).read u37) = 0xffffffffffffffff := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r11
  have g38r11 : ((Operand.reg 11 : Operand 64).read u38) = 0xffffffffffffffff := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r11
  have g39r11 : ((Operand.reg 11 : Operand 64).read u39) = 0xffffffffffffffff := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r11
  have g40r11 : ((Operand.reg 11 : Operand 64).read u40) = 0xffffffffffffffff := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r11
  have g41r11 : ((Operand.reg 11 : Operand 64).read u41) = 0xffffffffffffffff := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r11
  have g42r11 : ((Operand.reg 11 : Operand 64).read u42) = 0xffffffffffffffff := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r11
  have g43r11 : ((Operand.reg 11 : Operand 64).read u43) = 0xffffffffffffffff := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r11
  have g44r11 : ((Operand.reg 11 : Operand 64).read u44) = 0xffffffffffffffff := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r11
  have g22r3 : ((Operand.reg 3 : Operand 64).read u22) = x.1 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r3
  have g23r3 : ((Operand.reg 3 : Operand 64).read u23) = x.1 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r3
  have g24r3 : ((Operand.reg 3 : Operand 64).read u24) = x.1 := (e24.agrees.read (by simp [setccR8Effect_components])).trans g23r3
  have g25r3 : ((Operand.reg 3 : Operand 64).read u25) = x.1 := (e25.agrees.read (by simp [addR64R64Effect_components])).trans g24r3
  have g26r3 : ((Operand.reg 3 : Operand 64).read u26) = x.1 := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r3
  have g27r3 : ((Operand.reg 3 : Operand 64).read u27) = x.1 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r3
  have g28r3 : ((Operand.reg 3 : Operand 64).read u28) = x.1 := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r3
  have g29r3 : ((Operand.reg 3 : Operand 64).read u29) = x.1 := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r3
  have g30r3 : ((Operand.reg 3 : Operand 64).read u30) = x.1 := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r3
  have g31r3 : ((Operand.reg 3 : Operand 64).read u31) = x.1 := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r3
  have g32r3 : ((Operand.reg 3 : Operand 64).read u32) = x.1 := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r3
  have g33r3 : ((Operand.reg 3 : Operand 64).read u33) = x.1 := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r3
  have g34r3 : ((Operand.reg 3 : Operand 64).read u34) = x.1 := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r3
  have g35r3 : ((Operand.reg 3 : Operand 64).read u35) = x.1 := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r3
  have g36r3 : ((Operand.reg 3 : Operand 64).read u36) = x.1 := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r3
  have g37r3 : ((Operand.reg 3 : Operand 64).read u37) = x.1 := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r3
  have g38r3 : ((Operand.reg 3 : Operand 64).read u38) = x.1 := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r3
  have g39r3 : ((Operand.reg 3 : Operand 64).read u39) = x.1 := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r3
  have g40r3 : ((Operand.reg 3 : Operand 64).read u40) = x.1 := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r3
  have g41r3 : ((Operand.reg 3 : Operand 64).read u41) = x.1 := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r3
  have g42r3 : ((Operand.reg 3 : Operand 64).read u42) = x.1 := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r3
  have g43r3 : ((Operand.reg 3 : Operand 64).read u43) = x.1 := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r3
  have g44r3 : ((Operand.reg 3 : Operand 64).read u44) = x.1 := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r3
  have g26r1 : ((Operand.reg 1 : Operand 64).read u26) = middle.1 := (e26.agrees.read (by simp [adcR64R64Effect_components])).trans g25r1
  have g27r1 : ((Operand.reg 1 : Operand 64).read u27) = middle.1 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r1
  have g28r1 : ((Operand.reg 1 : Operand 64).read u28) = middle.1 := (e28.agrees.read (by simp [mulR64Effect_components])).trans g27r1
  have g29r1 : ((Operand.reg 1 : Operand 64).read u29) = middle.1 := (e29.agrees.read (by simp [xorR32R32Effect_components])).trans g28r1
  have g30r1 : ((Operand.reg 1 : Operand 64).read u30) = middle.1 := (e30.agrees.read (by simp [addR64R64Effect_components])).trans g29r1
  have g31r1 : ((Operand.reg 1 : Operand 64).read u31) = middle.1 := (e31.agrees.read (by simp [setccR8Effect_components])).trans g30r1
  have g32r1 : ((Operand.reg 1 : Operand 64).read u32) = middle.1 := (e32.agrees.read (by simp [addR64R64Effect_components])).trans g31r1
  have g33r1 : ((Operand.reg 1 : Operand 64).read u33) = middle.1 := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r1
  have g34r1 : ((Operand.reg 1 : Operand 64).read u34) = middle.1 := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r1
  have g35r1 : ((Operand.reg 1 : Operand 64).read u35) = middle.1 := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r1
  have g36r1 : ((Operand.reg 1 : Operand 64).read u36) = middle.1 := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r1
  have g37r1 : ((Operand.reg 1 : Operand 64).read u37) = middle.1 := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r1
  have g38r1 : ((Operand.reg 1 : Operand 64).read u38) = middle.1 := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r1
  have g39r1 : ((Operand.reg 1 : Operand 64).read u39) = middle.1 := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r1
  have g40r1 : ((Operand.reg 1 : Operand 64).read u40) = middle.1 := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r1
  have g41r1 : ((Operand.reg 1 : Operand 64).read u41) = middle.1 := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r1
  have g42r1 : ((Operand.reg 1 : Operand 64).read u42) = middle.1 := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r1
  have g43r1 : ((Operand.reg 1 : Operand 64).read u43) = middle.1 := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r1
  have g44r1 : ((Operand.reg 1 : Operand 64).read u44) = middle.1 := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r1
  have g33r8 : ((Operand.reg 8 : Operand 64).read u33) = r.1 := (e33.agrees.read (by simp [adcR64R64Effect_components])).trans g32r8
  have g34r8 : ((Operand.reg 8 : Operand 64).read u34) = r.1 := (e34.agrees.read (by simp [addR64R64Effect_components])).trans g33r8
  have g35r8 : ((Operand.reg 8 : Operand 64).read u35) = r.1 := (e35.agrees.read (by simp [movzxR32M8Effect_components])).trans g34r8
  have g36r8 : ((Operand.reg 8 : Operand 64).read u36) = r.1 := (e36.agrees.read (by simp [adcR64R64Effect_components])).trans g35r8
  have g37r8 : ((Operand.reg 8 : Operand 64).read u37) = r.1 := (e37.agrees.read (by simp [setccR8Effect_components])).trans g36r8
  have g38r8 : ((Operand.reg 8 : Operand 64).read u38) = r.1 := (e38.agrees.read (by simp [movzxR32R8Effect_components])).trans g37r8
  have g39r8 : ((Operand.reg 8 : Operand 64).read u39) = r.1 := (e39.agrees.read (by simp [movM64R64Effect_components])).trans g38r8
  have g40r8 : ((Operand.reg 8 : Operand 64).read u40) = r.1 := (e40.agrees.read (by simp [movR64M64Effect_components])).trans g39r8
  have g41r8 : ((Operand.reg 8 : Operand 64).read u41) = r.1 := (e41.agrees.read (by simp [movM64R64Effect_components])).trans g40r8
  have g42r8 : ((Operand.reg 8 : Operand 64).read u42) = r.1 := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r8
  have g43r8 : ((Operand.reg 8 : Operand 64).read u43) = r.1 := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r8
  have g44r8 : ((Operand.reg 8 : Operand 64).read u44) = r.1 := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r8
  have g44r0 : ((Operand.reg 0 : Operand 64).read u44) = last.1 := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r0
  have g42r2 : ((Operand.reg 2 : Operand 64).read u42) = top.1 := (e42.agrees.read (by simp [movR64R64Effect_components])).trans g41r2
  have g43r2 : ((Operand.reg 2 : Operand 64).read u43) = top.1 := (e43.agrees.read (by simp [addR64R64Effect_components])).trans g42r2
  have g44r2 : ((Operand.reg 2 : Operand 64).read u44) = top.1 := (e44.agrees.read (by simp [adcR64Imm8Effect_components])).trans g43r2
  have keep56 : slot s u44 56 = slot s u21 56 := by
    as_aux_lemma =>
      have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 16) 8, .mem (stackPtr s - 112 + 24) 8]) u21 u44 := ((((((((((((((((((((((e22.agrees.trans e23.agrees).trans e24.agrees).trans e25.agrees).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans e34.agrees).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans ag39).trans e40.agrees).trans ag41).trans e42.agrees).trans e43.agrees).trans e44.agrees).mono (by simp only [addR64R64Effect_components, leaR64Effect_components, setccR8Effect_components, adcR64R64Effect_components, movR64R64Effect_components, mulR64Effect_components, xorR32R32Effect_components, movzxR32M8Effect_components, movzxR32R8Effect_components, f38.rsp, movR64M64Effect_components, f40.rsp, adcR64Imm8Effect_components]; simp)
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
      intro i hi c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      all_goals try exact id
      all_goals try contradiction
      all_goals rintro ⟨j, hj, he⟩
      all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot56 : slot s u44 56 = 0xffffffffffffffff := keep56.trans (by
    change memLoad u21.external _ 64 = 0xffffffffffffffff
    rw [mem21]
    exact state.slots.p0)
  have keep48 : slot s u44 48 = slot s u21 48 := by
    as_aux_lemma =>
      have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 16) 8, .mem (stackPtr s - 112 + 24) 8]) u21 u44 := ((((((((((((((((((((((e22.agrees.trans e23.agrees).trans e24.agrees).trans e25.agrees).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans e34.agrees).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans ag39).trans e40.agrees).trans ag41).trans e42.agrees).trans e43.agrees).trans e44.agrees).mono (by simp only [addR64R64Effect_components, leaR64Effect_components, setccR8Effect_components, adcR64R64Effect_components, movR64R64Effect_components, mulR64Effect_components, xorR32R32Effect_components, movzxR32M8Effect_components, movzxR32R8Effect_components, f38.rsp, movR64M64Effect_components, f40.rsp, adcR64Imm8Effect_components]; simp)
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
      intro i hi c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      all_goals try exact id
      all_goals try contradiction
      all_goals rintro ⟨j, hj, he⟩
      all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot48 : slot s u44 48 = 0xffffffff := keep48.trans (by
    change memLoad u21.external _ 64 = 0xffffffff
    rw [mem21]
    exact state.slots.p1)
  have keep40 : slot s u44 40 = slot s u21 40 := by
    as_aux_lemma =>
      have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 16) 8, .mem (stackPtr s - 112 + 24) 8]) u21 u44 := ((((((((((((((((((((((e22.agrees.trans e23.agrees).trans e24.agrees).trans e25.agrees).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans e34.agrees).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans ag39).trans e40.agrees).trans ag41).trans e42.agrees).trans e43.agrees).trans e44.agrees).mono (by simp only [addR64R64Effect_components, leaR64Effect_components, setccR8Effect_components, adcR64R64Effect_components, movR64R64Effect_components, mulR64Effect_components, xorR32R32Effect_components, movzxR32M8Effect_components, movzxR32R8Effect_components, f38.rsp, movR64M64Effect_components, f40.rsp, adcR64Imm8Effect_components]; simp)
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
      intro i hi c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      all_goals try exact id
      all_goals try contradiction
      all_goals rintro ⟨j, hj, he⟩
      all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot40 : slot s u44 40 = 0 := keep40.trans (by
    change memLoad u21.external _ 64 = 0
    rw [mem21]
    exact state.slots.p2)
  have keep32 : slot s u44 32 = slot s u21 32 := by
    as_aux_lemma =>
      have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 16) 8, .mem (stackPtr s - 112 + 24) 8]) u21 u44 := ((((((((((((((((((((((e22.agrees.trans e23.agrees).trans e24.agrees).trans e25.agrees).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans e34.agrees).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans ag39).trans e40.agrees).trans ag41).trans e42.agrees).trans e43.agrees).trans e44.agrees).mono (by simp only [addR64R64Effect_components, leaR64Effect_components, setccR8Effect_components, adcR64R64Effect_components, movR64R64Effect_components, mulR64Effect_components, xorR32R32Effect_components, movzxR32M8Effect_components, movzxR32R8Effect_components, f38.rsp, movR64M64Effect_components, f40.rsp, adcR64Imm8Effect_components]; simp)
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
      intro i hi c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      all_goals try exact id
      all_goals try contradiction
      all_goals rintro ⟨j, hj, he⟩
      all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot32 : slot s u44 32 = 0xffffffff00000001 := keep32.trans (by
    change memLoad u21.external _ 64 = 0xffffffff00000001
    rw [mem21]
    exact state.slots.p3)
  have keep16 : slot s u44 16 = slot s u39 16 := by
    as_aux_lemma =>
      have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8]) u39 u44 := ((((e40.agrees.trans ag41).trans e42.agrees).trans e43.agrees).trans e44.agrees).mono (by simp only [movR64M64Effect_components, f40.rsp, movR64R64Effect_components, addR64R64Effect_components, adcR64Imm8Effect_components]; simp)
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
      intro i hi c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl)
      all_goals try exact id
      all_goals try contradiction
      all_goals rintro ⟨j, hj, he⟩
      all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot16 := keep16.trans wr39
  have keep24 : slot s u44 24 = slot s u41 24 := by
    as_aux_lemma =>
      have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ []) u41 u44 := ((e42.agrees.trans e43.agrees).trans e44.agrees).mono (by simp only [movR64R64Effect_components, addR64R64Effect_components, adcR64Imm8Effect_components]; simp)
      apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
      intro i hi c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals try exact id
      all_goals try contradiction
  have slot24 := keep24.trans wr41
  refine ⟨u44, ⟨44, (((((((((((((((((((((((runPrefix.trans run22).trans run23).trans run24).trans run25).trans run26).trans run27).trans run28).trans run29).trans run30).trans run31).trans run32).trans run33).trans run34).trans run35).trans run36).trans run37).trans run38).trans run39).trans run40).trans run41).trans run42).trans run43).trans run44)⟩, f44, e44.rip, ⟨slot56, slot48, slot40, slot32⟩, g44r7, g44r11, ?_, ?_, ?_⟩
  · change ((Operand.reg 2 : Operand 64).read u44).toNat + (slot s u44 24).toNat + 2^64*(slot s u44 16).toNat = ((Operand.reg 0 : Operand 64).read u44).toNat + 2^64*((Operand.reg 12 : Operand 64).read u44).toNat
    rw [g44r2, slot24, slot16, g44r0, g44r12]
    have h := add_top_value top.1 input7 top.2
    have hc : top.2.toNat < 2^64 := Nat.lt_of_le_of_lt (Bool.toNat_le _) (by decide)
    simpa only [P256.Proofs.Field.Montgomery.wordBase, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hc, last, lasthi] using h.symm
  · change (⟨((Operand.reg 3 : Operand 64).read u44), ((Operand.reg 1 : Operand 64).read u44), ((Operand.reg 8 : Operand 64).read u44), ((Operand.reg 0 : Operand 64).read u44)⟩ : Limbs) = _
    rw [g44r3, g44r1, g44r8, g44r0]
    rfl
  · change ((Operand.reg 12 : Operand 64).read u44) = _
    rw [g44r12]
    rfl
end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthRound
