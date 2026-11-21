import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Lower
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Field.Montgomery (add64 adc64 product64)

attribute [local irreducible] add64 adc64 product64

set_option maxHeartbeats 800000 in
theorem upper [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (entry : Prefix s t v)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256))) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x113490 ∧
      ModulusSlots s u ∧ slot s u 16 = 1 ∧ u.regValue .rcx = 1 ∧
      u.regValue .rsi = s.regValue .rsi ∧ u.regValue .rdi = s.regValue .rdi ∧
      u.regValue .rbp = 0xffffffffffffffff ∧ u.regValue .r13 = 0xffffffff ∧
      (⟨u.regValue .r14, u.regValue .r15, u.regValue .r11, u.regValue .rbx⟩ : Limbs) =
        words (inputWords v) := by
  let a := inputWords v
  let p0 := product64 0xffffffffffffffff a.l0
  let p1 := product64 0xffffffff a.l0
  let x := add64 p1.1 a.l1
  let hi1 := adc64 p1.2 0 x.2
  let z := add64 p0.1 a.l0
  let y := adc64 x.1 p0.2 z.2
  let k := adc64 hi1.1 0 y.2
  let q := add64 0 a.l2
  let qh := adc64 0 0 q.2
  let w := add64 q.1 k.1
  let wh := adc64 qh.1 0 w.2
  let p3 := product64 0xffffffff00000001 a.l0
  let z3 := add64 p3.1 a.l3
  let zh := adc64 p3.2 0 z3.2
  let r3 := add64 z3.1 wh.1
  let rh := adc64 zh.1 0 r3.2
  have f23 := entry.frame
  have ip23 := entry.rip
  have g23r1 : ((Operand.reg 1 : Operand 64).read t) = 1 :=
    entry.rcx
  have g23r6 : ((Operand.reg 6 : Operand 64).read t) = s.regValue .rsi :=
    entry.rsi
  have g23r7 : ((Operand.reg 7 : Operand 64).read t) = s.regValue .rdi :=
    entry.rdi
  have g23r5 : ((Operand.reg 5 : Operand 64).read t) = 0xffffffffffffffff :=
    entry.rbp
  have g23r13 : ((Operand.reg 13 : Operand 64).read t) = 0xffffffff :=
    entry.r13
  have g23r10 : ((Operand.reg 10 : Operand 64).read t) = s.regValue .rdx :=
    entry.r10
  have g23r9 : ((Operand.reg 9 : Operand 64).read t) = a.l0 :=
    entry.r9
  have g23r14 : ((Operand.reg 14 : Operand 64).read t) = y.1 :=
    entry.r14
  have g23r3 : ((Operand.reg 3 : Operand 64).read t) = k.1 :=
    entry.rbx
  have wr23_16 := entry.inverse
  have wr23_56 := entry.modulus0
  have wr23_48 := entry.modulus1
  obtain ⟨u24, run24, ready24, e24⟩ :=
    (mov_r64_m64_effect_step 0x11344e 0x49 (by simp [RexWPrefix]) 0 (.base 10 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f23.machine f23.bindingsSupported)
      (programText_slice (programLoaded_codeIn f23.loaded) 0x1344e _ (by decide) (by decide +kernel))
      ⟨ip23, by
        change MemReadable t (((Operand.reg 10 : Operand 64).read t) + 16) 8
        rw [g23r10]
        exact modulus_readable pre f23 (j := 2) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13452 (by decide)))
  change (movR64M64Effect 0x11344e 0 (.base 10 (.d8 16)) t).Holds t u24 at e24
  have f24 := f23.after_registers ready24 e24.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load24 : memLoad t.external (((Operand.reg 10 : Operand 64).read t) + 16) 64 = 0 := by
    rw [g23r10]
    exact modulus_limb pre f23 2 (by decide)
  have g24r0 : ((Operand.reg 0 : Operand 64).read u24) = 0 := by
    have h := e24.writes
    change ((Operand.reg 0 : Operand 64).read u24) = memLoad t.external (((Operand.reg 10 : Operand 64).read t) + 16) 64 at h
    rw [load24] at h
    exact h
  obtain ⟨u25, run25, ready25, e25⟩ :=
    (mov_m64_r64_effect_step_any 0x113452 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances (readyToStep f24.machine f24.bindingsSupported)
      (programText_slice (programLoaded_codeIn f24.loaded) 0x13452 _ (by decide) (by decide +kernel))
      ⟨e24.rip, ScalarFrame.stack_writable pre.toCalleePre f24 (offset := 40) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f24 (offset := 40) (len := 8) (codeOffset := 0x13452) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13457 (by decide)))
  change (movM64R64Effect 0x113452 0 (.sib 4 none 0 (.d8 40)) u24).Holds u24 u25 at e25
  have ag25 : AgreesExcept [.mem (stackPtr u24 + 40) 8, .rip] u24 u25 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e25.agrees
  have f25 := after_store pre f24 ready25 (offset := 40) (by decide) ag25
  have wr25 : slot s u25 40 = 0 := by
    have h := e25.writes
    change memLoad u25.external (stackPtr u24 + 40) 64 = ((Operand.reg 0 : Operand 64).read u24) at h
    rw [f24.rsp, g24r0] at h
    exact h
  have g24r9 : ((Operand.reg 9 : Operand 64).read u24) = a.l0 := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r9
  have g25r9 : ((Operand.reg 9 : Operand 64).read u25) = a.l0 := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r9
  have g25r0 : ((Operand.reg 0 : Operand 64).read u25) = 0 := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r0
  obtain ⟨u26, run26, ready26, e26⟩ :=
    (mul_r64_effect_step 0x113457 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f25.machine f25.bindingsSupported)
      (programText_slice (programLoaded_codeIn f25.loaded) 0x13457 _ (by decide) (by decide +kernel))
      e25.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1345a (by decide)))
  change (mulR64Effect 0x113457 9 u25).Holds u25 u26 at e26
  have f26 := f25.after_registers ready26 e26.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have g26r0 : ((Operand.reg 0 : Operand 64).read u26) = 0 := by
    have h := e26.writes.1
    change ((Operand.reg 0 : Operand 64).read u26) = ((Operand.reg 0 : Operand 64).read u25) * ((Operand.reg 9 : Operand 64).read u25) at h
    rw [g25r9, g25r0] at h
    simpa [mulHigh64] using h
  have g26r2 : ((Operand.reg 2 : Operand 64).read u26) = 0 := by
    have h := e26.writes.2
    change ((Operand.reg 2 : Operand 64).read u26) = mulHigh64 ((Operand.reg 0 : Operand 64).read u25) ((Operand.reg 9 : Operand 64).read u25) at h
    rw [g25r9, g25r0] at h
    simpa [mulHigh64] using h
  obtain ⟨u27, run27, ready27, e27⟩ :=
    (mov_r64_r64_effect_step 0x11345a 0x49 0xd4 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f26.machine f26.bindingsSupported)
      (programText_slice (programLoaded_codeIn f26.loaded) 0x1345a _ (by decide) (by decide +kernel))
      e26.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1345d (by decide)))
  change (movR64R64Effect 0x11345a 12 2 u26).Holds u26 u27 at e27
  have f27 := f26.after_registers ready27 e27.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g27r12 : ((Operand.reg 12 : Operand 64).read u27) = 0 := by
    have h := e27.writes
    change ((Operand.reg 12 : Operand 64).read u27) = ((Operand.reg 2 : Operand 64).read u26) at h
    rw [g26r2] at h
    exact h
  have g27r0 : ((Operand.reg 0 : Operand 64).read u27) = 0 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r0
  obtain ⟨u28, run28, ready28, e28⟩ :=
    (mov_r64_r64_effect_step 0x11345d 0x49 0xc7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f27.machine f27.bindingsSupported)
      (programText_slice (programLoaded_codeIn f27.loaded) 0x1345d _ (by decide) (by decide +kernel))
      e27.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13460 (by decide)))
  change (movR64R64Effect 0x11345d 15 0 u27).Holds u27 u28 at e28
  have f28 := f27.after_registers ready28 e28.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g28r15 : ((Operand.reg 15 : Operand 64).read u28) = 0 := by
    have h := e28.writes
    change ((Operand.reg 15 : Operand 64).read u28) = ((Operand.reg 0 : Operand 64).read u27) at h
    rw [g27r0] at h
    exact h
  have g24r6 : ((Operand.reg 6 : Operand 64).read u24) = s.regValue .rsi := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r6
  have g25r6 : ((Operand.reg 6 : Operand 64).read u25) = s.regValue .rsi := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r6
  have g26r6 : ((Operand.reg 6 : Operand 64).read u26) = s.regValue .rsi := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r6
  have g27r6 : ((Operand.reg 6 : Operand 64).read u27) = s.regValue .rsi := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r6
  have g28r6 : ((Operand.reg 6 : Operand 64).read u28) = s.regValue .rsi := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r6
  obtain ⟨u29, run29, ready29, e29⟩ :=
    (add_r64_m64_effect_step 0x113460 0x4c (by simp [RexWPrefix]) 7 (.base 6 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f28.machine f28.bindingsSupported)
      (programText_slice (programLoaded_codeIn f28.loaded) 0x13460 _ (by decide) (by decide +kernel))
      ⟨e28.rip, by
        change MemReadable u28 (((Operand.reg 6 : Operand 64).read u28) + 16) 8
        rw [g28r6]
        exact input_readable pre f28 (j := 2) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13464 (by decide)))
  change (addR64M64Effect 0x113460 15 (.base 6 (.d8 16)) u28).Holds u28 u29 at e29
  have f29 := f28.after_registers ready29 e29.agrees (by simp [addR64M64Effect_components, Component.Covers]) (by simp [addR64M64Effect_components])
  have load29 : memLoad u28.external (((Operand.reg 6 : Operand 64).read u28) + 16) 64 = a.l2 := by
    rw [g28r6]
    simpa [a, inputWords] using input_limb pre f28 input 2 (by decide)
  have g29r15 : ((Operand.reg 15 : Operand 64).read u29) = q.1 := by
    have h := e29.writes
    change ((Operand.reg 15 : Operand 64).read u29) = (addSpec ((Operand.reg 15 : Operand 64).read u28) (memLoad u28.external (((Operand.reg 6 : Operand 64).read u28) + 16) 64)).1 at h
    rw [load29, g28r15] at h
    simpa only [q, add64] using h
  have cf29 : (StatusFlags.ofRFLAGS u29.RFLAGS).CF = q.2 := by
    have h := e29.flags.1
    change (StatusFlags.ofRFLAGS u29.RFLAGS).CF = (addSpec ((Operand.reg 15 : Operand 64).read u28) (memLoad u28.external (((Operand.reg 6 : Operand 64).read u28) + 16) 64)).2.CF at h
    rw [load29, g28r15] at h
    simpa only [q, add64] using h
  have g28r12 : ((Operand.reg 12 : Operand 64).read u28) = 0 := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r12
  have g29r12 : ((Operand.reg 12 : Operand 64).read u29) = 0 := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r12
  obtain ⟨u30, run30, ready30, e30⟩ :=
    (adc_r64_imm8_effect_step 0x113464 0x49 0xd4 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f29.machine f29.bindingsSupported)
      (programText_slice (programLoaded_codeIn f29.loaded) 0x13464 _ (by decide) (by decide +kernel))
      e29.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13468 (by decide)))
  change (adcR64Imm8Effect 0x113464 12 0 u29).Holds u29 u30 at e30
  have f30 := f29.after_registers ready30 e30.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g30r12 : ((Operand.reg 12 : Operand 64).read u30) = qh.1 := by
    have h := e30.writes
    change ((Operand.reg 12 : Operand 64).read u30) = (adcSpec ((Operand.reg 12 : Operand 64).read u29) (0) (u29.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g29r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf29] at h
    simpa only [qh, adc64] using h
  have cf30 : (StatusFlags.ofRFLAGS u30.RFLAGS).CF = qh.2 := by
    have h := e30.flags.1
    change (StatusFlags.ofRFLAGS u30.RFLAGS).CF = (adcSpec ((Operand.reg 12 : Operand 64).read u29) (0) (u29.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g29r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf29] at h
    simpa only [qh, adc64] using h
  have g24r3 : ((Operand.reg 3 : Operand 64).read u24) = k.1 := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r3
  have g25r3 : ((Operand.reg 3 : Operand 64).read u25) = k.1 := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r3
  have g26r3 : ((Operand.reg 3 : Operand 64).read u26) = k.1 := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r3
  have g27r3 : ((Operand.reg 3 : Operand 64).read u27) = k.1 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r3
  have g28r3 : ((Operand.reg 3 : Operand 64).read u28) = k.1 := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r3
  have g29r3 : ((Operand.reg 3 : Operand 64).read u29) = k.1 := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r3
  have g30r3 : ((Operand.reg 3 : Operand 64).read u30) = k.1 := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r3
  have g30r15 : ((Operand.reg 15 : Operand 64).read u30) = q.1 := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r15
  obtain ⟨u31, run31, ready31, e31⟩ :=
    (add_r64_r64_effect_step 0x113468 0x49 0xdf (by simp [RexWPrefix]) (by decide)).advances (readyToStep f30.machine f30.bindingsSupported)
      (programText_slice (programLoaded_codeIn f30.loaded) 0x13468 _ (by decide) (by decide +kernel))
      e30.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1346b (by decide)))
  change (addR64R64Effect 0x113468 15 3 u30).Holds u30 u31 at e31
  have f31 := f30.after_registers ready31 e31.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g31r15 : ((Operand.reg 15 : Operand 64).read u31) = w.1 := by
    have h := e31.writes
    change ((Operand.reg 15 : Operand 64).read u31) = (addSpec ((Operand.reg 15 : Operand 64).read u30) (((Operand.reg 3 : Operand 64).read u30))).1 at h
    rw [g30r3, g30r15] at h
    simpa only [w, add64] using h
  have cf31 : (StatusFlags.ofRFLAGS u31.RFLAGS).CF = w.2 := by
    have h := e31.flags.1
    change (StatusFlags.ofRFLAGS u31.RFLAGS).CF = (addSpec ((Operand.reg 15 : Operand 64).read u30) (((Operand.reg 3 : Operand 64).read u30))).2.CF at h
    rw [g30r3, g30r15] at h
    simpa only [w, add64] using h
  have g31r12 : ((Operand.reg 12 : Operand 64).read u31) = qh.1 := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r12
  obtain ⟨u32, run32, ready32, e32⟩ :=
    (adc_r64_imm8_effect_step 0x11346b 0x49 0xd4 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f31.machine f31.bindingsSupported)
      (programText_slice (programLoaded_codeIn f31.loaded) 0x1346b _ (by decide) (by decide +kernel))
      e31.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1346f (by decide)))
  change (adcR64Imm8Effect 0x11346b 12 0 u31).Holds u31 u32 at e32
  have f32 := f31.after_registers ready32 e32.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g32r12 : ((Operand.reg 12 : Operand 64).read u32) = wh.1 := by
    have h := e32.writes
    change ((Operand.reg 12 : Operand 64).read u32) = (adcSpec ((Operand.reg 12 : Operand 64).read u31) (0) (u31.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g31r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf31] at h
    simpa only [wh, adc64] using h
  have cf32 : (StatusFlags.ofRFLAGS u32.RFLAGS).CF = wh.2 := by
    have h := e32.flags.1
    change (StatusFlags.ofRFLAGS u32.RFLAGS).CF = (adcSpec ((Operand.reg 12 : Operand 64).read u31) (0) (u31.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g31r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf31] at h
    simpa only [wh, adc64] using h
  have g24r10 : ((Operand.reg 10 : Operand 64).read u24) = s.regValue .rdx := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r10
  have g25r10 : ((Operand.reg 10 : Operand 64).read u25) = s.regValue .rdx := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r10
  have g26r10 : ((Operand.reg 10 : Operand 64).read u26) = s.regValue .rdx := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r10
  have g27r10 : ((Operand.reg 10 : Operand 64).read u27) = s.regValue .rdx := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r10
  have g28r10 : ((Operand.reg 10 : Operand 64).read u28) = s.regValue .rdx := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r10
  have g29r10 : ((Operand.reg 10 : Operand 64).read u29) = s.regValue .rdx := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r10
  have g30r10 : ((Operand.reg 10 : Operand 64).read u30) = s.regValue .rdx := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r10
  have g31r10 : ((Operand.reg 10 : Operand 64).read u31) = s.regValue .rdx := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r10
  have g32r10 : ((Operand.reg 10 : Operand 64).read u32) = s.regValue .rdx := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r10
  obtain ⟨u33, run33, ready33, e33⟩ :=
    (mov_r64_m64_effect_step 0x11346f 0x49 (by simp [RexWPrefix]) 0 (.base 10 (.d8 24)) (by decide) rfl rfl).advances (readyToStep f32.machine f32.bindingsSupported)
      (programText_slice (programLoaded_codeIn f32.loaded) 0x1346f _ (by decide) (by decide +kernel))
      ⟨e32.rip, by
        change MemReadable u32 (((Operand.reg 10 : Operand 64).read u32) + 24) 8
        rw [g32r10]
        exact modulus_readable pre f32 (j := 3) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13473 (by decide)))
  change (movR64M64Effect 0x11346f 0 (.base 10 (.d8 24)) u32).Holds u32 u33 at e33
  have f33 := f32.after_registers ready33 e33.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load33 : memLoad u32.external (((Operand.reg 10 : Operand 64).read u32) + 24) 64 = 0xffffffff00000001 := by
    rw [g32r10]
    exact modulus_limb pre f32 3 (by decide)
  have g33r0 : ((Operand.reg 0 : Operand 64).read u33) = 0xffffffff00000001 := by
    have h := e33.writes
    change ((Operand.reg 0 : Operand 64).read u33) = memLoad u32.external (((Operand.reg 10 : Operand 64).read u32) + 24) 64 at h
    rw [load33] at h
    exact h
  obtain ⟨u34, run34, ready34, e34⟩ :=
    (mov_m64_r64_effect_step_any 0x113473 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances (readyToStep f33.machine f33.bindingsSupported)
      (programText_slice (programLoaded_codeIn f33.loaded) 0x13473 _ (by decide) (by decide +kernel))
      ⟨e33.rip, ScalarFrame.stack_writable pre.toCalleePre f33 (offset := 32) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f33 (offset := 32) (len := 8) (codeOffset := 0x13473) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13478 (by decide)))
  change (movM64R64Effect 0x113473 0 (.sib 4 none 0 (.d8 32)) u33).Holds u33 u34 at e34
  have ag34 : AgreesExcept [.mem (stackPtr u33 + 32) 8, .rip] u33 u34 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e34.agrees
  have f34 := after_store pre f33 ready34 (offset := 32) (by decide) ag34
  have wr34 : slot s u34 32 = 0xffffffff00000001 := by
    have h := e34.writes
    change memLoad u34.external (stackPtr u33 + 32) 64 = ((Operand.reg 0 : Operand 64).read u33) at h
    rw [f33.rsp, g33r0] at h
    exact h
  have g26r9 : ((Operand.reg 9 : Operand 64).read u26) = a.l0 := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r9
  have g27r9 : ((Operand.reg 9 : Operand 64).read u27) = a.l0 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r9
  have g28r9 : ((Operand.reg 9 : Operand 64).read u28) = a.l0 := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r9
  have g29r9 : ((Operand.reg 9 : Operand 64).read u29) = a.l0 := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r9
  have g30r9 : ((Operand.reg 9 : Operand 64).read u30) = a.l0 := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r9
  have g31r9 : ((Operand.reg 9 : Operand 64).read u31) = a.l0 := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r9
  have g32r9 : ((Operand.reg 9 : Operand 64).read u32) = a.l0 := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r9
  have g33r9 : ((Operand.reg 9 : Operand 64).read u33) = a.l0 := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r9
  have g34r9 : ((Operand.reg 9 : Operand 64).read u34) = a.l0 := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r9
  have g34r0 : ((Operand.reg 0 : Operand 64).read u34) = 0xffffffff00000001 := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r0
  obtain ⟨u35, run35, ready35, e35⟩ :=
    (mul_r64_effect_step 0x113478 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f34.machine f34.bindingsSupported)
      (programText_slice (programLoaded_codeIn f34.loaded) 0x13478 _ (by decide) (by decide +kernel))
      e34.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1347b (by decide)))
  change (mulR64Effect 0x113478 9 u34).Holds u34 u35 at e35
  have f35 := f34.after_registers ready35 e35.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have g35r0 : ((Operand.reg 0 : Operand 64).read u35) = p3.1 := by
    have h := e35.writes.1
    change ((Operand.reg 0 : Operand 64).read u35) = ((Operand.reg 0 : Operand 64).read u34) * ((Operand.reg 9 : Operand 64).read u34) at h
    rw [g34r9, g34r0] at h
    simpa only [p3, product64] using h
  have g35r2 : ((Operand.reg 2 : Operand 64).read u35) = p3.2 := by
    have h := e35.writes.2
    change ((Operand.reg 2 : Operand 64).read u35) = mulHigh64 ((Operand.reg 0 : Operand 64).read u34) ((Operand.reg 9 : Operand 64).read u34) at h
    rw [g34r9, g34r0] at h
    simpa only [p3, product64] using h
  obtain ⟨u36, run36, ready36, e36⟩ :=
    (mov_r64_r64_effect_step 0x11347b 0x48 0xd3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f35.machine f35.bindingsSupported)
      (programText_slice (programLoaded_codeIn f35.loaded) 0x1347b _ (by decide) (by decide +kernel))
      e35.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1347e (by decide)))
  change (movR64R64Effect 0x11347b 3 2 u35).Holds u35 u36 at e36
  have f36 := f35.after_registers ready36 e36.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g36r3 : ((Operand.reg 3 : Operand 64).read u36) = p3.2 := by
    have h := e36.writes
    change ((Operand.reg 3 : Operand 64).read u36) = ((Operand.reg 2 : Operand 64).read u35) at h
    rw [g35r2] at h
    simpa only [p3, product64] using h
  have g36r0 : ((Operand.reg 0 : Operand 64).read u36) = p3.1 := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r0
  obtain ⟨u37, run37, ready37, e37⟩ :=
    (mov_r64_r64_effect_step 0x11347e 0x49 0xc3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f36.machine f36.bindingsSupported)
      (programText_slice (programLoaded_codeIn f36.loaded) 0x1347e _ (by decide) (by decide +kernel))
      e36.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13481 (by decide)))
  change (movR64R64Effect 0x11347e 11 0 u36).Holds u36 u37 at e37
  have f37 := f36.after_registers ready37 e37.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g37r11 : ((Operand.reg 11 : Operand 64).read u37) = p3.1 := by
    have h := e37.writes
    change ((Operand.reg 11 : Operand 64).read u37) = ((Operand.reg 0 : Operand 64).read u36) at h
    rw [g36r0] at h
    simpa only [p3, product64] using h
  have g29r6 : ((Operand.reg 6 : Operand 64).read u29) = s.regValue .rsi := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r6
  have g30r6 : ((Operand.reg 6 : Operand 64).read u30) = s.regValue .rsi := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r6
  have g31r6 : ((Operand.reg 6 : Operand 64).read u31) = s.regValue .rsi := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r6
  have g32r6 : ((Operand.reg 6 : Operand 64).read u32) = s.regValue .rsi := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r6
  have g33r6 : ((Operand.reg 6 : Operand 64).read u33) = s.regValue .rsi := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r6
  have g34r6 : ((Operand.reg 6 : Operand 64).read u34) = s.regValue .rsi := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r6
  have g35r6 : ((Operand.reg 6 : Operand 64).read u35) = s.regValue .rsi := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r6
  have g36r6 : ((Operand.reg 6 : Operand 64).read u36) = s.regValue .rsi := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r6
  have g37r6 : ((Operand.reg 6 : Operand 64).read u37) = s.regValue .rsi := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r6
  obtain ⟨u38, run38, ready38, e38⟩ :=
    (add_r64_m64_effect_step 0x113481 0x4c (by simp [RexWPrefix]) 3 (.base 6 (.d8 24)) (by decide) rfl rfl).advances (readyToStep f37.machine f37.bindingsSupported)
      (programText_slice (programLoaded_codeIn f37.loaded) 0x13481 _ (by decide) (by decide +kernel))
      ⟨e37.rip, by
        change MemReadable u37 (((Operand.reg 6 : Operand 64).read u37) + 24) 8
        rw [g37r6]
        exact input_readable pre f37 (j := 3) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13485 (by decide)))
  change (addR64M64Effect 0x113481 11 (.base 6 (.d8 24)) u37).Holds u37 u38 at e38
  have f38 := f37.after_registers ready38 e38.agrees (by simp [addR64M64Effect_components, Component.Covers]) (by simp [addR64M64Effect_components])
  have load38 : memLoad u37.external (((Operand.reg 6 : Operand 64).read u37) + 24) 64 = a.l3 := by
    rw [g37r6]
    simpa [a, inputWords] using input_limb pre f37 input 3 (by decide)
  have g38r11 : ((Operand.reg 11 : Operand 64).read u38) = z3.1 := by
    have h := e38.writes
    change ((Operand.reg 11 : Operand 64).read u38) = (addSpec ((Operand.reg 11 : Operand 64).read u37) (memLoad u37.external (((Operand.reg 6 : Operand 64).read u37) + 24) 64)).1 at h
    rw [load38, g37r11] at h
    simpa only [z3, add64] using h
  have cf38 : (StatusFlags.ofRFLAGS u38.RFLAGS).CF = z3.2 := by
    have h := e38.flags.1
    change (StatusFlags.ofRFLAGS u38.RFLAGS).CF = (addSpec ((Operand.reg 11 : Operand 64).read u37) (memLoad u37.external (((Operand.reg 6 : Operand 64).read u37) + 24) 64)).2.CF at h
    rw [load38, g37r11] at h
    simpa only [z3, add64] using h
  have g37r3 : ((Operand.reg 3 : Operand 64).read u37) = p3.2 := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r3
  have g38r3 : ((Operand.reg 3 : Operand 64).read u38) = p3.2 := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r3
  obtain ⟨u39, run39, ready39, e39⟩ :=
    (adc_r64_imm8_effect_step 0x113485 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f38.machine f38.bindingsSupported)
      (programText_slice (programLoaded_codeIn f38.loaded) 0x13485 _ (by decide) (by decide +kernel))
      e38.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13489 (by decide)))
  change (adcR64Imm8Effect 0x113485 3 0 u38).Holds u38 u39 at e39
  have f39 := f38.after_registers ready39 e39.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g39r3 : ((Operand.reg 3 : Operand 64).read u39) = zh.1 := by
    have h := e39.writes
    change ((Operand.reg 3 : Operand 64).read u39) = (adcSpec ((Operand.reg 3 : Operand 64).read u38) (0) (u38.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g38r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf38] at h
    simpa only [zh, adc64] using h
  have cf39 : (StatusFlags.ofRFLAGS u39.RFLAGS).CF = zh.2 := by
    have h := e39.flags.1
    change (StatusFlags.ofRFLAGS u39.RFLAGS).CF = (adcSpec ((Operand.reg 3 : Operand 64).read u38) (0) (u38.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g38r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf38] at h
    simpa only [zh, adc64] using h
  have g33r12 : ((Operand.reg 12 : Operand 64).read u33) = wh.1 := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r12
  have g34r12 : ((Operand.reg 12 : Operand 64).read u34) = wh.1 := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r12
  have g35r12 : ((Operand.reg 12 : Operand 64).read u35) = wh.1 := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r12
  have g36r12 : ((Operand.reg 12 : Operand 64).read u36) = wh.1 := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r12
  have g37r12 : ((Operand.reg 12 : Operand 64).read u37) = wh.1 := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r12
  have g38r12 : ((Operand.reg 12 : Operand 64).read u38) = wh.1 := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r12
  have g39r12 : ((Operand.reg 12 : Operand 64).read u39) = wh.1 := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r12
  have g39r11 : ((Operand.reg 11 : Operand 64).read u39) = z3.1 := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r11
  obtain ⟨u40, run40, ready40, e40⟩ :=
    (add_r64_r64_effect_step 0x113489 0x4d 0xe3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f39.machine f39.bindingsSupported)
      (programText_slice (programLoaded_codeIn f39.loaded) 0x13489 _ (by decide) (by decide +kernel))
      e39.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1348c (by decide)))
  change (addR64R64Effect 0x113489 11 12 u39).Holds u39 u40 at e40
  have f40 := f39.after_registers ready40 e40.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g40r11 : ((Operand.reg 11 : Operand 64).read u40) = r3.1 := by
    have h := e40.writes
    change ((Operand.reg 11 : Operand 64).read u40) = (addSpec ((Operand.reg 11 : Operand 64).read u39) (((Operand.reg 12 : Operand 64).read u39))).1 at h
    rw [g39r12, g39r11] at h
    simpa only [r3, add64] using h
  have cf40 : (StatusFlags.ofRFLAGS u40.RFLAGS).CF = r3.2 := by
    have h := e40.flags.1
    change (StatusFlags.ofRFLAGS u40.RFLAGS).CF = (addSpec ((Operand.reg 11 : Operand 64).read u39) (((Operand.reg 12 : Operand 64).read u39))).2.CF at h
    rw [g39r12, g39r11] at h
    simpa only [r3, add64] using h
  have g40r3 : ((Operand.reg 3 : Operand 64).read u40) = zh.1 := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r3
  obtain ⟨u41, run41, ready41, e41⟩ :=
    (adc_r64_imm8_effect_step 0x11348c 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f40.machine f40.bindingsSupported)
      (programText_slice (programLoaded_codeIn f40.loaded) 0x1348c _ (by decide) (by decide +kernel))
      e40.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13490 (by decide)))
  change (adcR64Imm8Effect 0x11348c 3 0 u40).Holds u40 u41 at e41
  have f41 := f40.after_registers ready41 e41.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g41r3 : ((Operand.reg 3 : Operand 64).read u41) = rh.1 := by
    have h := e41.writes
    change ((Operand.reg 3 : Operand 64).read u41) = (adcSpec ((Operand.reg 3 : Operand 64).read u40) (0) (u40.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g40r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf40] at h
    simpa only [rh, adc64] using h
  have cf41 : (StatusFlags.ofRFLAGS u41.RFLAGS).CF = rh.2 := by
    have h := e41.flags.1
    change (StatusFlags.ofRFLAGS u41.RFLAGS).CF = (adcSpec ((Operand.reg 3 : Operand 64).read u40) (0) (u40.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g40r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf40] at h
    simpa only [rh, adc64] using h
  have g24r1 : ((Operand.reg 1 : Operand 64).read u24) = 1 := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r1
  have g25r1 : ((Operand.reg 1 : Operand 64).read u25) = 1 := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r1
  have g26r1 : ((Operand.reg 1 : Operand 64).read u26) = 1 := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r1
  have g27r1 : ((Operand.reg 1 : Operand 64).read u27) = 1 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r1
  have g28r1 : ((Operand.reg 1 : Operand 64).read u28) = 1 := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r1
  have g29r1 : ((Operand.reg 1 : Operand 64).read u29) = 1 := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r1
  have g30r1 : ((Operand.reg 1 : Operand 64).read u30) = 1 := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r1
  have g31r1 : ((Operand.reg 1 : Operand 64).read u31) = 1 := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r1
  have g32r1 : ((Operand.reg 1 : Operand 64).read u32) = 1 := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r1
  have g33r1 : ((Operand.reg 1 : Operand 64).read u33) = 1 := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r1
  have g34r1 : ((Operand.reg 1 : Operand 64).read u34) = 1 := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r1
  have g35r1 : ((Operand.reg 1 : Operand 64).read u35) = 1 := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r1
  have g36r1 : ((Operand.reg 1 : Operand 64).read u36) = 1 := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r1
  have g37r1 : ((Operand.reg 1 : Operand 64).read u37) = 1 := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r1
  have g38r1 : ((Operand.reg 1 : Operand 64).read u38) = 1 := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r1
  have g39r1 : ((Operand.reg 1 : Operand 64).read u39) = 1 := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r1
  have g40r1 : ((Operand.reg 1 : Operand 64).read u40) = 1 := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r1
  have g41r1 : ((Operand.reg 1 : Operand 64).read u41) = 1 := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r1
  have g38r6 : ((Operand.reg 6 : Operand 64).read u38) = s.regValue .rsi := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r6
  have g39r6 : ((Operand.reg 6 : Operand 64).read u39) = s.regValue .rsi := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r6
  have g40r6 : ((Operand.reg 6 : Operand 64).read u40) = s.regValue .rsi := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r6
  have g41r6 : ((Operand.reg 6 : Operand 64).read u41) = s.regValue .rsi := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r6
  have g24r7 : ((Operand.reg 7 : Operand 64).read u24) = s.regValue .rdi := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r7
  have g25r7 : ((Operand.reg 7 : Operand 64).read u25) = s.regValue .rdi := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r7
  have g26r7 : ((Operand.reg 7 : Operand 64).read u26) = s.regValue .rdi := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r7
  have g27r7 : ((Operand.reg 7 : Operand 64).read u27) = s.regValue .rdi := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r7
  have g28r7 : ((Operand.reg 7 : Operand 64).read u28) = s.regValue .rdi := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r7
  have g29r7 : ((Operand.reg 7 : Operand 64).read u29) = s.regValue .rdi := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r7
  have g30r7 : ((Operand.reg 7 : Operand 64).read u30) = s.regValue .rdi := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r7
  have g31r7 : ((Operand.reg 7 : Operand 64).read u31) = s.regValue .rdi := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r7
  have g32r7 : ((Operand.reg 7 : Operand 64).read u32) = s.regValue .rdi := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r7
  have g33r7 : ((Operand.reg 7 : Operand 64).read u33) = s.regValue .rdi := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r7
  have g34r7 : ((Operand.reg 7 : Operand 64).read u34) = s.regValue .rdi := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r7
  have g35r7 : ((Operand.reg 7 : Operand 64).read u35) = s.regValue .rdi := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r7
  have g36r7 : ((Operand.reg 7 : Operand 64).read u36) = s.regValue .rdi := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r7
  have g37r7 : ((Operand.reg 7 : Operand 64).read u37) = s.regValue .rdi := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r7
  have g38r7 : ((Operand.reg 7 : Operand 64).read u38) = s.regValue .rdi := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r7
  have g39r7 : ((Operand.reg 7 : Operand 64).read u39) = s.regValue .rdi := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r7
  have g40r7 : ((Operand.reg 7 : Operand 64).read u40) = s.regValue .rdi := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r7
  have g41r7 : ((Operand.reg 7 : Operand 64).read u41) = s.regValue .rdi := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r7
  have g24r5 : ((Operand.reg 5 : Operand 64).read u24) = 0xffffffffffffffff := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r5
  have g25r5 : ((Operand.reg 5 : Operand 64).read u25) = 0xffffffffffffffff := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r5
  have g26r5 : ((Operand.reg 5 : Operand 64).read u26) = 0xffffffffffffffff := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r5
  have g27r5 : ((Operand.reg 5 : Operand 64).read u27) = 0xffffffffffffffff := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r5
  have g28r5 : ((Operand.reg 5 : Operand 64).read u28) = 0xffffffffffffffff := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r5
  have g29r5 : ((Operand.reg 5 : Operand 64).read u29) = 0xffffffffffffffff := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r5
  have g30r5 : ((Operand.reg 5 : Operand 64).read u30) = 0xffffffffffffffff := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r5
  have g31r5 : ((Operand.reg 5 : Operand 64).read u31) = 0xffffffffffffffff := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r5
  have g32r5 : ((Operand.reg 5 : Operand 64).read u32) = 0xffffffffffffffff := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r5
  have g33r5 : ((Operand.reg 5 : Operand 64).read u33) = 0xffffffffffffffff := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r5
  have g34r5 : ((Operand.reg 5 : Operand 64).read u34) = 0xffffffffffffffff := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r5
  have g35r5 : ((Operand.reg 5 : Operand 64).read u35) = 0xffffffffffffffff := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r5
  have g36r5 : ((Operand.reg 5 : Operand 64).read u36) = 0xffffffffffffffff := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r5
  have g37r5 : ((Operand.reg 5 : Operand 64).read u37) = 0xffffffffffffffff := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r5
  have g38r5 : ((Operand.reg 5 : Operand 64).read u38) = 0xffffffffffffffff := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r5
  have g39r5 : ((Operand.reg 5 : Operand 64).read u39) = 0xffffffffffffffff := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r5
  have g40r5 : ((Operand.reg 5 : Operand 64).read u40) = 0xffffffffffffffff := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r5
  have g41r5 : ((Operand.reg 5 : Operand 64).read u41) = 0xffffffffffffffff := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r5
  have g24r13 : ((Operand.reg 13 : Operand 64).read u24) = 0xffffffff := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r13
  have g25r13 : ((Operand.reg 13 : Operand 64).read u25) = 0xffffffff := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r13
  have g26r13 : ((Operand.reg 13 : Operand 64).read u26) = 0xffffffff := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r13
  have g27r13 : ((Operand.reg 13 : Operand 64).read u27) = 0xffffffff := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r13
  have g28r13 : ((Operand.reg 13 : Operand 64).read u28) = 0xffffffff := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r13
  have g29r13 : ((Operand.reg 13 : Operand 64).read u29) = 0xffffffff := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r13
  have g30r13 : ((Operand.reg 13 : Operand 64).read u30) = 0xffffffff := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r13
  have g31r13 : ((Operand.reg 13 : Operand 64).read u31) = 0xffffffff := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r13
  have g32r13 : ((Operand.reg 13 : Operand 64).read u32) = 0xffffffff := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r13
  have g33r13 : ((Operand.reg 13 : Operand 64).read u33) = 0xffffffff := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r13
  have g34r13 : ((Operand.reg 13 : Operand 64).read u34) = 0xffffffff := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r13
  have g35r13 : ((Operand.reg 13 : Operand 64).read u35) = 0xffffffff := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r13
  have g36r13 : ((Operand.reg 13 : Operand 64).read u36) = 0xffffffff := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r13
  have g37r13 : ((Operand.reg 13 : Operand 64).read u37) = 0xffffffff := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r13
  have g38r13 : ((Operand.reg 13 : Operand 64).read u38) = 0xffffffff := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r13
  have g39r13 : ((Operand.reg 13 : Operand 64).read u39) = 0xffffffff := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r13
  have g40r13 : ((Operand.reg 13 : Operand 64).read u40) = 0xffffffff := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r13
  have g41r13 : ((Operand.reg 13 : Operand 64).read u41) = 0xffffffff := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r13
  have g24r14 : ((Operand.reg 14 : Operand 64).read u24) = y.1 := (e24.agrees.read (by simp [movR64M64Effect_components])).trans g23r14
  have g25r14 : ((Operand.reg 14 : Operand 64).read u25) = y.1 := (e25.agrees.read (by simp [movM64R64Effect_components])).trans g24r14
  have g26r14 : ((Operand.reg 14 : Operand 64).read u26) = y.1 := (e26.agrees.read (by simp [mulR64Effect_components])).trans g25r14
  have g27r14 : ((Operand.reg 14 : Operand 64).read u27) = y.1 := (e27.agrees.read (by simp [movR64R64Effect_components])).trans g26r14
  have g28r14 : ((Operand.reg 14 : Operand 64).read u28) = y.1 := (e28.agrees.read (by simp [movR64R64Effect_components])).trans g27r14
  have g29r14 : ((Operand.reg 14 : Operand 64).read u29) = y.1 := (e29.agrees.read (by simp [addR64M64Effect_components])).trans g28r14
  have g30r14 : ((Operand.reg 14 : Operand 64).read u30) = y.1 := (e30.agrees.read (by simp [adcR64Imm8Effect_components])).trans g29r14
  have g31r14 : ((Operand.reg 14 : Operand 64).read u31) = y.1 := (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r14
  have g32r14 : ((Operand.reg 14 : Operand 64).read u32) = y.1 := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r14
  have g33r14 : ((Operand.reg 14 : Operand 64).read u33) = y.1 := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r14
  have g34r14 : ((Operand.reg 14 : Operand 64).read u34) = y.1 := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r14
  have g35r14 : ((Operand.reg 14 : Operand 64).read u35) = y.1 := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r14
  have g36r14 : ((Operand.reg 14 : Operand 64).read u36) = y.1 := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r14
  have g37r14 : ((Operand.reg 14 : Operand 64).read u37) = y.1 := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r14
  have g38r14 : ((Operand.reg 14 : Operand 64).read u38) = y.1 := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r14
  have g39r14 : ((Operand.reg 14 : Operand 64).read u39) = y.1 := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r14
  have g40r14 : ((Operand.reg 14 : Operand 64).read u40) = y.1 := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r14
  have g41r14 : ((Operand.reg 14 : Operand 64).read u41) = y.1 := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r14
  have g32r15 : ((Operand.reg 15 : Operand 64).read u32) = w.1 := (e32.agrees.read (by simp [adcR64Imm8Effect_components])).trans g31r15
  have g33r15 : ((Operand.reg 15 : Operand 64).read u33) = w.1 := (e33.agrees.read (by simp [movR64M64Effect_components])).trans g32r15
  have g34r15 : ((Operand.reg 15 : Operand 64).read u34) = w.1 := (e34.agrees.read (by simp [movM64R64Effect_components])).trans g33r15
  have g35r15 : ((Operand.reg 15 : Operand 64).read u35) = w.1 := (e35.agrees.read (by simp [mulR64Effect_components])).trans g34r15
  have g36r15 : ((Operand.reg 15 : Operand 64).read u36) = w.1 := (e36.agrees.read (by simp [movR64R64Effect_components])).trans g35r15
  have g37r15 : ((Operand.reg 15 : Operand 64).read u37) = w.1 := (e37.agrees.read (by simp [movR64R64Effect_components])).trans g36r15
  have g38r15 : ((Operand.reg 15 : Operand 64).read u38) = w.1 := (e38.agrees.read (by simp [addR64M64Effect_components])).trans g37r15
  have g39r15 : ((Operand.reg 15 : Operand 64).read u39) = w.1 := (e39.agrees.read (by simp [adcR64Imm8Effect_components])).trans g38r15
  have g40r15 : ((Operand.reg 15 : Operand 64).read u40) = w.1 := (e40.agrees.read (by simp [addR64R64Effect_components])).trans g39r15
  have g41r15 : ((Operand.reg 15 : Operand 64).read u41) = w.1 := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r15
  have g41r11 : ((Operand.reg 11 : Operand 64).read u41) = r3.1 := (e41.agrees.read (by simp [adcR64Imm8Effect_components])).trans g40r11
  have keep16 : slot s u41 16 = slot s t 16 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 40) 8, .mem (stackPtr s - 112 + 32) 8]) t u41 := (((((((((((((((((e24.agrees.trans ag25).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans ag34).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans e39.agrees).trans e40.agrees).trans e41.agrees).mono (by simp only [movR64M64Effect_components, f24.rsp, mulR64Effect_components, movR64R64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, f33.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot16 := keep16.trans wr23_16
  have keep56 : slot s u41 56 = slot s t 56 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 40) 8, .mem (stackPtr s - 112 + 32) 8]) t u41 := (((((((((((((((((e24.agrees.trans ag25).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans ag34).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans e39.agrees).trans e40.agrees).trans e41.agrees).mono (by simp only [movR64M64Effect_components, f24.rsp, mulR64Effect_components, movR64R64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, f33.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot56 := keep56.trans wr23_56
  have keep48 : slot s u41 48 = slot s t 48 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 40) 8, .mem (stackPtr s - 112 + 32) 8]) t u41 := (((((((((((((((((e24.agrees.trans ag25).trans e26.agrees).trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans ag34).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans e39.agrees).trans e40.agrees).trans e41.agrees).mono (by simp only [movR64M64Effect_components, f24.rsp, mulR64Effect_components, movR64R64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, f33.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot48 := keep48.trans wr23_48
  have keep40 : slot s u41 40 = slot s u25 40 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 32) 8]) u25 u41 := (((((((((((((((e26.agrees.trans e27.agrees).trans e28.agrees).trans e29.agrees).trans e30.agrees).trans e31.agrees).trans e32.agrees).trans e33.agrees).trans ag34).trans e35.agrees).trans e36.agrees).trans e37.agrees).trans e38.agrees).trans e39.agrees).trans e40.agrees).trans e41.agrees).mono (by simp only [mulR64Effect_components, movR64R64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, movR64M64Effect_components, f33.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot40 := keep40.trans wr25
  have keep32 : slot s u41 32 = slot s u34 32 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ []) u34 u41 := ((((((e35.agrees.trans e36.agrees).trans e37.agrees).trans e38.agrees).trans e39.agrees).trans e40.agrees).trans e41.agrees).mono (by simp only [mulR64Effect_components, movR64R64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
  have slot32 := keep32.trans wr34
  refine ⟨u41, ⟨18, (((((((((((((((((run24.trans run25).trans run26).trans run27).trans run28).trans run29).trans run30).trans run31).trans run32).trans run33).trans run34).trans run35).trans run36).trans run37).trans run38).trans run39).trans run40).trans run41)⟩, f41, e41.rip, ⟨slot56, slot48, slot40, slot32⟩, slot16,
    g41r1, g41r6, g41r7, g41r5, g41r13, ?_⟩
  change (⟨((Operand.reg 14 : Operand 64).read u41), ((Operand.reg 15 : Operand 64).read u41), ((Operand.reg 11 : Operand 64).read u41), ((Operand.reg 3 : Operand 64).read u41)⟩ : Limbs) = _
  rw [g41r14, g41r15, g41r11, g41r3]
  rfl
end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound
