import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail.Support

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Field.Montgomery (add64 adc64 product64)

attribute [local irreducible] add64 adc64 product64

set_option exponentiation.threshold 512 in
set_option maxHeartbeats 1200000 in
theorem machine [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : First s t v)
    (hpref : (prefixEffect t).Holds t u)
    (frame : ScalarFrame.FrameState s u 32 112 112)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256))) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x11350e ∧
      ModulusSlots s w ∧ slot s w 16 = 1 ∧ slot s w 24 = s.regValue .rsi ∧
      w.regValue .rdi = s.regValue .rdi ∧ w.regValue .r10 = 0 ∧
      (⟨w.regValue .r13, w.regValue .rbp, w.regValue .rbx, w.regValue .r14,
        w.regValue .r9, (carryByte s w != 0)⟩ : Words) =
        round (t.regValue .r14) (t.regValue .r15) (t.regValue .r11) (t.regValue .rbx)
          (BitVec.ofNat 64 (v / 2^256)) (BitVec.ofNat 64 (v / 2^320)) ∧
      (carryByte s w).toNat ≤ 1 := by
  let a := t.regValue .r14
  let b := t.regValue .r15
  let c := t.regValue .r11
  let d := t.regValue .rbx
  let e := BitVec.ofNat 64 (v / 2^256)
  let f := BitVec.ofNat 64 (v / 2^320)
  let p0 := product64 a 0xffffffffffffffff
  let p1 := product64 a 0xffffffff
  let x := add64 p1.1 b
  let xh := adc64 p1.2 0 x.2
  let z := add64 p0.1 a
  let y := adc64 x.1 p0.2 z.2
  let yh := adc64 xh.1 0 y.2
  let m := add64 c yh.1
  let mh := adc64 0 0 m.2
  let p3 := product64 a 0xffffffff00000001
  let h := add64 d e
  let eh := adc64 f 0 h.2
  let q := add64 h.1 p3.1
  let qh := adc64 p3.2 0 q.2
  let w := add64 q.1 mh.1
  let wh := adc64 qh.1 0 w.2
  have f0 := frame
  have ip0 : u.RIP = 0x1134b9 := hpref.rip
  obtain ⟨g0r12, g0r5, g0r13, g0r8, cf0⟩ := prefix_values state hpref
  change (Operand.reg 12 : Operand 64).read u = a at g0r12
  change (Operand.reg 5 : Operand 64).read u = p0.2 at g0r5
  change (Operand.reg 13 : Operand 64).read u = x.1 at g0r13
  change (Operand.reg 8 : Operand 64).read u = xh.1 at g0r8
  change (StatusFlags.ofRFLAGS u.RFLAGS).CF = z.2 at cf0
  have g0r3 : ((Operand.reg 3 : Operand 64).read u) = d := by
    exact (hpref.agrees.read (by simp [prefixEffect, Effect.components])).trans (rfl)
  have g0r11 : ((Operand.reg 11 : Operand 64).read u) = c := by
    exact (hpref.agrees.read (by simp [prefixEffect, Effect.components])).trans (rfl)
  have g0r6 : ((Operand.reg 6 : Operand 64).read u) = s.regValue .rsi := by
    exact (hpref.agrees.read (by simp [prefixEffect, Effect.components])).trans state.rsi
  have g0r7 : ((Operand.reg 7 : Operand 64).read u) = s.regValue .rdi := by
    exact (hpref.agrees.read (by simp [prefixEffect, Effect.components])).trans state.rdi
  have wr0_56 : slot s u 56 = 0xffffffffffffffff :=
    (P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees hpref.agrees _
      (by simp [prefixEffect, Effect.components, Component.Covers])).trans state.slots.p0
  have wr0_48 : slot s u 48 = 0xffffffff :=
    (P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees hpref.agrees _
      (by simp [prefixEffect, Effect.components, Component.Covers])).trans state.slots.p1
  have wr0_40 : slot s u 40 = 0 :=
    (P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees hpref.agrees _
      (by simp [prefixEffect, Effect.components, Component.Covers])).trans state.slots.p2
  have wr0_32 : slot s u 32 = 0xffffffff00000001 :=
    (P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees hpref.agrees _
      (by simp [prefixEffect, Effect.components, Component.Covers])).trans state.slots.p3
  have wr0_16 : slot s u 16 = 1 :=
    (P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees hpref.agrees _
      (by simp [prefixEffect, Effect.components, Component.Covers])).trans state.inverse
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m64_r64_effect_step_any 0x1134b9 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x134b9 _ (by decide) (by decide +kernel))
      ⟨ip0, ScalarFrame.stack_writable pre.toCalleePre f0 (offset := 24) (len := 8) (by decide) (by decide) (by decide), ScalarFrame.stack_code pre.toCalleePre f0 (offset := 24) (len := 8) (codeOffset := 0x134b9) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134be (by decide)))
  change (movM64R64Effect 0x1134b9 6 (.sib 4 none 0 (.d8 24)) u).Holds u u1 at e1
  have ag1 : AgreesExcept [.mem (stackPtr u + 24) 8, .rip] u u1 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_store pre f0 ready1 (offset := 24) (len := 8) (by decide) ag1
  have wr1 : memLoad u1.external (stackPtr s - 112 + 24) 64 = s.regValue .rsi := by
    have hh := e1.writes
    change memLoad u1.external (stackPtr u + 24) 64 = ((Operand.reg 6 : Operand 64).read u) at hh
    rw [f0.rsp, g0r6] at hh
    exact hh
  have g1r6 : ((Operand.reg 6 : Operand 64).read u1) = s.regValue .rsi := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r6
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x1134be 0x4c (by simp [RexWPrefix]) 1 (.base 6 (.d8 40)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x134be _ (by decide) (by decide +kernel))
      ⟨e1.rip, by
        change MemReadable u1 (((Operand.reg 6 : Operand 64).read u1) + 40) 8
        rw [g1r6]
        exact FirstRound.input_readable pre f1 (j := 5) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134c2 (by decide)))
  change (movR64M64Effect 0x1134be 9 (.base 6 (.d8 40)) u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load2 : memLoad u1.external (((Operand.reg 6 : Operand 64).read u1) + 40) 64 = f := by
    rw [g1r6]
    exact input_limb pre f1 input 5 (by decide)
  have g2r9 : ((Operand.reg 9 : Operand 64).read u2) = f := by
    have hh := e2.writes
    change ((Operand.reg 9 : Operand 64).read u2) = memLoad u1.external (((Operand.reg 6 : Operand 64).read u1) + 40) 64 at hh
    rw [load2] at hh
    simpa only [add64, adc64, product64] using hh
  have g1r5 : ((Operand.reg 5 : Operand 64).read u1) = p0.2 := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r5
  have g2r5 : ((Operand.reg 5 : Operand 64).read u2) = p0.2 := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r5
  have g1r13 : ((Operand.reg 13 : Operand 64).read u1) = x.1 := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r13
  have g2r13 : ((Operand.reg 13 : Operand 64).read u2) = x.1 := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r13
  have cf1 : (StatusFlags.ofRFLAGS u1.RFLAGS).CF = z.2 := by
    rw [e1.agrees.rflags (by simp [movM64R64Effect_components]) (by simp [movM64R64Effect_components])]
    exact cf0
  have cf2 : (StatusFlags.ofRFLAGS u2.RFLAGS).CF = z.2 := by
    rw [e2.agrees.rflags (by simp [movR64M64Effect_components]) (by simp [movR64M64Effect_components])]
    exact cf1
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (adc_r64_r64_effect_step 0x1134c2 0x49 0xed (by simp [RexWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x134c2 _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134c5 (by decide)))
  change (adcR64R64Effect 0x1134c2 13 5 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have g3r13 : ((Operand.reg 13 : Operand 64).read u3) = y.1 := by
    have hh := e3.writes
    change ((Operand.reg 13 : Operand 64).read u3) = (adcSpec ((Operand.reg 13 : Operand 64).read u2) (((Operand.reg 5 : Operand 64).read u2)) (u2.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g2r5, g2r13, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf2] at hh
    simpa only [y, add64, adc64, product64] using hh
  have cf3 : (StatusFlags.ofRFLAGS u3.RFLAGS).CF = y.2 := by
    have hh := e3.flags.1
    change (StatusFlags.ofRFLAGS u3.RFLAGS).CF = (adcSpec ((Operand.reg 13 : Operand 64).read u2) (((Operand.reg 5 : Operand 64).read u2)) (u2.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g2r5, g2r13, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf2] at hh
    simpa only [y, add64, adc64] using hh
  have g1r8 : ((Operand.reg 8 : Operand 64).read u1) = xh.1 := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r8
  have g2r8 : ((Operand.reg 8 : Operand 64).read u2) = xh.1 := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r8
  have g3r8 : ((Operand.reg 8 : Operand 64).read u3) = xh.1 := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r8
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (adc_r64_imm8_effect_step 0x1134c5 0x49 0xd0 0 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x134c5 _ (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134c9 (by decide)))
  change (adcR64Imm8Effect 0x1134c5 8 0 u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g4r8 : ((Operand.reg 8 : Operand 64).read u4) = yh.1 := by
    have hh := e4.writes
    change ((Operand.reg 8 : Operand 64).read u4) = (adcSpec ((Operand.reg 8 : Operand 64).read u3) (0) (u3.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g3r8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf3] at hh
    simpa only [yh, add64, adc64, product64] using hh
  have cf4 : (StatusFlags.ofRFLAGS u4.RFLAGS).CF = yh.2 := by
    have hh := e4.flags.1
    change (StatusFlags.ofRFLAGS u4.RFLAGS).CF = (adcSpec ((Operand.reg 8 : Operand 64).read u3) (0) (u3.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g3r8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf3] at hh
    simpa only [yh, add64, adc64] using hh
  have g1r12 : ((Operand.reg 12 : Operand 64).read u1) = a := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r12
  have g2r12 : ((Operand.reg 12 : Operand 64).read u2) = a := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r12
  have g3r12 : ((Operand.reg 12 : Operand 64).read u3) = a := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r12
  have g4r12 : ((Operand.reg 12 : Operand 64).read u4) = a := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r12
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (mov_r64_r64_effect_step 0x1134c9 0x4c 0xe0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x134c9 _ (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134cc (by decide)))
  change (movR64R64Effect 0x1134c9 0 12 u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g5r0 : ((Operand.reg 0 : Operand 64).read u5) = a := by
    have hh := e5.writes
    change ((Operand.reg 0 : Operand 64).read u5) = ((Operand.reg 12 : Operand 64).read u4) at hh
    rw [g4r12] at hh
    simpa only [add64, adc64, product64] using hh
  have keep5_40 : memLoad u5.external (stackPtr s - 112 + 40) 64 = memLoad u.external (stackPtr s - 112 + 40) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8]) u u5 := ((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (mov_r64_m64_effect_step 0x1134cc 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x134cc _ (by decide) (by decide +kernel))
      ⟨e5.rip, ScalarFrame.stack_readable pre.toCalleePre f5 (offset := 40) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134d1 (by decide)))
  change (movR64M64Effect 0x1134cc 10 (.sib 4 none 0 (.d8 40)) u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load6 : memLoad u5.external (stackPtr u5 + 40) 64 = 0 := by
    rw [f5.rsp]
    exact keep5_40.trans wr0_40
  have g6r10 : ((Operand.reg 10 : Operand 64).read u6) = 0 := by
    have hh := e6.writes
    change ((Operand.reg 10 : Operand 64).read u6) = memLoad u5.external (stackPtr u5 + 40) 64 at hh
    rw [load6] at hh
    simpa only [add64, adc64, product64] using hh
  have g6r0 : ((Operand.reg 0 : Operand 64).read u6) = a := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r0
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (mul_r64_effect_step 0x1134d1 0x49 0xe2 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x134d1 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134d4 (by decide)))
  change (mulR64Effect 0x1134d1 10 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have g7r0 : ((Operand.reg 0 : Operand 64).read u7) = 0 := by
    have hh := e7.writes.1
    change ((Operand.reg 0 : Operand 64).read u7) = ((Operand.reg 0 : Operand 64).read u6) * ((Operand.reg 10 : Operand 64).read u6) at hh
    rw [g6r10, g6r0] at hh
    simpa [mulHigh64] using hh
  have g7r2 : ((Operand.reg 2 : Operand 64).read u7) = 0 := by
    have hh := e7.writes.2
    change ((Operand.reg 2 : Operand 64).read u7) = mulHigh64 ((Operand.reg 0 : Operand 64).read u6) ((Operand.reg 10 : Operand 64).read u6) at hh
    rw [g6r10, g6r0] at hh
    simpa [mulHigh64] using hh
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x1134d4 0x49 0xd7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x134d4 _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134d7 (by decide)))
  change (movR64R64Effect 0x1134d4 15 2 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g8r15 : ((Operand.reg 15 : Operand 64).read u8) = 0 := by
    have hh := e8.writes
    change ((Operand.reg 15 : Operand 64).read u8) = ((Operand.reg 2 : Operand 64).read u7) at hh
    rw [g7r2] at hh
    simpa only [add64, adc64, product64] using hh
  have g8r0 : ((Operand.reg 0 : Operand 64).read u8) = 0 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r0
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (mov_r64_r64_effect_step 0x1134d7 0x48 0xc5 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x134d7 _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134da (by decide)))
  change (movR64R64Effect 0x1134d7 5 0 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g9r5 : ((Operand.reg 5 : Operand 64).read u9) = 0 := by
    have hh := e9.writes
    change ((Operand.reg 5 : Operand 64).read u9) = ((Operand.reg 0 : Operand 64).read u8) at hh
    rw [g8r0] at hh
    simpa only [add64, adc64, product64] using hh
  have g1r11 : ((Operand.reg 11 : Operand 64).read u1) = c := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r11
  have g2r11 : ((Operand.reg 11 : Operand 64).read u2) = c := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r11
  have g3r11 : ((Operand.reg 11 : Operand 64).read u3) = c := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r11
  have g4r11 : ((Operand.reg 11 : Operand 64).read u4) = c := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r11
  have g5r11 : ((Operand.reg 11 : Operand 64).read u5) = c := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r11
  have g6r11 : ((Operand.reg 11 : Operand 64).read u6) = c := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r11
  have g7r11 : ((Operand.reg 11 : Operand 64).read u7) = c := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r11
  have g8r11 : ((Operand.reg 11 : Operand 64).read u8) = c := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r11
  have g9r11 : ((Operand.reg 11 : Operand 64).read u9) = c := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r11
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (add_r64_r64_effect_step 0x1134da 0x4c 0xdd (by simp [RexWPrefix]) rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x134da _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134dd (by decide)))
  change (addR64R64Effect 0x1134da 5 11 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g10r5 : ((Operand.reg 5 : Operand 64).read u10) = c := by
    have hh := e10.writes
    change ((Operand.reg 5 : Operand 64).read u10) = (addSpec ((Operand.reg 5 : Operand 64).read u9) (((Operand.reg 11 : Operand 64).read u9))).1 at hh
    rw [g9r11, g9r5] at hh
    simpa [addSpec, adcSpec] using hh
  have cf10 : (StatusFlags.ofRFLAGS u10.RFLAGS).CF = false := by
    have hh := e10.flags.1
    change (StatusFlags.ofRFLAGS u10.RFLAGS).CF = (addSpec ((Operand.reg 5 : Operand 64).read u9) (((Operand.reg 11 : Operand 64).read u9))).2.CF at hh
    rw [g9r11, g9r5] at hh
    simpa [addSpec, adcSpec] using hh
  have g9r15 : ((Operand.reg 15 : Operand 64).read u9) = 0 := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r15
  have g10r15 : ((Operand.reg 15 : Operand 64).read u10) = 0 := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r15
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (adc_r64_imm8_effect_step 0x1134dd 0x49 0xd7 0 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x134dd _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134e1 (by decide)))
  change (adcR64Imm8Effect 0x1134dd 15 0 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = 0 := by
    have hh := e11.writes
    change ((Operand.reg 15 : Operand 64).read u11) = (adcSpec ((Operand.reg 15 : Operand 64).read u10) (0) (u10.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g10r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf10] at hh
    simpa [addSpec, adcSpec] using hh
  have cf11 : (StatusFlags.ofRFLAGS u11.RFLAGS).CF = false := by
    have hh := e11.flags.1
    change (StatusFlags.ofRFLAGS u11.RFLAGS).CF = (adcSpec ((Operand.reg 15 : Operand 64).read u10) (0) (u10.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g10r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf10] at hh
    simpa [addSpec, adcSpec] using hh
  have g5r8 : ((Operand.reg 8 : Operand 64).read u5) = yh.1 := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r8
  have g6r8 : ((Operand.reg 8 : Operand 64).read u6) = yh.1 := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r8
  have g7r8 : ((Operand.reg 8 : Operand 64).read u7) = yh.1 := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r8
  have g8r8 : ((Operand.reg 8 : Operand 64).read u8) = yh.1 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r8
  have g9r8 : ((Operand.reg 8 : Operand 64).read u9) = yh.1 := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r8
  have g10r8 : ((Operand.reg 8 : Operand 64).read u10) = yh.1 := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r8
  have g11r8 : ((Operand.reg 8 : Operand 64).read u11) = yh.1 := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r8
  have g11r5 : ((Operand.reg 5 : Operand 64).read u11) = c := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r5
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (add_r64_r64_effect_step 0x1134e1 0x4c 0xc5 (by simp [RexWPrefix]) rfl).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x134e1 _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134e4 (by decide)))
  change (addR64R64Effect 0x1134e1 5 8 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g12r5 : ((Operand.reg 5 : Operand 64).read u12) = m.1 := by
    have hh := e12.writes
    change ((Operand.reg 5 : Operand 64).read u12) = (addSpec ((Operand.reg 5 : Operand 64).read u11) (((Operand.reg 8 : Operand 64).read u11))).1 at hh
    rw [g11r8, g11r5] at hh
    simpa only [m, add64, adc64, product64] using hh
  have cf12 : (StatusFlags.ofRFLAGS u12.RFLAGS).CF = m.2 := by
    have hh := e12.flags.1
    change (StatusFlags.ofRFLAGS u12.RFLAGS).CF = (addSpec ((Operand.reg 5 : Operand 64).read u11) (((Operand.reg 8 : Operand 64).read u11))).2.CF at hh
    rw [g11r8, g11r5] at hh
    simpa only [m, add64, adc64] using hh
  have g12r15 : ((Operand.reg 15 : Operand 64).read u12) = 0 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r15
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (adc_r64_imm8_effect_step 0x1134e4 0x49 0xd7 0 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x134e4 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134e8 (by decide)))
  change (adcR64Imm8Effect 0x1134e4 15 0 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g13r15 : ((Operand.reg 15 : Operand 64).read u13) = mh.1 := by
    have hh := e13.writes
    change ((Operand.reg 15 : Operand 64).read u13) = (adcSpec ((Operand.reg 15 : Operand 64).read u12) (0) (u12.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g12r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf12] at hh
    simpa only [mh, add64, adc64, product64] using hh
  have cf13 : (StatusFlags.ofRFLAGS u13.RFLAGS).CF = mh.2 := by
    have hh := e13.flags.1
    change (StatusFlags.ofRFLAGS u13.RFLAGS).CF = (adcSpec ((Operand.reg 15 : Operand 64).read u12) (0) (u12.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g12r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf12] at hh
    simpa only [mh, add64, adc64] using hh
  have g5r12 : ((Operand.reg 12 : Operand 64).read u5) = a := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r12
  have g6r12 : ((Operand.reg 12 : Operand 64).read u6) = a := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r12
  have g7r12 : ((Operand.reg 12 : Operand 64).read u7) = a := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r12
  have g8r12 : ((Operand.reg 12 : Operand 64).read u8) = a := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r12
  have g9r12 : ((Operand.reg 12 : Operand 64).read u9) = a := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r12
  have g10r12 : ((Operand.reg 12 : Operand 64).read u10) = a := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r12
  have g11r12 : ((Operand.reg 12 : Operand 64).read u11) = a := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r12
  have g12r12 : ((Operand.reg 12 : Operand 64).read u12) = a := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r12
  have g13r12 : ((Operand.reg 12 : Operand 64).read u13) = a := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r12
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (mov_r64_r64_effect_step 0x1134e8 0x4c 0xe0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x134e8 _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134eb (by decide)))
  change (movR64R64Effect 0x1134e8 0 12 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g14r0 : ((Operand.reg 0 : Operand 64).read u14) = a := by
    have hh := e14.writes
    change ((Operand.reg 0 : Operand 64).read u14) = ((Operand.reg 12 : Operand 64).read u13) at hh
    rw [g13r12] at hh
    simpa only [add64, adc64, product64] using hh
  have keep14_32 : memLoad u14.external (stackPtr s - 112 + 32) 64 = memLoad u.external (stackPtr s - 112 + 32) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8]) u u14 := (((((((((((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (mul_m64_effect_step 0x1134eb 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x134eb _ (by decide) (by decide +kernel))
      ⟨e14.rip, ScalarFrame.stack_readable pre.toCalleePre f14 (offset := 32) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134f0 (by decide)))
  change (mulM64Effect 0x1134eb (.sib 4 none 0 (.d8 32)) u14).Holds u14 u15 at e15
  have f15 := f14.after_registers ready15 e15.agrees (by simp [mulM64Effect_components, Component.Covers]) (by simp [mulM64Effect_components])
  have load15 : memLoad u14.external (stackPtr u14 + 32) 64 = 0xffffffff00000001 := by
    rw [f14.rsp]
    exact keep14_32.trans wr0_32
  have g15r0 : ((Operand.reg 0 : Operand 64).read u15) = p3.1 := by
    have hh := e15.writes.1
    change ((Operand.reg 0 : Operand 64).read u15) = ((Operand.reg 0 : Operand 64).read u14) * (memLoad u14.external (stackPtr u14 + 32) 64) at hh
    rw [load15, g14r0] at hh
    simpa only [p3, add64, adc64, product64] using hh
  have g15r2 : ((Operand.reg 2 : Operand 64).read u15) = p3.2 := by
    have hh := e15.writes.2
    change ((Operand.reg 2 : Operand 64).read u15) = mulHigh64 ((Operand.reg 0 : Operand 64).read u14) (memLoad u14.external (stackPtr u14 + 32) 64) at hh
    rw [load15, g14r0] at hh
    simpa only [p3, add64, adc64, product64] using hh
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (mov_r64_r64_effect_step 0x1134f0 0x49 0xd6 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x134f0 _ (by decide) (by decide +kernel))
      e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134f3 (by decide)))
  change (movR64R64Effect 0x1134f0 14 2 u15).Holds u15 u16 at e16
  have f16 := f15.after_registers ready16 e16.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g16r14 : ((Operand.reg 14 : Operand 64).read u16) = p3.2 := by
    have hh := e16.writes
    change ((Operand.reg 14 : Operand 64).read u16) = ((Operand.reg 2 : Operand 64).read u15) at hh
    rw [g15r2] at hh
    simpa only [p3, add64, adc64, product64] using hh
  have g2r6 : ((Operand.reg 6 : Operand 64).read u2) = s.regValue .rsi := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r6
  have g3r6 : ((Operand.reg 6 : Operand 64).read u3) = s.regValue .rsi := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r6
  have g4r6 : ((Operand.reg 6 : Operand 64).read u4) = s.regValue .rsi := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r6
  have g5r6 : ((Operand.reg 6 : Operand 64).read u5) = s.regValue .rsi := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r6
  have g6r6 : ((Operand.reg 6 : Operand 64).read u6) = s.regValue .rsi := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r6
  have g7r6 : ((Operand.reg 6 : Operand 64).read u7) = s.regValue .rsi := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r6
  have g8r6 : ((Operand.reg 6 : Operand 64).read u8) = s.regValue .rsi := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r6
  have g9r6 : ((Operand.reg 6 : Operand 64).read u9) = s.regValue .rsi := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r6
  have g10r6 : ((Operand.reg 6 : Operand 64).read u10) = s.regValue .rsi := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r6
  have g11r6 : ((Operand.reg 6 : Operand 64).read u11) = s.regValue .rsi := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r6
  have g12r6 : ((Operand.reg 6 : Operand 64).read u12) = s.regValue .rsi := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r6
  have g13r6 : ((Operand.reg 6 : Operand 64).read u13) = s.regValue .rsi := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r6
  have g14r6 : ((Operand.reg 6 : Operand 64).read u14) = s.regValue .rsi := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r6
  have g15r6 : ((Operand.reg 6 : Operand 64).read u15) = s.regValue .rsi := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r6
  have g16r6 : ((Operand.reg 6 : Operand 64).read u16) = s.regValue .rsi := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r6
  have g1r3 : ((Operand.reg 3 : Operand 64).read u1) = d := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r3
  have g2r3 : ((Operand.reg 3 : Operand 64).read u2) = d := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r3
  have g3r3 : ((Operand.reg 3 : Operand 64).read u3) = d := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r3
  have g4r3 : ((Operand.reg 3 : Operand 64).read u4) = d := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r3
  have g5r3 : ((Operand.reg 3 : Operand 64).read u5) = d := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r3
  have g6r3 : ((Operand.reg 3 : Operand 64).read u6) = d := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r3
  have g7r3 : ((Operand.reg 3 : Operand 64).read u7) = d := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r3
  have g8r3 : ((Operand.reg 3 : Operand 64).read u8) = d := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r3
  have g9r3 : ((Operand.reg 3 : Operand 64).read u9) = d := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r3
  have g10r3 : ((Operand.reg 3 : Operand 64).read u10) = d := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r3
  have g11r3 : ((Operand.reg 3 : Operand 64).read u11) = d := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r3
  have g12r3 : ((Operand.reg 3 : Operand 64).read u12) = d := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r3
  have g13r3 : ((Operand.reg 3 : Operand 64).read u13) = d := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r3
  have g14r3 : ((Operand.reg 3 : Operand 64).read u14) = d := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r3
  have g15r3 : ((Operand.reg 3 : Operand 64).read u15) = d := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r3
  have g16r3 : ((Operand.reg 3 : Operand 64).read u16) = d := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r3
  obtain ⟨u17, run17, ready17, e17⟩ :=
    (add_r64_m64_effect_step 0x1134f3 0x48 (by simp [RexWPrefix]) 3 (.base 6 (.d8 32)) (by decide) rfl rfl).advances (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x134f3 _ (by decide) (by decide +kernel))
      ⟨e16.rip, by
        change MemReadable u16 (((Operand.reg 6 : Operand 64).read u16) + 32) 8
        rw [g16r6]
        exact FirstRound.input_readable pre f16 (j := 4) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134f7 (by decide)))
  change (addR64M64Effect 0x1134f3 3 (.base 6 (.d8 32)) u16).Holds u16 u17 at e17
  have f17 := f16.after_registers ready17 e17.agrees (by simp [addR64M64Effect_components, Component.Covers]) (by simp [addR64M64Effect_components])
  have load17 : memLoad u16.external (((Operand.reg 6 : Operand 64).read u16) + 32) 64 = e := by
    rw [g16r6]
    exact input_limb pre f16 input 4 (by decide)
  have g17r3 : ((Operand.reg 3 : Operand 64).read u17) = h.1 := by
    have hh := e17.writes
    change ((Operand.reg 3 : Operand 64).read u17) = (addSpec ((Operand.reg 3 : Operand 64).read u16) (memLoad u16.external (((Operand.reg 6 : Operand 64).read u16) + 32) 64)).1 at hh
    rw [load17, g16r3] at hh
    simpa only [h, add64, adc64, product64] using hh
  have cf17 : (StatusFlags.ofRFLAGS u17.RFLAGS).CF = h.2 := by
    have hh := e17.flags.1
    change (StatusFlags.ofRFLAGS u17.RFLAGS).CF = (addSpec ((Operand.reg 3 : Operand 64).read u16) (memLoad u16.external (((Operand.reg 6 : Operand 64).read u16) + 32) 64)).2.CF at hh
    rw [load17, g16r3] at hh
    simpa only [h, add64, adc64] using hh
  have g3r9 : ((Operand.reg 9 : Operand 64).read u3) = f := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r9
  have g4r9 : ((Operand.reg 9 : Operand 64).read u4) = f := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r9
  have g5r9 : ((Operand.reg 9 : Operand 64).read u5) = f := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r9
  have g6r9 : ((Operand.reg 9 : Operand 64).read u6) = f := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r9
  have g7r9 : ((Operand.reg 9 : Operand 64).read u7) = f := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r9
  have g8r9 : ((Operand.reg 9 : Operand 64).read u8) = f := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r9
  have g9r9 : ((Operand.reg 9 : Operand 64).read u9) = f := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r9
  have g10r9 : ((Operand.reg 9 : Operand 64).read u10) = f := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r9
  have g11r9 : ((Operand.reg 9 : Operand 64).read u11) = f := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r9
  have g12r9 : ((Operand.reg 9 : Operand 64).read u12) = f := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r9
  have g13r9 : ((Operand.reg 9 : Operand 64).read u13) = f := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r9
  have g14r9 : ((Operand.reg 9 : Operand 64).read u14) = f := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r9
  have g15r9 : ((Operand.reg 9 : Operand 64).read u15) = f := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r9
  have g16r9 : ((Operand.reg 9 : Operand 64).read u16) = f := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r9
  have g17r9 : ((Operand.reg 9 : Operand 64).read u17) = f := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r9
  obtain ⟨u18, run18, ready18, e18⟩ :=
    (adc_r64_imm8_effect_step 0x1134f7 0x49 0xd1 0 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f17.machine f17.bindingsSupported)
      (programText_slice (programLoaded_codeIn f17.loaded) 0x134f7 _ (by decide) (by decide +kernel))
      e17.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x134fb (by decide)))
  change (adcR64Imm8Effect 0x1134f7 9 0 u17).Holds u17 u18 at e18
  have f18 := f17.after_registers ready18 e18.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g18r9 : ((Operand.reg 9 : Operand 64).read u18) = eh.1 := by
    have hh := e18.writes
    change ((Operand.reg 9 : Operand 64).read u18) = (adcSpec ((Operand.reg 9 : Operand 64).read u17) (0) (u17.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g17r9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf17] at hh
    simpa only [eh, add64, adc64, product64] using hh
  have cf18 : (StatusFlags.ofRFLAGS u18.RFLAGS).CF = eh.2 := by
    have hh := e18.flags.1
    change (StatusFlags.ofRFLAGS u18.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read u17) (0) (u17.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g17r9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf17] at hh
    simpa only [eh, add64, adc64] using hh
  obtain ⟨u19, run19, ready19, e19⟩ :=
    (setcc_m8_effect_step 0x1134fb 0x92 (.inl rfl) 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl).advances (readyToStep f18.machine f18.bindingsSupported)
      (programText_slice (programLoaded_codeIn f18.loaded) 0x134fb _ (by decide) (by decide +kernel))
      ⟨e18.rip, byte_writable pre f18, ScalarFrame.stack_code pre.toCalleePre f18 (offset := 7) (len := 1) (codeOffset := 0x134fb) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13500 (by decide)))
  change (setccM8Effect 0x1134fb 5 (.sib 4 none 0 (.d8 7)) 2 u18).Holds u18 u19 at e19
  have ag19 : AgreesExcept [.mem (stackPtr u18 + 7) 1, .rip] u18 u19 := by
    simpa [setccM8Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e19.agrees
  have f19 := after_store pre f18 ready19 (offset := 7) (len := 1) (by decide) ag19
  have wr19 : memLoad u19.external (stackPtr s - 112 + 7) 8 = (if eh.2 then (1 : BitVec 8) else 0) := by
    have hh := e19.writes
    change memLoad u19.external (stackPtr u18 + 7) 8 = (if (StatusFlags.ofRFLAGS u18.RFLAGS).CF then (1 : BitVec 8) else 0) at hh
    rw [f18.rsp, cf18] at hh
    exact hh
  have g16r0 : ((Operand.reg 0 : Operand 64).read u16) = p3.1 := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r0
  have g17r0 : ((Operand.reg 0 : Operand 64).read u17) = p3.1 := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r0
  have g18r0 : ((Operand.reg 0 : Operand 64).read u18) = p3.1 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r0
  have g19r0 : ((Operand.reg 0 : Operand 64).read u19) = p3.1 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r0
  have g18r3 : ((Operand.reg 3 : Operand 64).read u18) = h.1 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r3
  have g19r3 : ((Operand.reg 3 : Operand 64).read u19) = h.1 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r3
  obtain ⟨u20, run20, ready20, e20⟩ :=
    (add_r64_r64_effect_step 0x113500 0x48 0xc3 (by simp [RexWPrefix]) rfl).advances (readyToStep f19.machine f19.bindingsSupported)
      (programText_slice (programLoaded_codeIn f19.loaded) 0x13500 _ (by decide) (by decide +kernel))
      e19.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13503 (by decide)))
  change (addR64R64Effect 0x113500 3 0 u19).Holds u19 u20 at e20
  have f20 := f19.after_registers ready20 e20.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g20r3 : ((Operand.reg 3 : Operand 64).read u20) = q.1 := by
    have hh := e20.writes
    change ((Operand.reg 3 : Operand 64).read u20) = (addSpec ((Operand.reg 3 : Operand 64).read u19) (((Operand.reg 0 : Operand 64).read u19))).1 at hh
    rw [g19r0, g19r3] at hh
    simpa only [q, add64, adc64, product64] using hh
  have cf20 : (StatusFlags.ofRFLAGS u20.RFLAGS).CF = q.2 := by
    have hh := e20.flags.1
    change (StatusFlags.ofRFLAGS u20.RFLAGS).CF = (addSpec ((Operand.reg 3 : Operand 64).read u19) (((Operand.reg 0 : Operand 64).read u19))).2.CF at hh
    rw [g19r0, g19r3] at hh
    simpa only [q, add64, adc64] using hh
  have g17r14 : ((Operand.reg 14 : Operand 64).read u17) = p3.2 := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r14
  have g18r14 : ((Operand.reg 14 : Operand 64).read u18) = p3.2 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r14
  have g19r14 : ((Operand.reg 14 : Operand 64).read u19) = p3.2 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r14
  have g20r14 : ((Operand.reg 14 : Operand 64).read u20) = p3.2 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r14
  obtain ⟨u21, run21, ready21, e21⟩ :=
    (adc_r64_imm8_effect_step 0x113503 0x49 0xd6 0 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f20.machine f20.bindingsSupported)
      (programText_slice (programLoaded_codeIn f20.loaded) 0x13503 _ (by decide) (by decide +kernel))
      e20.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13507 (by decide)))
  change (adcR64Imm8Effect 0x113503 14 0 u20).Holds u20 u21 at e21
  have f21 := f20.after_registers ready21 e21.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g21r14 : ((Operand.reg 14 : Operand 64).read u21) = qh.1 := by
    have hh := e21.writes
    change ((Operand.reg 14 : Operand 64).read u21) = (adcSpec ((Operand.reg 14 : Operand 64).read u20) (0) (u20.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g20r14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf20] at hh
    simpa only [qh, add64, adc64, product64] using hh
  have cf21 : (StatusFlags.ofRFLAGS u21.RFLAGS).CF = qh.2 := by
    have hh := e21.flags.1
    change (StatusFlags.ofRFLAGS u21.RFLAGS).CF = (adcSpec ((Operand.reg 14 : Operand 64).read u20) (0) (u20.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g20r14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf20] at hh
    simpa only [qh, add64, adc64] using hh
  have g14r15 : ((Operand.reg 15 : Operand 64).read u14) = mh.1 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r15
  have g15r15 : ((Operand.reg 15 : Operand 64).read u15) = mh.1 := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r15
  have g16r15 : ((Operand.reg 15 : Operand 64).read u16) = mh.1 := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r15
  have g17r15 : ((Operand.reg 15 : Operand 64).read u17) = mh.1 := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r15
  have g18r15 : ((Operand.reg 15 : Operand 64).read u18) = mh.1 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r15
  have g19r15 : ((Operand.reg 15 : Operand 64).read u19) = mh.1 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r15
  have g20r15 : ((Operand.reg 15 : Operand 64).read u20) = mh.1 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r15
  have g21r15 : ((Operand.reg 15 : Operand 64).read u21) = mh.1 := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r15
  have g21r3 : ((Operand.reg 3 : Operand 64).read u21) = q.1 := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r3
  obtain ⟨u22, run22, ready22, e22⟩ :=
    (add_r64_r64_effect_step 0x113507 0x4c 0xfb (by simp [RexWPrefix]) rfl).advances (readyToStep f21.machine f21.bindingsSupported)
      (programText_slice (programLoaded_codeIn f21.loaded) 0x13507 _ (by decide) (by decide +kernel))
      e21.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1350a (by decide)))
  change (addR64R64Effect 0x113507 3 15 u21).Holds u21 u22 at e22
  have f22 := f21.after_registers ready22 e22.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g22r3 : ((Operand.reg 3 : Operand 64).read u22) = w.1 := by
    have hh := e22.writes
    change ((Operand.reg 3 : Operand 64).read u22) = (addSpec ((Operand.reg 3 : Operand 64).read u21) (((Operand.reg 15 : Operand 64).read u21))).1 at hh
    rw [g21r15, g21r3] at hh
    simpa only [w, add64, adc64, product64] using hh
  have cf22 : (StatusFlags.ofRFLAGS u22.RFLAGS).CF = w.2 := by
    have hh := e22.flags.1
    change (StatusFlags.ofRFLAGS u22.RFLAGS).CF = (addSpec ((Operand.reg 3 : Operand 64).read u21) (((Operand.reg 15 : Operand 64).read u21))).2.CF at hh
    rw [g21r15, g21r3] at hh
    simpa only [w, add64, adc64] using hh
  have g22r14 : ((Operand.reg 14 : Operand 64).read u22) = qh.1 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r14
  obtain ⟨u23, run23, ready23, e23⟩ :=
    (adc_r64_imm8_effect_step 0x11350a 0x49 0xd6 0 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f22.machine f22.bindingsSupported)
      (programText_slice (programLoaded_codeIn f22.loaded) 0x1350a _ (by decide) (by decide +kernel))
      e22.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1350e (by decide)))
  change (adcR64Imm8Effect 0x11350a 14 0 u22).Holds u22 u23 at e23
  have f23 := f22.after_registers ready23 e23.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g23r14 : ((Operand.reg 14 : Operand 64).read u23) = wh.1 := by
    have hh := e23.writes
    change ((Operand.reg 14 : Operand 64).read u23) = (adcSpec ((Operand.reg 14 : Operand 64).read u22) (0) (u22.RFLAGS.extractLsb' 0 1)).1 at hh
    rw [g22r14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf22] at hh
    simpa only [wh, add64, adc64, product64] using hh
  have cf23 : (StatusFlags.ofRFLAGS u23.RFLAGS).CF = wh.2 := by
    have hh := e23.flags.1
    change (StatusFlags.ofRFLAGS u23.RFLAGS).CF = (adcSpec ((Operand.reg 14 : Operand 64).read u22) (0) (u22.RFLAGS.extractLsb' 0 1)).2.CF at hh
    rw [g22r14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf22] at hh
    simpa only [wh, add64, adc64] using hh
  have g1r7 : ((Operand.reg 7 : Operand 64).read u1) = s.regValue .rdi := (e1.agrees.read (by simp [movM64R64Effect_components])).trans g0r7
  have g2r7 : ((Operand.reg 7 : Operand 64).read u2) = s.regValue .rdi := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r7
  have g3r7 : ((Operand.reg 7 : Operand 64).read u3) = s.regValue .rdi := (e3.agrees.read (by simp [adcR64R64Effect_components])).trans g2r7
  have g4r7 : ((Operand.reg 7 : Operand 64).read u4) = s.regValue .rdi := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r7
  have g5r7 : ((Operand.reg 7 : Operand 64).read u5) = s.regValue .rdi := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r7
  have g6r7 : ((Operand.reg 7 : Operand 64).read u6) = s.regValue .rdi := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r7
  have g7r7 : ((Operand.reg 7 : Operand 64).read u7) = s.regValue .rdi := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r7
  have g8r7 : ((Operand.reg 7 : Operand 64).read u8) = s.regValue .rdi := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r7
  have g9r7 : ((Operand.reg 7 : Operand 64).read u9) = s.regValue .rdi := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r7
  have g10r7 : ((Operand.reg 7 : Operand 64).read u10) = s.regValue .rdi := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r7
  have g11r7 : ((Operand.reg 7 : Operand 64).read u11) = s.regValue .rdi := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r7
  have g12r7 : ((Operand.reg 7 : Operand 64).read u12) = s.regValue .rdi := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r7
  have g13r7 : ((Operand.reg 7 : Operand 64).read u13) = s.regValue .rdi := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r7
  have g14r7 : ((Operand.reg 7 : Operand 64).read u14) = s.regValue .rdi := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r7
  have g15r7 : ((Operand.reg 7 : Operand 64).read u15) = s.regValue .rdi := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r7
  have g16r7 : ((Operand.reg 7 : Operand 64).read u16) = s.regValue .rdi := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r7
  have g17r7 : ((Operand.reg 7 : Operand 64).read u17) = s.regValue .rdi := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r7
  have g18r7 : ((Operand.reg 7 : Operand 64).read u18) = s.regValue .rdi := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r7
  have g19r7 : ((Operand.reg 7 : Operand 64).read u19) = s.regValue .rdi := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r7
  have g20r7 : ((Operand.reg 7 : Operand 64).read u20) = s.regValue .rdi := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r7
  have g21r7 : ((Operand.reg 7 : Operand 64).read u21) = s.regValue .rdi := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r7
  have g22r7 : ((Operand.reg 7 : Operand 64).read u22) = s.regValue .rdi := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r7
  have g23r7 : ((Operand.reg 7 : Operand 64).read u23) = s.regValue .rdi := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r7
  have g7r10 : ((Operand.reg 10 : Operand 64).read u7) = 0 := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r10
  have g8r10 : ((Operand.reg 10 : Operand 64).read u8) = 0 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r10
  have g9r10 : ((Operand.reg 10 : Operand 64).read u9) = 0 := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r10
  have g10r10 : ((Operand.reg 10 : Operand 64).read u10) = 0 := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r10
  have g11r10 : ((Operand.reg 10 : Operand 64).read u11) = 0 := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r10
  have g12r10 : ((Operand.reg 10 : Operand 64).read u12) = 0 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r10
  have g13r10 : ((Operand.reg 10 : Operand 64).read u13) = 0 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r10
  have g14r10 : ((Operand.reg 10 : Operand 64).read u14) = 0 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r10
  have g15r10 : ((Operand.reg 10 : Operand 64).read u15) = 0 := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r10
  have g16r10 : ((Operand.reg 10 : Operand 64).read u16) = 0 := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r10
  have g17r10 : ((Operand.reg 10 : Operand 64).read u17) = 0 := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r10
  have g18r10 : ((Operand.reg 10 : Operand 64).read u18) = 0 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r10
  have g19r10 : ((Operand.reg 10 : Operand 64).read u19) = 0 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r10
  have g20r10 : ((Operand.reg 10 : Operand 64).read u20) = 0 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r10
  have g21r10 : ((Operand.reg 10 : Operand 64).read u21) = 0 := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r10
  have g22r10 : ((Operand.reg 10 : Operand 64).read u22) = 0 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r10
  have g23r10 : ((Operand.reg 10 : Operand 64).read u23) = 0 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r10
  have g4r13 : ((Operand.reg 13 : Operand 64).read u4) = y.1 := (e4.agrees.read (by simp [adcR64Imm8Effect_components])).trans g3r13
  have g5r13 : ((Operand.reg 13 : Operand 64).read u5) = y.1 := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r13
  have g6r13 : ((Operand.reg 13 : Operand 64).read u6) = y.1 := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r13
  have g7r13 : ((Operand.reg 13 : Operand 64).read u7) = y.1 := (e7.agrees.read (by simp [mulR64Effect_components])).trans g6r13
  have g8r13 : ((Operand.reg 13 : Operand 64).read u8) = y.1 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r13
  have g9r13 : ((Operand.reg 13 : Operand 64).read u9) = y.1 := (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r13
  have g10r13 : ((Operand.reg 13 : Operand 64).read u10) = y.1 := (e10.agrees.read (by simp [addR64R64Effect_components])).trans g9r13
  have g11r13 : ((Operand.reg 13 : Operand 64).read u11) = y.1 := (e11.agrees.read (by simp [adcR64Imm8Effect_components])).trans g10r13
  have g12r13 : ((Operand.reg 13 : Operand 64).read u12) = y.1 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r13
  have g13r13 : ((Operand.reg 13 : Operand 64).read u13) = y.1 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r13
  have g14r13 : ((Operand.reg 13 : Operand 64).read u14) = y.1 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r13
  have g15r13 : ((Operand.reg 13 : Operand 64).read u15) = y.1 := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r13
  have g16r13 : ((Operand.reg 13 : Operand 64).read u16) = y.1 := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r13
  have g17r13 : ((Operand.reg 13 : Operand 64).read u17) = y.1 := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r13
  have g18r13 : ((Operand.reg 13 : Operand 64).read u18) = y.1 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r13
  have g19r13 : ((Operand.reg 13 : Operand 64).read u19) = y.1 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r13
  have g20r13 : ((Operand.reg 13 : Operand 64).read u20) = y.1 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r13
  have g21r13 : ((Operand.reg 13 : Operand 64).read u21) = y.1 := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r13
  have g22r13 : ((Operand.reg 13 : Operand 64).read u22) = y.1 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r13
  have g23r13 : ((Operand.reg 13 : Operand 64).read u23) = y.1 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r13
  have g13r5 : ((Operand.reg 5 : Operand 64).read u13) = m.1 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r5
  have g14r5 : ((Operand.reg 5 : Operand 64).read u14) = m.1 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r5
  have g15r5 : ((Operand.reg 5 : Operand 64).read u15) = m.1 := (e15.agrees.read (by simp [mulM64Effect_components])).trans g14r5
  have g16r5 : ((Operand.reg 5 : Operand 64).read u16) = m.1 := (e16.agrees.read (by simp [movR64R64Effect_components])).trans g15r5
  have g17r5 : ((Operand.reg 5 : Operand 64).read u17) = m.1 := (e17.agrees.read (by simp [addR64M64Effect_components])).trans g16r5
  have g18r5 : ((Operand.reg 5 : Operand 64).read u18) = m.1 := (e18.agrees.read (by simp [adcR64Imm8Effect_components])).trans g17r5
  have g19r5 : ((Operand.reg 5 : Operand 64).read u19) = m.1 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r5
  have g20r5 : ((Operand.reg 5 : Operand 64).read u20) = m.1 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r5
  have g21r5 : ((Operand.reg 5 : Operand 64).read u21) = m.1 := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r5
  have g22r5 : ((Operand.reg 5 : Operand 64).read u22) = m.1 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r5
  have g23r5 : ((Operand.reg 5 : Operand 64).read u23) = m.1 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r5
  have g23r3 : ((Operand.reg 3 : Operand 64).read u23) = w.1 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r3
  have g19r9 : ((Operand.reg 9 : Operand 64).read u19) = eh.1 := (e19.agrees.read (by simp [setccM8Effect_components])).trans g18r9
  have g20r9 : ((Operand.reg 9 : Operand 64).read u20) = eh.1 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r9
  have g21r9 : ((Operand.reg 9 : Operand 64).read u21) = eh.1 := (e21.agrees.read (by simp [adcR64Imm8Effect_components])).trans g20r9
  have g22r9 : ((Operand.reg 9 : Operand 64).read u22) = eh.1 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r9
  have g23r9 : ((Operand.reg 9 : Operand 64).read u23) = eh.1 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r9
  have keep23_56 : memLoad u23.external (stackPtr s - 112 + 56) 64 = memLoad u.external (stackPtr s - 112 + 56) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8, .mem (stackPtr s - 112 + 7) 1]) u u23 := ((((((((((((((((((((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans ag19).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components, mulM64Effect_components, addR64M64Effect_components, f18.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot56 := keep23_56.trans wr0_56
  have keep23_48 : memLoad u23.external (stackPtr s - 112 + 48) 64 = memLoad u.external (stackPtr s - 112 + 48) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8, .mem (stackPtr s - 112 + 7) 1]) u u23 := ((((((((((((((((((((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans ag19).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components, mulM64Effect_components, addR64M64Effect_components, f18.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot48 := keep23_48.trans wr0_48
  have keep23_40 : memLoad u23.external (stackPtr s - 112 + 40) 64 = memLoad u.external (stackPtr s - 112 + 40) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8, .mem (stackPtr s - 112 + 7) 1]) u u23 := ((((((((((((((((((((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans ag19).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components, mulM64Effect_components, addR64M64Effect_components, f18.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot40 := keep23_40.trans wr0_40
  have keep23_32 : memLoad u23.external (stackPtr s - 112 + 32) 64 = memLoad u.external (stackPtr s - 112 + 32) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8, .mem (stackPtr s - 112 + 7) 1]) u u23 := ((((((((((((((((((((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans ag19).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components, mulM64Effect_components, addR64M64Effect_components, f18.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot32 := keep23_32.trans wr0_32
  have keep23_16 : memLoad u23.external (stackPtr s - 112 + 16) 64 = memLoad u.external (stackPtr s - 112 + 16) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 24) 8, .mem (stackPtr s - 112 + 7) 1]) u u23 := ((((((((((((((((((((((ag1.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans ag19).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [f0.rsp, movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components, mulM64Effect_components, addR64M64Effect_components, f18.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot16 := keep23_16.trans wr0_16
  have keep23_24 : memLoad u23.external (stackPtr s - 112 + 24) 64 = memLoad u1.external (stackPtr s - 112 + 24) 64 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 7) 1]) u1 u23 := (((((((((((((((((((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans ag19).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [movR64M64Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64R64Effect_components, mulM64Effect_components, addR64M64Effect_components, f18.rsp]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot24 := keep23_24.trans wr1
  have keep23_7 : memLoad u23.external (stackPtr s - 112 + 7) 8 = memLoad u19.external (stackPtr s - 112 + 7) 8 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ []) u19 u23 := (((e20.agrees.trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [addR64R64Effect_components, adcR64Imm8Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi cc hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
  have slot7 := keep23_7.trans wr19
  refine ⟨u23, ⟨23, ((((((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20).trans run21).trans run22).trans run23)⟩, f23, e23.rip, ⟨slot56, slot48, slot40, slot32⟩, slot16, slot24, g23r7, g23r10, ?_, ?_⟩
  · have carry23 : carryByte s u23 = (if eh.2 then (1 : BitVec 8) else 0) := slot7
    change (⟨((Operand.reg 13 : Operand 64).read u23), ((Operand.reg 5 : Operand 64).read u23), ((Operand.reg 3 : Operand 64).read u23), ((Operand.reg 14 : Operand 64).read u23), ((Operand.reg 9 : Operand 64).read u23), (carryByte s u23 != 0)⟩ : Words) = _
    rw [g23r13, g23r5, g23r3, g23r14, g23r9, carry23]
    change Words.mk y.1 m.1 w.1 wh.1 eh.1 ((if eh.2 then (1 : BitVec 8) else 0) != 0) =
      Words.mk y.1 m.1 w.1 wh.1 eh.1 eh.2
    congr 1
    cases eh.2 <;> rfl
  · change (memLoad _ _ 8).toNat ≤ 1
    rw [slot7]
    cases eh.2 <;> decide
end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail
