import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Support
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Field.Montgomery (add64 adc64 product64)

structure Prefix [Bindings] (s t : RamState) (v : Nat) : Prop where
  frame : ScalarFrame.FrameState s t 32 112 112
  rip : t.RIP = 0x11344e
  inverse : slot s t 16 = 1
  modulus0 : slot s t 56 = 0xffffffffffffffff
  modulus1 : slot s t 48 = 0xffffffff
  rcx : t.regValue .rcx = 1
  rsi : t.regValue .rsi = s.regValue .rsi
  rdi : t.regValue .rdi = s.regValue .rdi
  rbp : t.regValue .rbp = 0xffffffffffffffff
  r13 : t.regValue .r13 = 0xffffffff
  r10 : t.regValue .r10 = s.regValue .rdx
  r9 : t.regValue .r9 = (inputWords v).l0
  r14 : t.regValue .r14 = (lowWords (inputWords v)).1
  rbx : t.regValue .rbx = (lowWords (inputWords v)).2

attribute [local irreducible] add64 adc64 product64

set_option maxHeartbeats 800000 in
theorem lower [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (entry : Entry s t boundary)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256))) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ Prefix s u v := by
  let a := inputWords v
  let p0 := product64 0xffffffffffffffff a.l0
  let p1 := product64 0xffffffff a.l0
  let x := add64 p1.1 a.l1
  let hi1 := adc64 p1.2 0 x.2
  let z := add64 p0.1 a.l0
  let y := adc64 x.1 p0.2 z.2
  let k := adc64 hi1.1 0 y.2
  have f0 := entry.state
  have ip0 := entry.rip
  have g0r1 : ((Operand.reg 1 : Operand 64).read t) = 1 :=
    (entry.agrees.read (by simp [saveFrame])).trans pre.inverse
  have g0r2 : ((Operand.reg 2 : Operand 64).read t) = s.regValue .rdx :=
    (entry.agrees.read (by simp [saveFrame])).trans (rfl)
  have g0r6 : ((Operand.reg 6 : Operand 64).read t) = s.regValue .rsi :=
    (entry.agrees.read (by simp [saveFrame])).trans (rfl)
  have g0r7 : ((Operand.reg 7 : Operand 64).read t) = s.regValue .rdi :=
    (entry.agrees.read (by simp [saveFrame])).trans (rfl)
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x1133fe 0x49 0xd2 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x133fe _ (by decide) (by decide +kernel))
      ip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13401 (by decide)))
  change (movR64R64Effect 0x1133fe 10 2 t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g1r10 : ((Operand.reg 10 : Operand 64).read u1) = s.regValue .rdx := by
    have h := e1.writes
    change ((Operand.reg 10 : Operand 64).read u1) = ((Operand.reg 2 : Operand 64).read t) at h
    rw [g0r2] at h
    exact h
  have g1r6 : ((Operand.reg 6 : Operand 64).read u1) = s.regValue .rsi := (e1.agrees.read (by simp [movR64R64Effect_components])).trans g0r6
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x113401 0x4c (by simp [RexWPrefix]) 7 (.base 6 .none) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13401 _ (by decide) (by decide +kernel))
      ⟨e1.rip, by
        change MemReadable u1 (((Operand.reg 6 : Operand 64).read u1) + 0) 8
        rw [g1r6]
        exact input_readable pre f1 (j := 0) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13404 (by decide)))
  change (movR64M64Effect 0x113401 15 (.base 6 .none) u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load2 : memLoad u1.external (((Operand.reg 6 : Operand 64).read u1) + 0) 64 = a.l0 := by
    rw [g1r6]
    simpa [a, inputWords] using input_limb pre f1 input 0 (by decide)
  have g2r15 : ((Operand.reg 15 : Operand 64).read u2) = a.l0 := by
    have h := e2.writes
    change ((Operand.reg 15 : Operand 64).read u2) = memLoad u1.external (((Operand.reg 6 : Operand 64).read u1) + 0) 64 at h
    rw [load2] at h
    exact h
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x113404 0x4d 0xf9 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13404 _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13407 (by decide)))
  change (movR64R64Effect 0x113404 9 15 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g3r9 : ((Operand.reg 9 : Operand 64).read u3) = a.l0 := by
    have h := e3.writes
    change ((Operand.reg 9 : Operand 64).read u3) = ((Operand.reg 15 : Operand 64).read u2) at h
    rw [g2r15] at h
    exact h
  have g1r1 : ((Operand.reg 1 : Operand 64).read u1) = 1 := (e1.agrees.read (by simp [movR64R64Effect_components])).trans g0r1
  have g2r1 : ((Operand.reg 1 : Operand 64).read u2) = 1 := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r1
  have g3r1 : ((Operand.reg 1 : Operand 64).read u3) = 1 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r1
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (imul_r64_r64_effect_step 0x113407 0x4c 0xc9 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13407 _ (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1340b (by decide)))
  change (imulR64R64Effect 0x113407 9 1 u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [imulR64R64Effect_components, Component.Covers]) (by simp [imulR64R64Effect_components])
  have g4r9 : ((Operand.reg 9 : Operand 64).read u4) = a.l0 := by
    have h := e4.writes
    change ((Operand.reg 9 : Operand 64).read u4) = ((Operand.reg 9 : Operand 64).read u3) * ((Operand.reg 1 : Operand 64).read u3) at h
    rw [g3r1, g3r9] at h
    simpa using h
  have g4r1 : ((Operand.reg 1 : Operand 64).read u4) = 1 := (e4.agrees.read (by simp [imulR64R64Effect_components])).trans g3r1
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (mov_m64_r64_effect_step_any 0x11340b 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x1340b _ (by decide) (by decide +kernel))
      ⟨e4.rip, ScalarFrame.stack_writable pre.toCalleePre f4 (offset := 16) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f4 (offset := 16) (len := 8) (codeOffset := 0x1340b) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13410 (by decide)))
  change (movM64R64Effect 0x11340b 1 (.sib 4 none 0 (.d8 16)) u4).Holds u4 u5 at e5
  have ag5 : AgreesExcept [.mem (stackPtr u4 + 16) 8, .rip] u4 u5 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := after_store pre f4 ready5 (offset := 16) (by decide) ag5
  have wr5 : slot s u5 16 = 1 := by
    have h := e5.writes
    change memLoad u5.external (stackPtr u4 + 16) 64 = ((Operand.reg 1 : Operand 64).read u4) at h
    rw [f4.rsp, g4r1] at h
    exact h
  have g1r2 : ((Operand.reg 2 : Operand 64).read u1) = s.regValue .rdx := (e1.agrees.read (by simp [movR64R64Effect_components])).trans g0r2
  have g2r2 : ((Operand.reg 2 : Operand 64).read u2) = s.regValue .rdx := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r2
  have g3r2 : ((Operand.reg 2 : Operand 64).read u3) = s.regValue .rdx := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r2
  have g4r2 : ((Operand.reg 2 : Operand 64).read u4) = s.regValue .rdx := (e4.agrees.read (by simp [imulR64R64Effect_components])).trans g3r2
  have g5r2 : ((Operand.reg 2 : Operand 64).read u5) = s.regValue .rdx := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r2
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (mov_r64_m64_effect_step 0x113410 0x48 (by simp [RexWPrefix]) 0 (.base 2 .none) (by decide) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x13410 _ (by decide) (by decide +kernel))
      ⟨e5.rip, by
        change MemReadable u5 (((Operand.reg 2 : Operand 64).read u5) + 0) 8
        rw [g5r2]
        exact modulus_readable pre f5 (j := 0) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13413 (by decide)))
  change (movR64M64Effect 0x113410 0 (.base 2 .none) u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load6 : memLoad u5.external (((Operand.reg 2 : Operand 64).read u5) + 0) 64 = 0xffffffffffffffff := by
    rw [g5r2]
    exact modulus_limb pre f5 0 (by decide)
  have g6r0 : ((Operand.reg 0 : Operand 64).read u6) = 0xffffffffffffffff := by
    have h := e6.writes
    change ((Operand.reg 0 : Operand 64).read u6) = memLoad u5.external (((Operand.reg 2 : Operand 64).read u5) + 0) 64 at h
    rw [load6] at h
    exact h
  have g6r2 : ((Operand.reg 2 : Operand 64).read u6) = s.regValue .rdx := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r2
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (mov_r64_m64_effect_step 0x113413 0x48 (by simp [RexWPrefix]) 3 (.base 2 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x13413 _ (by decide) (by decide +kernel))
      ⟨e6.rip, by
        change MemReadable u6 (((Operand.reg 2 : Operand 64).read u6) + 8) 8
        rw [g6r2]
        exact modulus_readable pre f6 (j := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13417 (by decide)))
  change (movR64M64Effect 0x113413 3 (.base 2 (.d8 8)) u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have load7 : memLoad u6.external (((Operand.reg 2 : Operand 64).read u6) + 8) 64 = 0xffffffff := by
    rw [g6r2]
    exact modulus_limb pre f6 1 (by decide)
  have g7r3 : ((Operand.reg 3 : Operand 64).read u7) = 0xffffffff := by
    have h := e7.writes
    change ((Operand.reg 3 : Operand 64).read u7) = memLoad u6.external (((Operand.reg 2 : Operand 64).read u6) + 8) 64 at h
    rw [load7] at h
    exact h
  have g7r0 : ((Operand.reg 0 : Operand 64).read u7) = 0xffffffffffffffff := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r0
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x113417 0x48 0xc5 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x13417 _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1341a (by decide)))
  change (movR64R64Effect 0x113417 5 0 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g8r5 : ((Operand.reg 5 : Operand 64).read u8) = 0xffffffffffffffff := by
    have h := e8.writes
    change ((Operand.reg 5 : Operand 64).read u8) = ((Operand.reg 0 : Operand 64).read u7) at h
    rw [g7r0] at h
    exact h
  have g8r0 : ((Operand.reg 0 : Operand 64).read u8) = 0xffffffffffffffff := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r0
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (mov_m64_r64_effect_step_any 0x11341a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x1341a _ (by decide) (by decide +kernel))
      ⟨e8.rip, ScalarFrame.stack_writable pre.toCalleePre f8 (offset := 56) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f8 (offset := 56) (len := 8) (codeOffset := 0x1341a) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1341f (by decide)))
  change (movM64R64Effect 0x11341a 0 (.sib 4 none 0 (.d8 56)) u8).Holds u8 u9 at e9
  have ag9 : AgreesExcept [.mem (stackPtr u8 + 56) 8, .rip] u8 u9 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e9.agrees
  have f9 := after_store pre f8 ready9 (offset := 56) (by decide) ag9
  have wr9 : slot s u9 56 = 0xffffffffffffffff := by
    have h := e9.writes
    change memLoad u9.external (stackPtr u8 + 56) 64 = ((Operand.reg 0 : Operand 64).read u8) at h
    rw [f8.rsp, g8r0] at h
    exact h
  have g5r9 : ((Operand.reg 9 : Operand 64).read u5) = a.l0 := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r9
  have g6r9 : ((Operand.reg 9 : Operand 64).read u6) = a.l0 := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r9
  have g7r9 : ((Operand.reg 9 : Operand 64).read u7) = a.l0 := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r9
  have g8r9 : ((Operand.reg 9 : Operand 64).read u8) = a.l0 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r9
  have g9r9 : ((Operand.reg 9 : Operand 64).read u9) = a.l0 := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r9
  have g9r0 : ((Operand.reg 0 : Operand 64).read u9) = 0xffffffffffffffff := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r0
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (mul_r64_effect_step 0x11341f 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x1341f _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13422 (by decide)))
  change (mulR64Effect 0x11341f 9 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have g10r0 : ((Operand.reg 0 : Operand 64).read u10) = p0.1 := by
    have h := e10.writes.1
    change ((Operand.reg 0 : Operand 64).read u10) = ((Operand.reg 0 : Operand 64).read u9) * ((Operand.reg 9 : Operand 64).read u9) at h
    rw [g9r9, g9r0] at h
    simpa only [p0, product64] using h
  have g10r2 : ((Operand.reg 2 : Operand 64).read u10) = p0.2 := by
    have h := e10.writes.2
    change ((Operand.reg 2 : Operand 64).read u10) = mulHigh64 ((Operand.reg 0 : Operand 64).read u9) ((Operand.reg 9 : Operand 64).read u9) at h
    rw [g9r9, g9r0] at h
    simpa only [p0, product64] using h
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (mov_r64_r64_effect_step 0x113422 0x49 0xd0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x13422 _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13425 (by decide)))
  change (movR64R64Effect 0x113422 8 2 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g11r8 : ((Operand.reg 8 : Operand 64).read u11) = p0.2 := by
    have h := e11.writes
    change ((Operand.reg 8 : Operand 64).read u11) = ((Operand.reg 2 : Operand 64).read u10) at h
    rw [g10r2] at h
    simpa only [p0, product64] using h
  have g11r0 : ((Operand.reg 0 : Operand 64).read u11) = p0.1 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r0
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (mov_r64_r64_effect_step 0x113425 0x49 0xc3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x13425 _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13428 (by decide)))
  change (movR64R64Effect 0x113425 11 0 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g12r11 : ((Operand.reg 11 : Operand 64).read u12) = p0.1 := by
    have h := e12.writes
    change ((Operand.reg 11 : Operand 64).read u12) = ((Operand.reg 0 : Operand 64).read u11) at h
    rw [g11r0] at h
    simpa only [p0, product64] using h
  have g8r3 : ((Operand.reg 3 : Operand 64).read u8) = 0xffffffff := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r3
  have g9r3 : ((Operand.reg 3 : Operand 64).read u9) = 0xffffffff := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r3
  have g10r3 : ((Operand.reg 3 : Operand 64).read u10) = 0xffffffff := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r3
  have g11r3 : ((Operand.reg 3 : Operand 64).read u11) = 0xffffffff := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r3
  have g12r3 : ((Operand.reg 3 : Operand 64).read u12) = 0xffffffff := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r3
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (mov_r64_r64_effect_step 0x113428 0x48 0xd8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x13428 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1342b (by decide)))
  change (movR64R64Effect 0x113428 0 3 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g13r0 : ((Operand.reg 0 : Operand 64).read u13) = 0xffffffff := by
    have h := e13.writes
    change ((Operand.reg 0 : Operand 64).read u13) = ((Operand.reg 3 : Operand 64).read u12) at h
    rw [g12r3] at h
    exact h
  have g13r3 : ((Operand.reg 3 : Operand 64).read u13) = 0xffffffff := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r3
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (mov_r64_r64_effect_step 0x11342b 0x49 0xdd (by simp [RexWPrefix]) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x1342b _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1342e (by decide)))
  change (movR64R64Effect 0x11342b 13 3 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g14r13 : ((Operand.reg 13 : Operand 64).read u14) = 0xffffffff := by
    have h := e14.writes
    change ((Operand.reg 13 : Operand 64).read u14) = ((Operand.reg 3 : Operand 64).read u13) at h
    rw [g13r3] at h
    exact h
  have g14r3 : ((Operand.reg 3 : Operand 64).read u14) = 0xffffffff := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r3
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (mov_m64_r64_effect_step_any 0x11342e 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x1342e _ (by decide) (by decide +kernel))
      ⟨e14.rip, ScalarFrame.stack_writable pre.toCalleePre f14 (offset := 48) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f14 (offset := 48) (len := 8) (codeOffset := 0x1342e) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13433 (by decide)))
  change (movM64R64Effect 0x11342e 3 (.sib 4 none 0 (.d8 48)) u14).Holds u14 u15 at e15
  have ag15 : AgreesExcept [.mem (stackPtr u14 + 48) 8, .rip] u14 u15 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e15.agrees
  have f15 := after_store pre f14 ready15 (offset := 48) (by decide) ag15
  have wr15 : slot s u15 48 = 0xffffffff := by
    have h := e15.writes
    change memLoad u15.external (stackPtr u14 + 48) 64 = ((Operand.reg 3 : Operand 64).read u14) at h
    rw [f14.rsp, g14r3] at h
    exact h
  have g10r9 : ((Operand.reg 9 : Operand 64).read u10) = a.l0 := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r9
  have g11r9 : ((Operand.reg 9 : Operand 64).read u11) = a.l0 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r9
  have g12r9 : ((Operand.reg 9 : Operand 64).read u12) = a.l0 := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r9
  have g13r9 : ((Operand.reg 9 : Operand 64).read u13) = a.l0 := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r9
  have g14r9 : ((Operand.reg 9 : Operand 64).read u14) = a.l0 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r9
  have g15r9 : ((Operand.reg 9 : Operand 64).read u15) = a.l0 := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r9
  have g14r0 : ((Operand.reg 0 : Operand 64).read u14) = 0xffffffff := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r0
  have g15r0 : ((Operand.reg 0 : Operand 64).read u15) = 0xffffffff := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r0
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (mul_r64_effect_step 0x113433 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x13433 _ (by decide) (by decide +kernel))
      e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13436 (by decide)))
  change (mulR64Effect 0x113433 9 u15).Holds u15 u16 at e16
  have f16 := f15.after_registers ready16 e16.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have g16r0 : ((Operand.reg 0 : Operand 64).read u16) = p1.1 := by
    have h := e16.writes.1
    change ((Operand.reg 0 : Operand 64).read u16) = ((Operand.reg 0 : Operand 64).read u15) * ((Operand.reg 9 : Operand 64).read u15) at h
    rw [g15r9, g15r0] at h
    simpa only [p1, product64] using h
  have g16r2 : ((Operand.reg 2 : Operand 64).read u16) = p1.2 := by
    have h := e16.writes.2
    change ((Operand.reg 2 : Operand 64).read u16) = mulHigh64 ((Operand.reg 0 : Operand 64).read u15) ((Operand.reg 9 : Operand 64).read u15) at h
    rw [g15r9, g15r0] at h
    simpa only [p1, product64] using h
  obtain ⟨u17, run17, ready17, e17⟩ :=
    (mov_r64_r64_effect_step 0x113436 0x48 0xd3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x13436 _ (by decide) (by decide +kernel))
      e16.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13439 (by decide)))
  change (movR64R64Effect 0x113436 3 2 u16).Holds u16 u17 at e17
  have f17 := f16.after_registers ready17 e17.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g17r3 : ((Operand.reg 3 : Operand 64).read u17) = p1.2 := by
    have h := e17.writes
    change ((Operand.reg 3 : Operand 64).read u17) = ((Operand.reg 2 : Operand 64).read u16) at h
    rw [g16r2] at h
    simpa only [p1, product64] using h
  have g17r0 : ((Operand.reg 0 : Operand 64).read u17) = p1.1 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r0
  obtain ⟨u18, run18, ready18, e18⟩ :=
    (mov_r64_r64_effect_step 0x113439 0x49 0xc6 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f17.machine f17.bindingsSupported)
      (programText_slice (programLoaded_codeIn f17.loaded) 0x13439 _ (by decide) (by decide +kernel))
      e17.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1343c (by decide)))
  change (movR64R64Effect 0x113439 14 0 u17).Holds u17 u18 at e18
  have f18 := f17.after_registers ready18 e18.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g18r14 : ((Operand.reg 14 : Operand 64).read u18) = p1.1 := by
    have h := e18.writes
    change ((Operand.reg 14 : Operand 64).read u18) = ((Operand.reg 0 : Operand 64).read u17) at h
    rw [g17r0] at h
    simpa only [p1, product64] using h
  have g2r6 : ((Operand.reg 6 : Operand 64).read u2) = s.regValue .rsi := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r6
  have g3r6 : ((Operand.reg 6 : Operand 64).read u3) = s.regValue .rsi := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r6
  have g4r6 : ((Operand.reg 6 : Operand 64).read u4) = s.regValue .rsi := (e4.agrees.read (by simp [imulR64R64Effect_components])).trans g3r6
  have g5r6 : ((Operand.reg 6 : Operand 64).read u5) = s.regValue .rsi := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r6
  have g6r6 : ((Operand.reg 6 : Operand 64).read u6) = s.regValue .rsi := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r6
  have g7r6 : ((Operand.reg 6 : Operand 64).read u7) = s.regValue .rsi := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r6
  have g8r6 : ((Operand.reg 6 : Operand 64).read u8) = s.regValue .rsi := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r6
  have g9r6 : ((Operand.reg 6 : Operand 64).read u9) = s.regValue .rsi := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r6
  have g10r6 : ((Operand.reg 6 : Operand 64).read u10) = s.regValue .rsi := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r6
  have g11r6 : ((Operand.reg 6 : Operand 64).read u11) = s.regValue .rsi := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r6
  have g12r6 : ((Operand.reg 6 : Operand 64).read u12) = s.regValue .rsi := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r6
  have g13r6 : ((Operand.reg 6 : Operand 64).read u13) = s.regValue .rsi := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r6
  have g14r6 : ((Operand.reg 6 : Operand 64).read u14) = s.regValue .rsi := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r6
  have g15r6 : ((Operand.reg 6 : Operand 64).read u15) = s.regValue .rsi := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r6
  have g16r6 : ((Operand.reg 6 : Operand 64).read u16) = s.regValue .rsi := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r6
  have g17r6 : ((Operand.reg 6 : Operand 64).read u17) = s.regValue .rsi := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r6
  have g18r6 : ((Operand.reg 6 : Operand 64).read u18) = s.regValue .rsi := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r6
  obtain ⟨u19, run19, ready19, e19⟩ :=
    (add_r64_m64_effect_step 0x11343c 0x4c (by simp [RexWPrefix]) 6 (.base 6 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f18.machine f18.bindingsSupported)
      (programText_slice (programLoaded_codeIn f18.loaded) 0x1343c _ (by decide) (by decide +kernel))
      ⟨e18.rip, by
        change MemReadable u18 (((Operand.reg 6 : Operand 64).read u18) + 8) 8
        rw [g18r6]
        exact input_readable pre f18 (j := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13440 (by decide)))
  change (addR64M64Effect 0x11343c 14 (.base 6 (.d8 8)) u18).Holds u18 u19 at e19
  have f19 := f18.after_registers ready19 e19.agrees (by simp [addR64M64Effect_components, Component.Covers]) (by simp [addR64M64Effect_components])
  have load19 : memLoad u18.external (((Operand.reg 6 : Operand 64).read u18) + 8) 64 = a.l1 := by
    rw [g18r6]
    simpa [a, inputWords] using input_limb pre f18 input 1 (by decide)
  have g19r14 : ((Operand.reg 14 : Operand 64).read u19) = x.1 := by
    have h := e19.writes
    change ((Operand.reg 14 : Operand 64).read u19) = (addSpec ((Operand.reg 14 : Operand 64).read u18) (memLoad u18.external (((Operand.reg 6 : Operand 64).read u18) + 8) 64)).1 at h
    rw [load19, g18r14] at h
    simpa only [x, add64] using h
  have cf19 : (StatusFlags.ofRFLAGS u19.RFLAGS).CF = x.2 := by
    have h := e19.flags.1
    change (StatusFlags.ofRFLAGS u19.RFLAGS).CF = (addSpec ((Operand.reg 14 : Operand 64).read u18) (memLoad u18.external (((Operand.reg 6 : Operand 64).read u18) + 8) 64)).2.CF at h
    rw [load19, g18r14] at h
    simpa only [x, add64] using h
  have g18r3 : ((Operand.reg 3 : Operand 64).read u18) = p1.2 := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r3
  have g19r3 : ((Operand.reg 3 : Operand 64).read u19) = p1.2 := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r3
  obtain ⟨u20, run20, ready20, e20⟩ :=
    (adc_r64_imm8_effect_step 0x113440 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f19.machine f19.bindingsSupported)
      (programText_slice (programLoaded_codeIn f19.loaded) 0x13440 _ (by decide) (by decide +kernel))
      e19.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13444 (by decide)))
  change (adcR64Imm8Effect 0x113440 3 0 u19).Holds u19 u20 at e20
  have f20 := f19.after_registers ready20 e20.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g20r3 : ((Operand.reg 3 : Operand 64).read u20) = hi1.1 := by
    have h := e20.writes
    change ((Operand.reg 3 : Operand 64).read u20) = (adcSpec ((Operand.reg 3 : Operand 64).read u19) (0) (u19.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g19r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf19] at h
    simpa only [hi1, adc64] using h
  have cf20 : (StatusFlags.ofRFLAGS u20.RFLAGS).CF = hi1.2 := by
    have h := e20.flags.1
    change (StatusFlags.ofRFLAGS u20.RFLAGS).CF = (adcSpec ((Operand.reg 3 : Operand 64).read u19) (0) (u19.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g19r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf19] at h
    simpa only [hi1, adc64] using h
  have g3r15 : ((Operand.reg 15 : Operand 64).read u3) = a.l0 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r15
  have g4r15 : ((Operand.reg 15 : Operand 64).read u4) = a.l0 := (e4.agrees.read (by simp [imulR64R64Effect_components])).trans g3r15
  have g5r15 : ((Operand.reg 15 : Operand 64).read u5) = a.l0 := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r15
  have g6r15 : ((Operand.reg 15 : Operand 64).read u6) = a.l0 := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r15
  have g7r15 : ((Operand.reg 15 : Operand 64).read u7) = a.l0 := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r15
  have g8r15 : ((Operand.reg 15 : Operand 64).read u8) = a.l0 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r15
  have g9r15 : ((Operand.reg 15 : Operand 64).read u9) = a.l0 := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r15
  have g10r15 : ((Operand.reg 15 : Operand 64).read u10) = a.l0 := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r15
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = a.l0 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r15
  have g12r15 : ((Operand.reg 15 : Operand 64).read u12) = a.l0 := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r15
  have g13r15 : ((Operand.reg 15 : Operand 64).read u13) = a.l0 := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r15
  have g14r15 : ((Operand.reg 15 : Operand 64).read u14) = a.l0 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r15
  have g15r15 : ((Operand.reg 15 : Operand 64).read u15) = a.l0 := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r15
  have g16r15 : ((Operand.reg 15 : Operand 64).read u16) = a.l0 := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r15
  have g17r15 : ((Operand.reg 15 : Operand 64).read u17) = a.l0 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r15
  have g18r15 : ((Operand.reg 15 : Operand 64).read u18) = a.l0 := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r15
  have g19r15 : ((Operand.reg 15 : Operand 64).read u19) = a.l0 := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r15
  have g20r15 : ((Operand.reg 15 : Operand 64).read u20) = a.l0 := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r15
  have g13r11 : ((Operand.reg 11 : Operand 64).read u13) = p0.1 := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r11
  have g14r11 : ((Operand.reg 11 : Operand 64).read u14) = p0.1 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r11
  have g15r11 : ((Operand.reg 11 : Operand 64).read u15) = p0.1 := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r11
  have g16r11 : ((Operand.reg 11 : Operand 64).read u16) = p0.1 := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r11
  have g17r11 : ((Operand.reg 11 : Operand 64).read u17) = p0.1 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r11
  have g18r11 : ((Operand.reg 11 : Operand 64).read u18) = p0.1 := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r11
  have g19r11 : ((Operand.reg 11 : Operand 64).read u19) = p0.1 := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r11
  have g20r11 : ((Operand.reg 11 : Operand 64).read u20) = p0.1 := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r11
  obtain ⟨u21, run21, ready21, e21⟩ :=
    (add_r64_r64_effect_step 0x113444 0x4d 0xfb (by simp [RexWPrefix]) (by decide)).advances (readyToStep f20.machine f20.bindingsSupported)
      (programText_slice (programLoaded_codeIn f20.loaded) 0x13444 _ (by decide) (by decide +kernel))
      e20.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13447 (by decide)))
  change (addR64R64Effect 0x113444 11 15 u20).Holds u20 u21 at e21
  have f21 := f20.after_registers ready21 e21.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g21r11 : ((Operand.reg 11 : Operand 64).read u21) = z.1 := by
    have h := e21.writes
    change ((Operand.reg 11 : Operand 64).read u21) = (addSpec ((Operand.reg 11 : Operand 64).read u20) (((Operand.reg 15 : Operand 64).read u20))).1 at h
    rw [g20r15, g20r11] at h
    simpa only [z, add64] using h
  have cf21 : (StatusFlags.ofRFLAGS u21.RFLAGS).CF = z.2 := by
    have h := e21.flags.1
    change (StatusFlags.ofRFLAGS u21.RFLAGS).CF = (addSpec ((Operand.reg 11 : Operand 64).read u20) (((Operand.reg 15 : Operand 64).read u20))).2.CF at h
    rw [g20r15, g20r11] at h
    simpa only [z, add64] using h
  have g12r8 : ((Operand.reg 8 : Operand 64).read u12) = p0.2 := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r8
  have g13r8 : ((Operand.reg 8 : Operand 64).read u13) = p0.2 := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r8
  have g14r8 : ((Operand.reg 8 : Operand 64).read u14) = p0.2 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r8
  have g15r8 : ((Operand.reg 8 : Operand 64).read u15) = p0.2 := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r8
  have g16r8 : ((Operand.reg 8 : Operand 64).read u16) = p0.2 := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r8
  have g17r8 : ((Operand.reg 8 : Operand 64).read u17) = p0.2 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r8
  have g18r8 : ((Operand.reg 8 : Operand 64).read u18) = p0.2 := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r8
  have g19r8 : ((Operand.reg 8 : Operand 64).read u19) = p0.2 := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r8
  have g20r8 : ((Operand.reg 8 : Operand 64).read u20) = p0.2 := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r8
  have g21r8 : ((Operand.reg 8 : Operand 64).read u21) = p0.2 := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r8
  have g20r14 : ((Operand.reg 14 : Operand 64).read u20) = x.1 := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r14
  have g21r14 : ((Operand.reg 14 : Operand 64).read u21) = x.1 := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r14
  obtain ⟨u22, run22, ready22, e22⟩ :=
    (adc_r64_r64_effect_step 0x113447 0x4d 0xc6 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f21.machine f21.bindingsSupported)
      (programText_slice (programLoaded_codeIn f21.loaded) 0x13447 _ (by decide) (by decide +kernel))
      e21.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1344a (by decide)))
  change (adcR64R64Effect 0x113447 14 8 u21).Holds u21 u22 at e22
  have f22 := f21.after_registers ready22 e22.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have g22r14 : ((Operand.reg 14 : Operand 64).read u22) = y.1 := by
    have h := e22.writes
    change ((Operand.reg 14 : Operand 64).read u22) = (adcSpec ((Operand.reg 14 : Operand 64).read u21) (((Operand.reg 8 : Operand 64).read u21)) (u21.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g21r8, g21r14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf21] at h
    simpa only [y, adc64] using h
  have cf22 : (StatusFlags.ofRFLAGS u22.RFLAGS).CF = y.2 := by
    have h := e22.flags.1
    change (StatusFlags.ofRFLAGS u22.RFLAGS).CF = (adcSpec ((Operand.reg 14 : Operand 64).read u21) (((Operand.reg 8 : Operand 64).read u21)) (u21.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g21r8, g21r14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf21] at h
    simpa only [y, adc64] using h
  have g21r3 : ((Operand.reg 3 : Operand 64).read u21) = hi1.1 := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r3
  have g22r3 : ((Operand.reg 3 : Operand 64).read u22) = hi1.1 := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r3
  obtain ⟨u23, run23, ready23, e23⟩ :=
    (adc_r64_imm8_effect_step 0x11344a 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f22.machine f22.bindingsSupported)
      (programText_slice (programLoaded_codeIn f22.loaded) 0x1344a _ (by decide) (by decide +kernel))
      e22.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1344e (by decide)))
  change (adcR64Imm8Effect 0x11344a 3 0 u22).Holds u22 u23 at e23
  have f23 := f22.after_registers ready23 e23.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have g23r3 : ((Operand.reg 3 : Operand 64).read u23) = k.1 := by
    have h := e23.writes
    change ((Operand.reg 3 : Operand 64).read u23) = (adcSpec ((Operand.reg 3 : Operand 64).read u22) (0) (u22.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g22r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf22] at h
    simpa only [k, adc64] using h
  have cf23 : (StatusFlags.ofRFLAGS u23.RFLAGS).CF = k.2 := by
    have h := e23.flags.1
    change (StatusFlags.ofRFLAGS u23.RFLAGS).CF = (adcSpec ((Operand.reg 3 : Operand 64).read u22) (0) (u22.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g22r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf22] at h
    simpa only [k, adc64] using h
  have g5r1 : ((Operand.reg 1 : Operand 64).read u5) = 1 := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r1
  have g6r1 : ((Operand.reg 1 : Operand 64).read u6) = 1 := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r1
  have g7r1 : ((Operand.reg 1 : Operand 64).read u7) = 1 := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r1
  have g8r1 : ((Operand.reg 1 : Operand 64).read u8) = 1 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r1
  have g9r1 : ((Operand.reg 1 : Operand 64).read u9) = 1 := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r1
  have g10r1 : ((Operand.reg 1 : Operand 64).read u10) = 1 := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r1
  have g11r1 : ((Operand.reg 1 : Operand 64).read u11) = 1 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r1
  have g12r1 : ((Operand.reg 1 : Operand 64).read u12) = 1 := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r1
  have g13r1 : ((Operand.reg 1 : Operand 64).read u13) = 1 := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r1
  have g14r1 : ((Operand.reg 1 : Operand 64).read u14) = 1 := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r1
  have g15r1 : ((Operand.reg 1 : Operand 64).read u15) = 1 := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r1
  have g16r1 : ((Operand.reg 1 : Operand 64).read u16) = 1 := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r1
  have g17r1 : ((Operand.reg 1 : Operand 64).read u17) = 1 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r1
  have g18r1 : ((Operand.reg 1 : Operand 64).read u18) = 1 := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r1
  have g19r1 : ((Operand.reg 1 : Operand 64).read u19) = 1 := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r1
  have g20r1 : ((Operand.reg 1 : Operand 64).read u20) = 1 := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r1
  have g21r1 : ((Operand.reg 1 : Operand 64).read u21) = 1 := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r1
  have g22r1 : ((Operand.reg 1 : Operand 64).read u22) = 1 := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r1
  have g23r1 : ((Operand.reg 1 : Operand 64).read u23) = 1 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r1
  have g19r6 : ((Operand.reg 6 : Operand 64).read u19) = s.regValue .rsi := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r6
  have g20r6 : ((Operand.reg 6 : Operand 64).read u20) = s.regValue .rsi := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r6
  have g21r6 : ((Operand.reg 6 : Operand 64).read u21) = s.regValue .rsi := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r6
  have g22r6 : ((Operand.reg 6 : Operand 64).read u22) = s.regValue .rsi := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r6
  have g23r6 : ((Operand.reg 6 : Operand 64).read u23) = s.regValue .rsi := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r6
  have g1r7 : ((Operand.reg 7 : Operand 64).read u1) = s.regValue .rdi := (e1.agrees.read (by simp [movR64R64Effect_components])).trans g0r7
  have g2r7 : ((Operand.reg 7 : Operand 64).read u2) = s.regValue .rdi := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r7
  have g3r7 : ((Operand.reg 7 : Operand 64).read u3) = s.regValue .rdi := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r7
  have g4r7 : ((Operand.reg 7 : Operand 64).read u4) = s.regValue .rdi := (e4.agrees.read (by simp [imulR64R64Effect_components])).trans g3r7
  have g5r7 : ((Operand.reg 7 : Operand 64).read u5) = s.regValue .rdi := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r7
  have g6r7 : ((Operand.reg 7 : Operand 64).read u6) = s.regValue .rdi := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r7
  have g7r7 : ((Operand.reg 7 : Operand 64).read u7) = s.regValue .rdi := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r7
  have g8r7 : ((Operand.reg 7 : Operand 64).read u8) = s.regValue .rdi := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r7
  have g9r7 : ((Operand.reg 7 : Operand 64).read u9) = s.regValue .rdi := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r7
  have g10r7 : ((Operand.reg 7 : Operand 64).read u10) = s.regValue .rdi := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r7
  have g11r7 : ((Operand.reg 7 : Operand 64).read u11) = s.regValue .rdi := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r7
  have g12r7 : ((Operand.reg 7 : Operand 64).read u12) = s.regValue .rdi := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r7
  have g13r7 : ((Operand.reg 7 : Operand 64).read u13) = s.regValue .rdi := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r7
  have g14r7 : ((Operand.reg 7 : Operand 64).read u14) = s.regValue .rdi := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r7
  have g15r7 : ((Operand.reg 7 : Operand 64).read u15) = s.regValue .rdi := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r7
  have g16r7 : ((Operand.reg 7 : Operand 64).read u16) = s.regValue .rdi := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r7
  have g17r7 : ((Operand.reg 7 : Operand 64).read u17) = s.regValue .rdi := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r7
  have g18r7 : ((Operand.reg 7 : Operand 64).read u18) = s.regValue .rdi := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r7
  have g19r7 : ((Operand.reg 7 : Operand 64).read u19) = s.regValue .rdi := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r7
  have g20r7 : ((Operand.reg 7 : Operand 64).read u20) = s.regValue .rdi := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r7
  have g21r7 : ((Operand.reg 7 : Operand 64).read u21) = s.regValue .rdi := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r7
  have g22r7 : ((Operand.reg 7 : Operand 64).read u22) = s.regValue .rdi := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r7
  have g23r7 : ((Operand.reg 7 : Operand 64).read u23) = s.regValue .rdi := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r7
  have g9r5 : ((Operand.reg 5 : Operand 64).read u9) = 0xffffffffffffffff := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r5
  have g10r5 : ((Operand.reg 5 : Operand 64).read u10) = 0xffffffffffffffff := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r5
  have g11r5 : ((Operand.reg 5 : Operand 64).read u11) = 0xffffffffffffffff := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r5
  have g12r5 : ((Operand.reg 5 : Operand 64).read u12) = 0xffffffffffffffff := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r5
  have g13r5 : ((Operand.reg 5 : Operand 64).read u13) = 0xffffffffffffffff := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r5
  have g14r5 : ((Operand.reg 5 : Operand 64).read u14) = 0xffffffffffffffff := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r5
  have g15r5 : ((Operand.reg 5 : Operand 64).read u15) = 0xffffffffffffffff := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r5
  have g16r5 : ((Operand.reg 5 : Operand 64).read u16) = 0xffffffffffffffff := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r5
  have g17r5 : ((Operand.reg 5 : Operand 64).read u17) = 0xffffffffffffffff := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r5
  have g18r5 : ((Operand.reg 5 : Operand 64).read u18) = 0xffffffffffffffff := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r5
  have g19r5 : ((Operand.reg 5 : Operand 64).read u19) = 0xffffffffffffffff := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r5
  have g20r5 : ((Operand.reg 5 : Operand 64).read u20) = 0xffffffffffffffff := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r5
  have g21r5 : ((Operand.reg 5 : Operand 64).read u21) = 0xffffffffffffffff := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r5
  have g22r5 : ((Operand.reg 5 : Operand 64).read u22) = 0xffffffffffffffff := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r5
  have g23r5 : ((Operand.reg 5 : Operand 64).read u23) = 0xffffffffffffffff := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r5
  have g15r13 : ((Operand.reg 13 : Operand 64).read u15) = 0xffffffff := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r13
  have g16r13 : ((Operand.reg 13 : Operand 64).read u16) = 0xffffffff := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r13
  have g17r13 : ((Operand.reg 13 : Operand 64).read u17) = 0xffffffff := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r13
  have g18r13 : ((Operand.reg 13 : Operand 64).read u18) = 0xffffffff := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r13
  have g19r13 : ((Operand.reg 13 : Operand 64).read u19) = 0xffffffff := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r13
  have g20r13 : ((Operand.reg 13 : Operand 64).read u20) = 0xffffffff := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r13
  have g21r13 : ((Operand.reg 13 : Operand 64).read u21) = 0xffffffff := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r13
  have g22r13 : ((Operand.reg 13 : Operand 64).read u22) = 0xffffffff := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r13
  have g23r13 : ((Operand.reg 13 : Operand 64).read u23) = 0xffffffff := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r13
  have g2r10 : ((Operand.reg 10 : Operand 64).read u2) = s.regValue .rdx := (e2.agrees.read (by simp [movR64M64Effect_components])).trans g1r10
  have g3r10 : ((Operand.reg 10 : Operand 64).read u3) = s.regValue .rdx := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r10
  have g4r10 : ((Operand.reg 10 : Operand 64).read u4) = s.regValue .rdx := (e4.agrees.read (by simp [imulR64R64Effect_components])).trans g3r10
  have g5r10 : ((Operand.reg 10 : Operand 64).read u5) = s.regValue .rdx := (e5.agrees.read (by simp [movM64R64Effect_components])).trans g4r10
  have g6r10 : ((Operand.reg 10 : Operand 64).read u6) = s.regValue .rdx := (e6.agrees.read (by simp [movR64M64Effect_components])).trans g5r10
  have g7r10 : ((Operand.reg 10 : Operand 64).read u7) = s.regValue .rdx := (e7.agrees.read (by simp [movR64M64Effect_components])).trans g6r10
  have g8r10 : ((Operand.reg 10 : Operand 64).read u8) = s.regValue .rdx := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r10
  have g9r10 : ((Operand.reg 10 : Operand 64).read u9) = s.regValue .rdx := (e9.agrees.read (by simp [movM64R64Effect_components])).trans g8r10
  have g10r10 : ((Operand.reg 10 : Operand 64).read u10) = s.regValue .rdx := (e10.agrees.read (by simp [mulR64Effect_components])).trans g9r10
  have g11r10 : ((Operand.reg 10 : Operand 64).read u11) = s.regValue .rdx := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r10
  have g12r10 : ((Operand.reg 10 : Operand 64).read u12) = s.regValue .rdx := (e12.agrees.read (by simp [movR64R64Effect_components])).trans g11r10
  have g13r10 : ((Operand.reg 10 : Operand 64).read u13) = s.regValue .rdx := (e13.agrees.read (by simp [movR64R64Effect_components])).trans g12r10
  have g14r10 : ((Operand.reg 10 : Operand 64).read u14) = s.regValue .rdx := (e14.agrees.read (by simp [movR64R64Effect_components])).trans g13r10
  have g15r10 : ((Operand.reg 10 : Operand 64).read u15) = s.regValue .rdx := (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r10
  have g16r10 : ((Operand.reg 10 : Operand 64).read u16) = s.regValue .rdx := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r10
  have g17r10 : ((Operand.reg 10 : Operand 64).read u17) = s.regValue .rdx := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r10
  have g18r10 : ((Operand.reg 10 : Operand 64).read u18) = s.regValue .rdx := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r10
  have g19r10 : ((Operand.reg 10 : Operand 64).read u19) = s.regValue .rdx := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r10
  have g20r10 : ((Operand.reg 10 : Operand 64).read u20) = s.regValue .rdx := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r10
  have g21r10 : ((Operand.reg 10 : Operand 64).read u21) = s.regValue .rdx := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r10
  have g22r10 : ((Operand.reg 10 : Operand 64).read u22) = s.regValue .rdx := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r10
  have g23r10 : ((Operand.reg 10 : Operand 64).read u23) = s.regValue .rdx := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r10
  have g16r9 : ((Operand.reg 9 : Operand 64).read u16) = a.l0 := (e16.agrees.read (by simp [mulR64Effect_components])).trans g15r9
  have g17r9 : ((Operand.reg 9 : Operand 64).read u17) = a.l0 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r9
  have g18r9 : ((Operand.reg 9 : Operand 64).read u18) = a.l0 := (e18.agrees.read (by simp [movR64R64Effect_components])).trans g17r9
  have g19r9 : ((Operand.reg 9 : Operand 64).read u19) = a.l0 := (e19.agrees.read (by simp [addR64M64Effect_components])).trans g18r9
  have g20r9 : ((Operand.reg 9 : Operand 64).read u20) = a.l0 := (e20.agrees.read (by simp [adcR64Imm8Effect_components])).trans g19r9
  have g21r9 : ((Operand.reg 9 : Operand 64).read u21) = a.l0 := (e21.agrees.read (by simp [addR64R64Effect_components])).trans g20r9
  have g22r9 : ((Operand.reg 9 : Operand 64).read u22) = a.l0 := (e22.agrees.read (by simp [adcR64R64Effect_components])).trans g21r9
  have g23r9 : ((Operand.reg 9 : Operand 64).read u23) = a.l0 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r9
  have g23r14 : ((Operand.reg 14 : Operand 64).read u23) = y.1 := (e23.agrees.read (by simp [adcR64Imm8Effect_components])).trans g22r14
  have keep16 : slot s u23 16 = slot s u5 16 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 56) 8, .mem (stackPtr s - 112 + 48) 8]) u5 u23 := (((((((((((((((((e6.agrees.trans e7.agrees).trans e8.agrees).trans ag9).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans ag15).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [movR64M64Effect_components, movR64R64Effect_components, f8.rsp, mulR64Effect_components, f14.rsp, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, adcR64R64Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot16 := keep16.trans wr5
  have keep56 : slot s u23 56 = slot s u9 56 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ [.mem (stackPtr s - 112 + 48) 8]) u9 u23 := (((((((((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans ag15).trans e16.agrees).trans e17.agrees).trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [mulR64Effect_components, movR64R64Effect_components, f14.rsp, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, adcR64R64Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl)
    all_goals try exact id
    all_goals try contradiction
    all_goals rintro ⟨j, hj, he⟩
    all_goals exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have slot56 := keep56.trans wr9
  have keep48 : slot s u23 48 = slot s u15 48 := by
    have ag : AgreesExcept ([.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] ++ []) u15 u23 := (((((((e16.agrees.trans e17.agrees).trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).mono (by simp only [mulR64Effect_components, movR64R64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, addR64R64Effect_components, adcR64R64Effect_components]; simp)
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact id
    all_goals try contradiction
  have slot48 := keep48.trans wr15
  exact ⟨u23, ⟨23, ((((((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20).trans run21).trans run22).trans run23)⟩, ⟨f23, e23.rip, slot16, slot56, slot48, g23r1, g23r6, g23r7, g23r5, g23r13, g23r10, g23r9, g23r14, g23r3⟩⟩
end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.FirstRound
