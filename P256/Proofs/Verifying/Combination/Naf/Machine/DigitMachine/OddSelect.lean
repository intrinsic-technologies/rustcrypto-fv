import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Memory
import P256.Proofs.Common.Instructions.Setae
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.CmovMemory.AboveEqual
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.SubByte
import P256.Proofs.Verifying.Combination.Naf.Machine.RecodeBranchArithmetic
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Encoding.Parser.LengthCheck.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Encoding.Parser.LengthCheck

set_option maxHeartbeats 600000 in
theorem odd_select [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i c w : Nat}
    (pre : Pre s boundary) (state : BranchPre s t i c w) (rip : t.RIP = 0x10f470) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10f495 ∧
      u.regValue .rax = BitVec.ofNat 64 (257-i) ∧
      u.regValue .r13 = BitVec.ofNat 64 (carry w) ∧
      (u.regValue .rdx).setWidth 8 = BitVec.ofInt 8 (digit w) ∧
      AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 13, .flags, .rip] t u := by
  have hi := state.indexBound
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset h)
  obtain ⟨a, ra, readyA, ea⟩ :=
    (mov_r64_m64_effect_step 0x10f470 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 .none) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf470 _ (by decide) (by decide +kernel))
      ⟨rip, by change MemReadable t (stackPtr t+0#64) 8
               exact stack_readable pre.toCalleePre state.toFrameState (offset := 0) (len := 8) (by decide)⟩
      (next 0xf474 (by decide))
  have ga : AgreesExcept [.reg 0, .rip] t a := ea.agrees
  have fa := state.toFrameState.after_registers readyA ga (by simp [Component.Covers]) (by simp)
  have axA : a.regValue .rax = 257 := by
    have h : a.regValue .rax = memLoad t.external (stackPtr t+0#64) 64 := ea.writes
    rw [BitVec.add_zero, state.rsp, state.outputLength] at h
    exact h
  have r14A : a.regValue .r14 = BitVec.ofNat 64 i :=
    (ga.read (n := 64) (r := 14) (by simp)).trans state.r14
  obtain ⟨b, rb, readyB, eb⟩ :=
    (sub_r64_r64_effect_step 0x10f474 0x4c 0xf0 (by simp [RexWPrefix]) rfl).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0xf474 _ (by decide) (by decide +kernel))
      ea.rip (next 0xf477 (by decide))
  have gb : AgreesExcept [.reg 0, .flags, .rip] a b := eb.agrees
  have fb := fa.after_registers readyB gb (by simp [Component.Covers]) (by simp)
  have axB : b.regValue .rax = BitVec.ofNat 64 (257-i) := by
    have h : b.regValue .rax = a.regValue .rax-a.regValue .r14 := eb.writes
    rw [axA, r14A] at h
    exact h.trans (recode_room hi)
  have cfB : (StatusFlags.ofRFLAGS b.RFLAGS).CF = false := by
    have h : _ = decide ((a.regValue .rax).toNat < (a.regValue .r14).toNat) := eb.flags.1
    rw [axA, r14A] at h
    rw [h]
    simp only [BitVec.toNat_ofNat, BitVec.reduceToNat, decide_eq_false_iff_not]
    omega
  have zfB : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = false := by
    have h : _ = ((a.regValue .rax-a.regValue .r14) == 0) := eb.flags.2.2.2.1
    rw [h, axA, r14A]
    have ne : (257 : BitVec 64) ≠ BitVec.ofNat 64 i := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
      omega
    simpa [BitVec.sub_eq_iff_eq_add] using ne
  obtain ⟨d, rd, readyD, _, ipD, gd⟩ := Iterator.Advance.branch32 (offset := 0xf477) 6 0xb0 false
    readyB fb.loaded eb.rip (by simp [condHolds, cfB, zfB]) (by decide) (by decide +kernel)
    (by decide +kernel) (next 0xf47d (by decide))
  have fd := fb.after_registers readyD gd (by simp [Component.Covers]) (by simp)
  obtain ⟨e, re, readyE, ee⟩ :=
    (xor_r32_r32_rex_effect_step 0x10f47d 0x45 0xed (by simp [RexNoWPrefix]) rfl).advances readyD
      (programText_slice (programLoaded_codeIn fd.loaded) 0xf47d _ (by decide) (by decide +kernel))
      ipD (next 0xf480 (by decide))
  have ge : AgreesExcept [.reg 13, .flags, .rip] d e := ee.agrees
  have fe := fd.after_registers readyE ge (by simp [Component.Covers]) (by simp)
  have r13E : e.regValue .r13 = 0 := by
    have h : e.regValue .r13 = (((Operand.reg 13 : Operand 32).read d) ^^^
      ((Operand.reg 13 : Operand 32).read d)).setWidth 64 := ee.writes
    simpa [BitVec.xor_self, BitVec.setWidth_zero] using h
  have early := ((ga.trans gb).trans gd).trans ge
  have rdxE : e.regValue .rdx = BitVec.ofNat 64 w :=
    (early.read (n := 64) (r := 2) (by simp)).trans state.rdx
  have halfE : memLoad e.external (stackPtr e+32) 64 = 16 := by
    rw [show stackPtr e+32 = stackPtr s-104 from stack_address fe.rsp (by decide),
      early.external (by simp [Component.Covers])]
    exact state.half
  obtain ⟨f, rf, readyF, ef⟩ :=
    (cmp_r64_m64_effect_step 0x10f480 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances readyE
      (programText_slice (programLoaded_codeIn fe.loaded) 0xf480 _ (by decide) (by decide +kernel))
      ⟨ee.rip, stack_readable pre.toCalleePre fe (by decide : 32+8 ≤ 136)⟩
      (next 0xf485 (by decide))
  have gf : AgreesExcept [.flags, .rip] e f := ef.agrees
  have ff := fe.after_registers readyF gf (by simp [Component.Covers]) (by simp)
  have cfF : (StatusFlags.ofRFLAGS f.RFLAGS).CF = decide (w<16) := by
    have h : _ = decide ((e.regValue .rdx).toNat < (memLoad e.external (stackPtr e+32) 64).toNat) := ef.flags.1
    rw [rdxE, halfE] at h
    exact h.trans (window_ult_sixteen state.windowBound)
  obtain ⟨g, rg, readyG, eg⟩ :=
    (setae_r8_rex_effect_step 0x10f485 0x41 0x93 0xc5 (by simp [RexPrefix]) rfl rfl).advances readyF
      (programText_slice (programLoaded_codeIn ff.loaded) 0xf485 _ (by decide) (by decide +kernel))
      ef.rip (next 0xf489 (by decide))
  have gg : AgreesExcept [.reg 13, .rip] f g := eg.agrees
  have fg := ff.after_registers readyG gg (by simp [Component.Covers]) (by simp)
  have r13G : g.regValue .r13 = BitVec.ofNat 64 (carry w) := by
    have r13F : f.regValue .r13 = 0 := (gf.read (n := 64) (r := 13) (by simp)).trans r13E
    have h : g.regValue .r13 = mergeGPR 8 (setccValue 3 f) (f.regValue .r13) := eg.writes
    rw [r13F] at h
    simp only [setccValue, condHolds, BitVec.reduceToNat, cfF] at h
    rw [h]
    cases small : decide (w<16) <;> simpa only [small, Bool.not_false, Bool.not_true, ite_true,
      Bool.false_eq_true, ite_false] using window_carry_merge w
  obtain ⟨h, rh, readyH, eh⟩ :=
    (mov_r32_imm32_effect_step 0x10f489 0xb9 (by decide) 0).advances readyG
      (programText_slice (programLoaded_codeIn fg.loaded) 0xf489 _ (by decide) (by decide +kernel))
      eg.rip (next 0xf48e (by decide))
  have gh : AgreesExcept [.reg 1, .rip] g h := eh.agrees
  have fh := fg.after_registers readyH gh (by simp [Component.Covers]) (by simp)
  have cxH : h.regValue .rcx = 0 := eh.writes
  have cfH : (StatusFlags.ofRFLAGS h.RFLAGS).CF = decide (w<16) :=
    (congrArg (fun r => (StatusFlags.ofRFLAGS r).CF) ((gg.trans gh).rflags (by simp) (by simp))).trans cfF
  have allH := (early.trans gf).trans gg |>.trans gh
  have byteH : memLoad h.external (stackPtr h+12) 32 = 32 := by
    rw [show stackPtr h+12 = stackPtr s-124 from stack_address fh.rsp (by decide),
      allH.external (by simp [Component.Covers])]
    exact state.byteWindow
  obtain ⟨v, rv, readyV, ev⟩ :=
    (cmovae_r32_m32_effect_step 0x10f48e 0x43 rfl 1 (.sib 4 none 0 (.d8 12))
      (by decide) rfl rfl).advances readyH
      (programText_slice (programLoaded_codeIn fh.loaded) 0xf48e _ (by decide) (by decide +kernel))
      ⟨eh.rip, stack_readable pre.toCalleePre fh (by decide : 12+4 ≤ 136)⟩
      (next 0xf493 (by decide))
  have gv : AgreesExcept [.reg 1, .rip] h v := ev.agrees
  have fv := fh.after_registers readyV gv (by simp [Component.Covers]) (by simp)
  have cxV : (v.regValue .rcx).setWidth 8 =
      (if decide (w<16) then (0 : BitVec 32) else 32).setWidth 8 := by
    have hx : v.regValue .rcx = (cmovR32M32Value 3 1 (stackPtr h+12) h).setWidth 64 := ev.writes
    have src : (Operand.reg 1 : Operand 32).read h = 0 := by
      change (h.regValue .rcx).setWidth 32 = 0
      rw [cxH]
      rfl
    simp only [cmovR32M32Value, condHolds, BitVec.reduceToNat, cfH, src] at hx
    change v.regValue .rcx = (if !decide (w<16) then memLoad h.external (stackPtr h+12) 32 else 0).setWidth 64 at hx
    rw [byteH] at hx
    rw [hx]
    cases decide (w<16) <;> rfl
  obtain ⟨u, ru, readyU, eu⟩ := (sub_dl_cl_effect_step 0x10f493).advances readyV
    (programText_slice (programLoaded_codeIn fv.loaded) 0xf493 _ (by decide) (by decide +kernel))
    ev.rip (next 0xf495 (by decide))
  have gu : AgreesExcept [.reg 2, .flags, .rip] v u := eu.agrees
  have fu := fv.after_registers readyU gu (by simp [Component.Covers]) (by simp)
  have full := ((allH.trans gv).trans gu)
  refine ⟨_, u, (((((((ra.trans rb).trans rd).trans re).trans rf).trans rg).trans rh).trans rv).trans ru,
    fu, eu.rip, ?_, ?_, ?_, full.mono (by simp)⟩
  · exact (((((((gd.trans ge).trans gf).trans gg).trans gh).trans gv).trans gu).read
      (n := 64) (r := 0) (by simp)).trans axB
  · exact (((gh.trans gv).trans gu).read (n := 64) (r := 13) (by simp)).trans r13G
  · have dxV : v.regValue .rdx = BitVec.ofNat 64 w :=
      ((allH.trans gv).read (n := 64) (r := 2) (by simp)).trans state.rdx
    have h : u.regValue .rdx = mergeGPR 8 ((v.regValue .rdx).setWidth 8 -
      (v.regValue .rcx).setWidth 8) (v.regValue .rdx) := eu.writes
    rw [h, dxV, cxV]
    exact window_digit_merge state.windowBound _

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
