import P256.Proofs.Common.Instructions.CrossPageStore.Mov
import P256.Proofs.Sec1.SquareRoot.Exponent.NextWord.Steps
import P256.Proofs.Sec1.SquareRoot.Exponent.NextWord.Memory

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ExponentPosition.next_word [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x n : Nat} (ctx : ExponentPre s boundary x) (hp : ExponentPosition s t x n)
    (hnpos : 0 < n) (hn : n < 64) (hmod : n % 16 = 0) (hip : t.RIP = 0x1154c0)
    (hacc : MontgomeryAt t (exponentFrameBase s + 0x30)
      (x ^ (sqrtExponent / 16 ^ n) % P256.Spec.Operations.domain.p)) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentLoopState s u x n := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.toCalleePre.outerBoundary (inProgram_of_textOffset offset ho)
  obtain ⟨t0, fuel, ha0, hr0, hi0, hs0⟩ := exponent_window_continue
    (readyToStep hp.frame.machine hp.frame.bindingsSupported) (programLoaded_codeIn hp.frame.loaded)
    hip ctx.toCalleePre.outerBoundary
  have he0 (a : BitVec 64) : t0.external[a]? = t.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (hs0.external (by simp [Component.Covers]))
  have hp0 := hp.of_flags hr0 hs0
  have hwzero : (Operand.reg 14 : Operand 32).read t = 0 := by
    exact hp.window32.trans (by rw [hmod]; rfl)
  have hnword : (Operand.reg 5 : Operand 64).read t ≠ 0 := by
    rw [show (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64 (n / 16) from hp.word]
    exact (show ∀ i : Fin 64, 0 < i.val → i.val % 16 = 0 →
      BitVec.ofNat 64 (i.val / 16) ≠ 0 by decide +kernel) ⟨n, hn⟩ hnpos hmod
  have hip0 : t0.RIP = 0x115499 := by
    simpa only [hwzero, hnword, ite_true, ite_false] using hi0
  obtain ⟨t1, ha1, hr1, hi1, hw1, hv1, hs1⟩ :=
    exponent_next_word_prepare ctx hp0 hnpos hn hmod hip0
  have hf1 := hp0.frame.of_registers hr1 hs1 (by decide) (by simp [Component.Covers])
  have he1 (a : BitVec 64) : t1.external[a]? = t0.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (hs1.external (by simp [Component.Covers]))
  have hc1 := hp0.constants.of_memory he1
  have hacc1 := montgomeryAt_of_memory he1 (montgomeryAt_of_memory he0 hacc)
  have haddr : storeAddrAt 0x1154ab (.sib 4 none 0 (.d32 0x2c0)) 8 t1 =
      exponentFrameBase s + 0x2c0 := by
    change t1.regValue .rsp + 0x2c0 = _
    rw [hf1.rsp]
  have hwrite : P256.Proofs.Common.Instructions.CrossPageStore.Writable t1
      (exponentFrameBase s + 0x2c0) 8 := by
    have hw := ScalarFrame.stack_writable ctx.toCalleePre hf1.scalarFrame
      (offset := 0x2c0) (len := 8) (by decide) (by decide) (by decide)
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t1
      (t1.regValue .rsp + 0x2c0) 8 at hw
    rw [hf1.rsp] at hw
    exact hw
  have hapart : RangeApart (exponentFrameBase s + 0x2c0) 8 0x1154ab 8 := by
    have hw := ScalarFrame.stack_code ctx.toCalleePre hf1.scalarFrame
      (offset := 0x2c0) (len := 8) (codeOffset := 0x154ab) (codeLen := 8)
      (by decide) (by decide) (by decide)
    change RangeApart (t1.regValue .rsp + 0x2c0) 8 0x1154ab 8 at hw
    rw [hf1.rsp] at hw
    exact hw
  have hc2 : CodeIn (codeRange 0x1154ab [0x48,0x89,0xac,0x24,0xc0,2,0,0]) t1 :=
    programText_slice (programLoaded_codeIn hf1.loaded) 0x154ab _
      (by decide) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1154ab 0x48 (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d32 0x2c0)) (by decide +kernel) rfl rfl).advances
      hr1 hc2 ⟨hi1, haddr ▸ hwrite, haddr ▸ hapart⟩ (hnext 0x154b3 (by decide))
  have hs2 : AgreesExcept [.mem (exponentFrameBase s + 0x2c0) 8, .rip] t1 t2 := by
    have hh := he2.agrees
    rw [movM64R64Effect_components,
      show 3 + (AddrMode.sib 4 none 0 (.d32 0x2c0)).tail.length = 8 from rfl, haddr] at hh
    exact hh
  have hf2 := NextWord.frame_of_store ctx hf1 hr2 hs2
  have hconst2 := ExponentConstants.of_savedWord_store ctx hc1 hf2 hs2
  have hacc2 := NextWord.accumulator_of_store hs2 hacc1
  have hsave2 : exponentWordAt t2 (exponentFrameBase s + 0x2c0)
      (BitVec.ofNat 64 ((n - 1) / 16)) := by
    have hh := he2.writes
    change exponentWordAt t2 (storeAddrAt 0x1154ab (.sib 4 none 0 (.d32 0x2c0)) 8 t1)
      (t1.regValue .rbp) at hh
    rw [haddr, hw1] at hh
    exact hh
  have hc3 : CodeIn (codeRange 0x1154b3 [0xeb,0x10]) t2 :=
    programText_slice (programLoaded_codeIn hf2.loaded) 0x154b3 _
      (by decide) (by decide +kernel)
  obtain ⟨u, ha3, hr3, he3⟩ :=
    (jmp_rel8_effect_step 0x1154b3 0x10 (by decide)).advances
      hr2 hc3 he2.rip (hnext 0x154c5 (by decide))
  have hs3 : AgreesExcept [.rip] t2 u := he3.agrees
  have hext3 (a : BitVec 64) : u.external[a]? = t2.external[a]? :=
    congrArg (fun m : Ram => m[a]?) (hs3.external (by simp [Component.Covers]))
  have hreg (r : BitVec 5) (h1 : Component.reg r ∉ [.reg 5, .reg 14, .flags, .rip]) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read t0 := by
    rw [hs3.read (by simp), hs2.read (by simp), hs1.read h1]
  refine ⟨u, fuel + 4 + 1 + 1, ((ha0.trans ha1).trans ha2).trans ha3,
    hf2.of_registers hr3 hs3 (by decide) (by simp [Component.Covers]),
    hconst2.of_memory hext3, he3.rip, ?_, exponentWordAt_of_memory hext3 hsave2, ?_,
    (hreg 3 (by decide)).trans hp0.firstWord,
    (hreg 13 (by decide)).trans hp0.firstWindow,
    (hreg 15 (by decide)).trans hp0.parameterPointer,
    (hreg 11 (by decide)).trans hp0.modulus0,
    (hreg 12 (by decide)).trans hp0.inverse,
    montgomeryAt_of_memory hext3 hacc2⟩
  · exact ((hs3.read (n := 64) (r := 5) (by simp)).trans
      (hs2.read (n := 64) (r := 5) (by simp))).trans hw1
  · have hnwindow : (n - 1) % 16 + 1 = 16 := by omega
    rw [hnwindow]
    exact ((hs3.read (n := 64) (r := 14) (by simp)).trans
      (hs2.read (n := 64) (r := 14) (by simp))).trans hv1

end P256.Proofs.Sec1.SquareRoot
