import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Frame
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Branch
import P256.Proofs.Common.Encoding.Parser.LengthCheck.Triple
import P256.Proofs.Common.Instructions.Neg64
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.BranchTail

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Encoding.Parser.LengthCheck
open P256.Proofs.Common.Instructions.Neg64
open Iterator.Advance (step_nomem branch32)

theorem tail [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i k : Nat}
    (pre : Pre s boundary) (frame : FrameState s t) (bound : i+k ≤ 256)
    (rip : t.RIP = 0x10f3d3) (r15 : t.regValue .r15 = BitVec.ofNat 64 i)
    (rbp : t.regValue .rbp = BitVec.ofNat 64 k)
    (bits : memLoad t.external (stackPtr t+24) 64 = 256) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      u.RIP = (if i+k<256 then 0x10f3e7 else 0x10f4da) ∧
      u.regValue .r15 = BitVec.ofNat 64 (i+k) ∧
      u.regValue .rbp = -BitVec.ofNat 64 (i+k) ∧
      AgreesExcept [.reg 15,.reg 5,.flags,.rip] t u := by
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset h)
  obtain ⟨a,runA,readyA,loadedA,effectA⟩ := step_nomem (offset := 0xf3d3)
    (add_r64_r64_effect_step 0x10f3d3 0x49 0xef (by simp [RexWPrefix]) rfl)
    (readyToStep frame.machine frame.bindingsSupported) frame.loaded rip (by decide) (by decide +kernel)
    (next 0xf3d6 (by decide)) (by simp [Component.Covers])
  have agreesA : AgreesExcept [.reg 15,.flags,.rip] t a := effectA.agrees
  have r15A : a.regValue .r15 = BitVec.ofNat 64 (i+k) := by
    have h : a.regValue .r15 = t.regValue .r15+t.regValue .rbp := effectA.writes
    simpa only [r15, rbp, BitVec.ofNat_add] using h
  obtain ⟨b,runB,readyB,loadedB,effectB⟩ := step_nomem (offset := 0xf3d6)
    (mov_r64_r64_effect_step 0x10f3d6 0x4c 0xfd (by simp [RexWPrefix]) rfl)
    readyA loadedA effectA.rip (by decide) (by decide +kernel)
    (next 0xf3d9 (by decide)) (by simp [Component.Covers])
  have agreesB : AgreesExcept [.reg 5,.rip] a b := effectB.agrees
  obtain ⟨c,runC,readyC,loadedC,effectC⟩ := step_nomem (offset := 0xf3d9)
    (neg_r64_effect_step 0x10f3d9 0x48 0xdd (by simp [RexWPrefix]) rfl rfl)
    readyB loadedB effectB.rip (by decide) (by decide +kernel)
    (next 0xf3dc (by decide)) (by simp [negR64Effect, Effect.components, Component.Covers])
  have agreesBC : AgreesExcept [.reg 5,.flags,.rip] b c := effectC.agrees
  have agreesC : AgreesExcept [.reg 15,.reg 5,.flags,.rip] t c :=
    ((agreesA.trans agreesB).trans agreesBC).mono (by simp)
  have frameC := frame.after_registers readyC agreesC (by simp [Component.Covers]) (by simp)
  have r15C : c.regValue .r15 = BitVec.ofNat 64 (i+k) :=
    ((agreesB.trans agreesBC).read (n := 64) (r := 15) (by simp)).trans r15A
  have rbpC : c.regValue .rbp = -BitVec.ofNat 64 (i+k) := by
    have move : b.regValue .rbp = a.regValue .r15 := effectB.writes
    have negate : c.regValue .rbp = -b.regValue .rbp := effectC.writes
    rw [negate, move, r15A]
  have bitsC : memLoad c.external (stackPtr c+24) 64 = 256 := by
    have stackC : stackPtr c = stackPtr t := agreesC.read (n := 64) (r := 4) (by simp)
    rw [stackC, agreesC.external (by simp [Component.Covers])]
    exact bits
  obtain ⟨d,runD,readyD,loadedD,effectD⟩ := step_nomem (offset := 0xf3dc)
    (cmp_r64_m64_effect_step 0x10f3dc 0x4c (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    readyC loadedC ⟨effectC.rip, stack_readable pre.toCalleePre frameC (by decide : 24+8≤136)⟩
    (by decide) (by decide +kernel) (next 0xf3e1 (by decide)) (by simp [cmpR64M64Effect, Effect.components, Component.Covers])
  have agreesD : AgreesExcept [.flags,.rip] c d := effectD.agrees
  have carry : (StatusFlags.ofRFLAGS d.RFLAGS).CF = decide (i+k<256) := by
    have h := effectD.flags.1
    change _ = decide ((c.regValue .r15).toNat < (memLoad c.external (stackPtr c+24) 64).toNat) at h
    simpa only [r15C, bitsC, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i+k<2^64), BitVec.reduceToNat] using h
  have condition : condHolds 3 (StatusFlags.ofRFLAGS d.RFLAGS) = decide (¬i+k<256) := by
    by_cases lt : i+k<256 <;> simp [condHolds, carry, lt]
  obtain ⟨u,runU,readyU,_,ripU,agreesU⟩ := branch32 (offset := 0xf3e1) 3 0xf3
    (decide (¬i+k<256)) readyD loadedD effectD.rip condition (by decide)
    (by decide +kernel) (by decide +kernel) (by
      by_cases lt : i+k<256
      · simpa [lt, branchTarget, Extracted.textAddress] using next 0xf3e7 (by decide)
      · simpa [lt, branchTarget, Extracted.textAddress] using next 0xf4da (by decide))
  have agrees : AgreesExcept [.reg 15,.reg 5,.flags,.rip] t u :=
    ((agreesC.trans agreesD).trans agreesU).mono (by simp)
  refine ⟨5,u,(((runA.trans runB).trans runC).trans runD).trans runU,
    frame.after_registers readyU agrees (by simp [Component.Covers]) (by simp), ?_, ?_, ?_, agrees⟩
  · by_cases lt : i+k<256 <;> simpa [lt, branchTarget, Extracted.textAddress] using ripU
  · exact ((agreesD.trans agreesU).read (n := 64) (r := 15) (by simp)).trans r15C
  · exact ((agreesD.trans agreesU).read (n := 64) (r := 5) (by simp)).trans rbpC

theorem padding_exit [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (frame : FrameState s t) (rip : t.RIP = 0x10f4d2) :
    ∃ u, Advances boundary 2 t u ∧ FrameState s u ∧ u.RIP = 0x10f3d3 ∧
      u.regValue .r14 = t.regValue .rcx ∧ AgreesExcept [.reg 14,.rip] t u := by
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset h)
  obtain ⟨a,runA,readyA,loadedA,effectA⟩ := step_nomem (offset := 0xf4d2)
    (mov_r64_r64_effect_step 0x10f4d2 0x49 0xce (by simp [RexWPrefix]) rfl)
    (readyToStep frame.machine frame.bindingsSupported) frame.loaded rip (by decide) (by decide +kernel)
    (next 0xf4d5 (by decide)) (by simp [Component.Covers])
  have agreesA : AgreesExcept [.reg 14,.rip] t a := effectA.agrees
  obtain ⟨u,runU,readyU,_,effectU⟩ := step_nomem (offset := 0xf4d5)
    (jmp_rel32_effect_step 0x10f4d5 0xfffffef9 (by decide +kernel))
    readyA loadedA effectA.rip (by decide) (by decide +kernel)
    (next 0xf3d3 (by decide)) (by simp [jmpEffect, Effect.components, Component.Covers])
  have agreesU : AgreesExcept [.rip] a u := effectU.agrees
  have agrees : AgreesExcept [.reg 14,.rip] t u :=
    (agreesA.trans agreesU).mono (by simp)
  refine ⟨u,runA.trans runU,
    frame.after_registers readyU agrees (by simp [Component.Covers]) (by simp), ?_, ?_, agrees⟩
  · exact effectU.rip
  · exact (agreesU.read (n := 64) (r := 14) (by simp)).trans effectA.writes

end P256.Proofs.Verifying.Combination.Naf.Machine.BranchTail
