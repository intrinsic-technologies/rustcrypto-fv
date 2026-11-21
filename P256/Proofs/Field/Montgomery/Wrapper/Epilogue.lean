import P256.Proofs.Field.Montgomery.Wrapper.State
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option hygiene false in
macro "montgomery_finish_return" square:term:max pre:term:max state:term:max rip:term:max run:term:max : tactic =>
  `(tactic| (
  obtain ⟨u, ha0, ready, effect⟩ :=
    (mov_r64_r64_effect_step (if $square then 0x113882 else 0x113912) 0x48 0xd8
      (by simp [RexWPrefix]) (by decide)).advances
      (readyToStep ($state).machine ($state).bindingsSupported)
      (programText_slice (programLoaded_codeIn ($state).loaded) (if $square then 0x13882 else 0x13912) _
        (by decide) (by decide +kernel)) $rip
      (boundary_ne_program ($pre).outerBoundary (inProgram_of_textOffset (if $square then 0x13885 else 0x13915) (by decide)))
  change (movR64R64Effect (if $square then 0x113882 else 0x113912) 0 3 t).Holds t u at effect
  have hm0 : u.external = t.external := effect.agrees.external (by simp [Component.Covers])
  have code := (programLoaded_codeIn ($state).loaded).of_external_eq hm0
  have hspu : stackPtr u = scratch s :=
    (effect.agrees.read (n := 64) (r := 4) (by simp)).trans ($state).rsp
  have hword (off : Nat) :
      (Operand.mem (stackPtr s - BitVec.ofNat 64 off) : Operand 64).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 off) : Operand 64).read t := by
    change memLoad u.external _ 64 = memLoad t.external _ 64
    rw [hm0]
  have readable (off : Nat) (ho : off ≤ 280) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 off) 8 :=
    readable_of_grow (stack_sub_readable ($pre).stack ho (by omega))
      ($state).allocated
  obtain ⟨v1, ha1, hr1, he1⟩ :=
    (add_r64_imm32_effect_step (if $square then 0x113885 else 0x113915) 0x48 0xc4 128
      (by simp [RexWPrefix]) (by decide) (by decide)).advances ready
      (programText_slice code (if $square then 0x13885 else 0x13915) [0x48, 0x81, 0xc4, 0x80, 0, 0, 0] (by decide +kernel) (by decide +kernel))
      effect.rip (boundary_ne_program ($pre).outerBoundary
        (inProgram_of_textOffset (if $square then 0x1388c else 0x1391c) (by decide)))
  change (addR64Imm32Effect (if $square then 0x113885 else 0x113915) 4 128 u).Holds u v1 at he1
  have hm1 : v1.external = u.external := he1.agrees.external (by simp [Component.Covers])
  have hsp1 : stackPtr v1 = stackPtr s - 8 := by
    have hw : stackPtr v1 = stackPtr u + 128 := he1.writes
    rw [hw, hspu]
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have hread1 : MemReadable v1 (stackPtr v1) 8 := by
    rw [hsp1]
    exact ((readable 8 (by decide)).of_holds effect).of_external_eq hm1
  obtain ⟨v2, ha2, hr2, he2⟩ :=
    (pop_r64_effect_step (if $square then 0x11388c else 0x11391c) 0x5b (by decide) (by decide)).advances hr1
      (programText_slice (code.of_external_eq hm1) (if $square then 0x1388c else 0x1391c) [0x5b] (by decide +kernel) (by decide +kernel))
      ⟨he1.rip, hread1⟩ (boundary_ne_program ($pre).outerBoundary
        (inProgram_of_textOffset (if $square then 0x1388d else 0x1391d) (by decide)))
  change (popR64Effect (if $square then 0x11388c else 0x11391c) 1 3 v1).Holds v1 v2 at he2
  have hm2 : v2.external = u.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hsp2 : stackPtr v2 = stackPtr s := by
    have hw : stackPtr v2 = stackPtr v1 + 8 := he2.writes.2
    rw [hw, hsp1]
    exact BitVec.sub_add_cancel _ _
  have hbx2 : v2.regValue .rbx = s.regValue .rbx := by
    have hw : v2.regValue .rbx = (Operand.mem (stackPtr v1) : Operand 64).read v1 := he2.writes.1
    rw [hw, hsp1]
    change memLoad v1.external (stackPtr s - 8) 64 = _
    rw [hm1]
    exact (hword 8).trans ($state).savedRbx
  have htop : stackTop v2 = (returnBoundary s).rip := by
    rw [stackTop, hsp2]
    change memLoad v2.external (stackPtr s) 64 = _
    rw [hm2]
    have hw := hword 0
    simp only [BitVec.sub_zero] at hw
    exact hw.trans ($state).returnWord
  have hread2 : MemReadable v2 (stackPtr v2) 8 := by
    rw [hsp2]
    have hw := (readable 0 (by decide)).of_holds effect
    simp only [BitVec.sub_zero] at hw
    exact hw.of_external_eq hm2
  obtain ⟨v3, ha3, hr3, he3⟩ := (ret_effect_step (if $square then 0x11388d else 0x11391d)).advances hr2
    (programText_slice (code.of_external_eq hm2) (if $square then 0x1388d else 0x1391d) [0xc3] (by decide +kernel) (by decide +kernel))
    ⟨⟨he2.rip, hread2⟩, htop ▸ inProgram_low ($pre).returnInProgram⟩
    (by change stackTop v2 ≠ boundary.rip
        rw [htop]
        exact boundary_ne_program ($pre).outerBoundary ($pre).returnInProgram)
  have hm3 : v3.external = u.external :=
    (he3.agrees.external (by simp [Component.Covers])).trans hm2
  have hag := ((effect.agrees.trans he1.agrees).trans he2.agrees).trans he3.agrees
  have registers : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      v3.regValue r = s.regValue r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (he3.agrees.read (n := 64) (r := 3) (by simp)).trans hbx2
    all_goals apply Eq.trans _ (($state).registers _ (by simp))
    all_goals first
      | exact hag.read (n := 64) (r := 5) (by simp [movR64R64Effect, addR64Imm32Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 12) (by simp [movR64R64Effect, addR64Imm32Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 13) (by simp [movR64R64Effect, addR64Imm32Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 14) (by simp [movR64R64Effect, addR64Imm32Effect, popR64Effect, retEffect, Effect.components])
      | exact hag.read (n := 64) (r := 15) (by simp [movR64R64Effect, addR64Imm32Effect, popR64Effect, retEffect, Effect.components])
  refine ⟨v3, {
    execution := ⟨_, (((($run).trans ha0).trans ha1).trans ha2).trans ha3⟩
    rip := he3.rip.trans htop
    rsp := ?_
    machine := supportedMachine_of_ready_agrees ($state).machine hr3 hag
    bindingsSupported := bindingsSupported_of_ready_agrees ($state).bindingsSupported hr3 hag
    calleeSaved := registers
    directionFlag := hag.directionFlagClear (by simp) ($state).directionFlag
    mxcsr := (hag.mxcsr (by simp)).trans ($state).mxcsr
    fp87 := (hag.fcw (by simp)).trans ($state).fp87
    frame := ?_
    loaded := ?_
    allocated := fun a ha => hag.grow a (($state).allocated a ha)
  }, ?_⟩
  · have hw : stackPtr v3 = stackPtr v2 + 8 := he3.writes
    change stackPtr v3 = stackPtr s + 8
    rw [hw, hsp2]
  · intro a hout
    rw [hm3, hm0]
    exact ($state).frame a hout
  · intro a b hf
    rw [hm3, hm0]
    exact ($state).loaded a b hf
  · exact hm3.trans hm0
  ))

theorem finish_return_at (square : Bool) [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64} {fuel : Nat}
    (pre : CalleePre s boundary entryPC 32 32 280) (state : FrameState s t)
    (rip : t.RIP = (if square then 0x113882 else 0x113912)) (run : Advances boundary fuel s t) :
    ∃ v, CalleeResult s v boundary 32 280 ∧ v.external = t.external := by
  cases square
  · montgomery_finish_return false pre state rip run
  · montgomery_finish_return true pre state rip run

theorem finish_return [Bindings] {s t : RamState} {boundary : ReturnBoundary} {fuel : Nat}
    (pre : MultiplyPre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x113912) (run : Advances boundary fuel s t) :
    ∃ v, CalleeResult s v boundary 32 280 ∧ v.external = t.external := by
  exact finish_return_at false pre.toCalleePre state rip run

end P256.Proofs.Field.Montgomery.Wrapper
