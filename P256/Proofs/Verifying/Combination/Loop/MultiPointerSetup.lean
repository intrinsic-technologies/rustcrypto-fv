import P256.Proofs.Verifying.Combination.Loop.MultiLength
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def pointerSetupBytes : List UInt8 :=
  [0x49,1,0xd9,0x4f,0x8d,0x2c,8,0x49,0x83,0xc5,7,0x48,0x8d,0x0c,0x52,0x48,0xc1,0xe1,8]

def pointerSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f14a
    writes := [⟨(.reg 9 : Operand 64), s.regValue .r9 + s.regValue .rbx⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .r8 + (s.regValue .r9 + s.regValue .rbx) + 7⟩,
      ⟨(.reg 1 : Operand 64), (s.regValue .rdx + (s.regValue .rdx <<< 1)) <<< 8⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem pointerSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f137)
      (codeRange 0x10f137 pointerSetupBytes) (Effect.post pointerSetupEffect) := by
  advance_begin (add_r64_r64_effect_step 0x10f137 0x49 0xd9 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf13a (by decide))
  advance_then (lea_r64_effect_step 0x10f13a 0x4f (by simp [RexWPrefix]) 5
    (.sib 8 (some 9) 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f137 pointerSetupBytes 3 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf13e (by decide))⟩
  advance_then (add_r64_imm8_effect_step 0x10f13e 0x49 0xc5 7 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f137 pointerSetupBytes 7 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf142 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f142 0x48 (by simp [RexWPrefix]) 1
    (.sib 2 (some 2) 1 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f137 pointerSetupBytes 11 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf146 (by decide))⟩
  advance_then (shl_r64_imm8_effect_step 0x10f146 0x48 0xe1 8 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f137 pointerSetupBytes 15 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf14a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [pointerSetupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [pointerSetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [pointerSetupEffect]
  · x86_norm [pointerSetupEffect]
    all_goals (repeat first | constructor | rfl)

theorem initialize_pointers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {k : Nat} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f137)
    (metadata : t.regValue .rax = s.regValue .rsi) (index : t.regValue .rdx = 0)
    (ptr : t.regValue .r8 = digits) (zero : t.regValue .r9 = 0)
    (count : t.regValue .rbx = BitVec.ofNat 64 k) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x10f14d ∧
      w.regValue .rcx = tables ∧ w.regValue .r13 = digits + BitVec.ofNat 64 (k+7) ∧
      AgreesExcept [.reg 9, .reg 13, .reg 1, .flags, .rip] t w := by
  obtain ⟨fuel, a, runA, readyA, _, effectA⟩ := pointerSetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf137 pointerSetupBytes
      (by decide) (by decide +kernel)) rip
  have frameA : AgreesExcept [.reg 9, .reg 13, .reg 1, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have cursorA : a.regValue .r13 = digits + BitVec.ofNat 64 (k+7) := by
    have h := effectA.writes.2.1
    change a.regValue .r13 = t.regValue .r8 + (t.regValue .r9 + t.regValue .rbx) + 7 at h
    rw [ptr, zero, count] at h
    change a.regValue .r13 = digits + (0#64 + BitVec.ofNat 64 k) + 7#64 at h
    simpa only [BitVec.zero_add, BitVec.ofNat_add, BitVec.add_assoc] using h
  have zeroA : a.regValue .rcx = 0 := by
    have h := effectA.writes.2.2
    change a.regValue .rcx = (t.regValue .rdx + (t.regValue .rdx <<< 1)) <<< 8 at h
    rw [index] at h
    exact h.trans (by decide +kernel)
  have metadataA : a.regValue .rax = s.regValue .rsi :=
    (frameA.read (n := 64) (r := 0) (by simp)).trans metadata
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (add_r64_m64_effect_step 0x10f14a 0x48 (by simp [RexWPrefix]) 1
      (.base 0 .none) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf14a _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by
        change MemReadable a (a.regValue .rax + 0#64) 8
        rw [metadataA]
        exact metadata_readable pre stateA 0 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf14d (by decide)))
  have frameW : AgreesExcept [.reg 1, .flags, .rip] a w := effectW.agrees
  have frame : AgreesExcept [.reg 9, .reg 13, .reg 1, .flags, .rip] t w :=
    (frameA.trans frameW).mono (by simp)
  refine ⟨fuel+1, w, runA.trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip,
    ?_, (frameW.read (n := 64) (r := 13) (by simp)).trans cursorA, frame⟩
  have h := effectW.writes
  change w.regValue .rcx = a.regValue .rcx + memLoad a.external (a.regValue .rax + 0#64) 64 at h
  rw [zeroA, metadataA] at h
  change w.regValue .rcx = 0#64 + memLoad a.external (s.regValue .rsi + 0#64) 64 at h
  rw [BitVec.zero_add, metadata_read pre stateA 0 (by decide), BitVec.add_zero] at h
  exact h.trans pre.tablePointer

end P256.Proofs.Verifying.Combination.Loop.Multi
