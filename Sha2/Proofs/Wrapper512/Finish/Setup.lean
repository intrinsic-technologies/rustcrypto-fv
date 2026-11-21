import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.State
import Sha2.Proofs.Common.EffectCompose
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Wrapper.Memory
import X86Proofs.Instructions.Lea.Triple
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
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Finish

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def cloneDestinationMode (reverse : Bool) : AddrMode :=
  .sib 4 none 0 (if reverse then .d32 240 else .d8 32)

def cloneSourceMode (reverse trait : Bool) : AddrMode :=
  .sib 4 none 0 (if reverse then .d8 16 else .d32 (if trait then 256 else 240))

def cloneSetupBytes (reverse trait : Bool) : List UInt8 :=
  encodeLeaR64M 7 (cloneDestinationMode reverse) ++
    encodeLeaR64M 6 (cloneSourceMode reverse trait) ++ (0xba :: immBytes 32 208)

def cloneSetupEffect (pc : BitVec 64) (reverse trait : Bool) (s : RamState) : Effect :=
  { rip := pc + 18
    writes := [⟨(.reg 7 : Operand 64), rspOf s + (if reverse then 240 else 32)⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + (if reverse then 16 else if trait then 256 else 240)⟩,
      ⟨(.reg 2 : Operand 64), 208⟩] }

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem cloneSetupTriple [Bindings] (pc : BitVec 64) (reverse trait : Bool)
    (boundary : ReturnBoundary) (outside : ∀ i ≤ 18, pc + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = pc)
      (codeRange pc (cloneSetupBytes reverse trait))
      (Effect.post (cloneSetupEffect pc reverse trait)) := by
  advance_begin (lea_r64_effect_step pc 0x48 (by simp [RexWPrefix]) 7
    (cloneDestinationMode reverse) (by cases reverse <;> decide) (by cases reverse <;> rfl)
    (by cases reverse <;> rfl))
  case sub =>
    have h := codeRange_slice_subset pc (cloneSetupBytes reverse trait) 0 (if reverse then 8 else 5)
    have hb : List.take (if reverse then 8 else 5) (List.drop 0 (cloneSetupBytes reverse trait)) =
        encodeLeaR64M 7 (cloneDestinationMode reverse) := by cases reverse <;> cases trait <;> decide
    rw [hb] at h
    have he : encodeLeaR64M 7 (cloneDestinationMode reverse) =
        0x48 :: 0x8d :: (cloneDestinationMode reverse).modrm 7 :: (cloneDestinationMode reverse).tail := by
      cases reverse <;> decide
    simpa only [he, BitVec.add_zero] using h
  case «next» =>
    intro _ _
    cases reverse <;> exact outside _ (by decide)
  advance_then (lea_r64_effect_step (pc + BitVec.ofNat 64 (if reverse then 8 else 5)) 0x48
    (by simp [RexWPrefix]) 6 (cloneSourceMode reverse trait)
    (by cases reverse <;> cases trait <;> decide) (by cases reverse <;> cases trait <;> rfl)
    (by cases reverse <;> cases trait <;> rfl))
  case sub =>
    have h := codeRange_slice_subset pc (cloneSetupBytes reverse trait)
      (if reverse then 8 else 5) (if reverse then 5 else 8)
    have hb : List.take (if reverse then 5 else 8)
        (List.drop (if reverse then 8 else 5) (cloneSetupBytes reverse trait)) =
        encodeLeaR64M 6 (cloneSourceMode reverse trait) := by cases reverse <;> cases trait <;> decide
    rw [hb] at h
    exact h
  case mid =>
    intro s t hp hh ho
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · cases reverse <;> exact hh.rip_of rfl
    · change pc + BitVec.ofNat 64 (if reverse then 8 else 5) +
        BitVec.ofNat 64 (leaLen (cloneSourceMode reverse trait)) ≠ boundary.rip
      have hl : BitVec.ofNat 64 (if reverse then 8 else 5) +
          BitVec.ofNat 64 (leaLen (cloneSourceMode reverse trait)) = 13 := by
        cases reverse <;> cases trait <;> decide
      rw [BitVec.add_assoc, hl]
      exact outside 13 (by decide)
  advance_then (mov_r32_imm32_effect_step (pc + 13) 0xba (by decide) 208)
  case sub =>
    have h := codeRange_slice_subset pc (cloneSetupBytes reverse trait) 13 5
    have hb : List.take 5 (List.drop 13 (cloneSetupBytes reverse trait)) =
        0xba :: immBytes 32 208 := by cases reverse <;> cases trait <;> decide
    rw [hb] at h
    exact h
  case mid =>
    intro s t hp hh ho
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · apply hh.rip_of
      cases reverse <;> cases trait <;>
        simp [cloneSourceMode]
    · simpa [movR32Imm32Effect, BitVec.add_assoc] using outside 18 (by decide)
  cases reverse <;> cases trait <;>
    advance_finish [cloneSetupEffect, cloneDestinationMode, cloneSourceMode,
      BitVec.add_assoc, BitVec.reduceAdd]

end Sha2.Proofs.Wrapper512.Finish

namespace Sha2.Proofs.Wrapper512.Finish

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

theorem secondSetupCode {v : Variant} {form : Form} {s : RamState}
    (loaded : ProgramLoaded s)
    (eligible : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true) :
    CodeIn (codeRange (v.pc (v.dispatchOffset form) form)
      (cloneSetupBytes (form == .finalizeIntoReset true) true)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + v.dispatchOffset form)
    (cloneSetupBytes (form == .finalizeIntoReset true) true)
  · rcases eligible with rfl | rfl <;> cases v <;> decide +kernel
  · rcases eligible with rfl | rfl <;> cases v <;> decide +kernel

theorem secondSetupTriple [Bindings] (v : Variant) (form : Form)
    (eligible : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (v.dispatchOffset form) form)
      (codeRange (v.pc (v.dispatchOffset form) form)
        (cloneSetupBytes (form == .finalizeIntoReset true) true))
      (Effect.post (cloneSetupEffect (v.pc (v.dispatchOffset form) form)
        (form == .finalizeIntoReset true) true)) := by
  apply cloneSetupTriple
  intro i hi
  apply boundary_ne_program outside
  rw [Variant.pc_add v _ _ form]
  apply inProgram_of_textOffset
  have bound : v.textOffset form + v.dispatchOffset form + 18 < 71757 := by
    rcases eligible with rfl | rfl <;> cases v <;> decide +kernel
  omega

end Sha2.Proofs.Wrapper512.Finish

namespace Sha2.Proofs.Wrapper512.Finish

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512

def setupBytes (form : Form := .slices) : List UInt8 :=
  match form with
  | .digest => [0x48, 0x89, 0xe7] ++
      encodeLeaR64M 6 (.sib 4 none 0 (.d32 208)) ++ (0xba :: immBytes 32 208)
  | _ =>
  encodeLeaR64M 7 (.sib 4 none 0 (.d8 32)) ++
  encodeLeaR64M 6 (.sib 4 none 0 (.d32 240)) ++
  (0xba :: immBytes 32 208)

def setupEffect (v : Variant) (s : RamState) (form : Form := .slices) : Effect :=
  { rip := v.pc (if form = .slices then 0x22a else 0x153) form
    writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + (if form = .slices then 32 else 0)⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + (if form = .slices then 240 else 208)⟩,
      ⟨(.reg 2 : Operand 64), 208⟩] }

theorem setupCode {v : Variant} {s : RamState} (loaded : ProgramLoaded s)
    (form : Form := .slices)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    CodeIn (codeRange (v.pc (if form = .slices then 0x218 else 0x143) form)
      (setupBytes form)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + (if form = .slices then 0x218 else 0x143)) (setupBytes form)
  · rcases eligible with rfl | rfl <;> cases v <;> decide +kernel
  · rcases eligible with rfl | rfl <;> cases v <;> decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem setupTriple [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (form : Form := .slices)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
      (codeRange (v.pc (if form = .slices then 0x218 else 0x143) form) (setupBytes form))
      (Effect.post (fun s => setupEffect v s form)) := by
  rcases eligible with rfl | rfl
  · have h := cloneSetupTriple (v.pc 0x218) false false boundary (by
      intro i hi
      apply boundary_ne_program outside
      rw [Variant.pc_add]
      exact Variant.pc_inProgram v (by omega))
    have he : cloneSetupEffect (v.pc 0x218) false false =
        (fun s => setupEffect v s .slices) := by
      funext s
      simp only [cloneSetupEffect, setupEffect, Bool.false_eq_true, reduceIte]
      rw [show v.pc 0x218 + 18 = v.pc 0x22a from Variant.pc_add v 0x218 18]
    rw [he] at h
    simpa only [setupBytes, cloneSetupBytes, cloneDestinationMode, cloneSourceMode,
      Bool.false_eq_true, reduceIte] using h
  ·
    advance_begin (mov_r64_r64_effect_step (v.pc 0x143 .digest) 0x48 0xe7
      (by simp [RexWPrefix]) rfl)
    case «next» =>
      intro _ _
      apply boundary_ne_program outside
      cases v
      · exact inProgram_of_textOffset (0x3880 + 0x146) (by decide)
      · exact inProgram_of_textOffset (0x9490 + 0x146) (by decide)
      · exact inProgram_of_textOffset (0x57d0 + 0x146) (by decide)
      · exact inProgram_of_textOffset (0x7630 + 0x146) (by decide)
    advance_then (lea_r64_effect_step (v.pc 0x146 .digest) 0x48
      (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl)
    case sub =>
      have h := codeRange_slice_subset (v.pc 0x143 .digest) (setupBytes .digest) 3 8
      have hb : List.take 8 (List.drop 3 (setupBytes .digest)) =
        encodeLeaR64M 6 (.sib 4 none 0 (.d32 208)) := by decide +kernel
      rw [hb, Variant.pc_add v 0x143 3 .digest] at h
      exact h
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (Variant.pc_add v 0x143 3 .digest), ?_, ?_⟩
      · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
      · apply boundary_ne_program outside
        cases v
        · exact inProgram_of_textOffset (0x3880 + 0x14e) (by decide)
        · exact inProgram_of_textOffset (0x9490 + 0x14e) (by decide)
        · exact inProgram_of_textOffset (0x57d0 + 0x14e) (by decide)
        · exact inProgram_of_textOffset (0x7630 + 0x14e) (by decide)
    advance_then (mov_r32_imm32_effect_step (v.pc 0x14e .digest) 0xba (by decide +kernel) 208)
    case sub =>
      have h := codeRange_slice_subset (v.pc 0x143 .digest) (setupBytes .digest) 11 5
      have hb : List.take 5 (List.drop 11 (setupBytes .digest)) = 0xba :: immBytes 32 208 :=
        by decide +kernel
      rw [hb, Variant.pc_add v 0x143 11 .digest] at h
      exact h
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (Variant.pc_add v 0x146 8 .digest), ?_, ?_⟩
      · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
      · apply boundary_ne_program outside
        cases v
        · exact inProgram_of_textOffset (0x3880 + 0x153) (by decide)
        · exact inProgram_of_textOffset (0x9490 + 0x153) (by decide)
        · exact inProgram_of_textOffset (0x57d0 + 0x153) (by decide)
        · exact inProgram_of_textOffset (0x7630 + 0x153) (by decide)
    advance_finish [setupEffect, BitVec.add_zero, BitVec.ofNat_eq_ofNat, Variant.pc_add v 0x14e 5 .digest]

theorem setup [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form)
    (state : State v initial s form) (rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
    (eligible : form = .slices ∨ form = .digest := by first | exact Or.inl rfl | exact Or.inr rfl) :
    ∃ t, State v initial t form ∧ t.RIP = v.pc (if form = .slices then 0x22a else 0x153) form ∧
      t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 600 ∧
      t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 392 ∧
      t.regValue .rdx = BitVec.ofNat 64 208 := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := setupTriple v (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 form eligible
    s
    (supportedMachine_readyToStep state.machine) (setupCode state.loaded form eligible) rip
  have frame : AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] s t := by
    have h := effect.agrees
    apply h.mono
    intro c hc
    simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
      List.mem_append, or_false] at hc
    rcases hc with (hc | hc | hc) | hc
    · simp [hc]
    · simp [hc]
    · simp [hc]
    · simp [hc]
  have writes : WritesWithin [.reg 7, .reg 6, .reg 2, .rip]
      (v.writeRegions initial form) := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim
  have nextState : State v initial t form := by
    obtain ⟨n, hn⟩ := state.execution
    refine ⟨⟨n + fuel, hn.trans run⟩,
      supportedMachine_of_ready_agrees state.machine ready frame, ?_,
      fun a ha => frame.grow a (state.allocated a ha), ?_,
      frame.directionFlagClear (by simp) state.directionFlag,
      memoryWriteFrame_trans state.frame (frame.memoryWriteFrame writes),
      (frame.read (n := 64) (r := 4) (by simp)).trans state.rsp⟩
    · intro address byte fetch
      rw [frame.external (by simp [Component.Covers])]
      exact state.loaded address byte fetch
    · refine ⟨?_, ?_⟩
      · intro slot hs
        rw [frame.external (by simp [Component.Covers])]
        exact state.saved.words slot hs
      · rw [frame.external (by simp [Component.Covers])]
        exact state.saved.returnAddress
  refine ⟨t, nextState, effect.rip, ?_, ?_, ?_⟩
  · have w := effect.writes.1
    change t.regValue .rdi = stackPtr s + (if form = .slices then 32 else 0) at w
    rw [w, state.rsp]
    rcases eligible with rfl | rfl <;> simp only [Form.frameBytes, reduceIte, BitVec.sub_eq_add_neg,
      BitVec.add_assoc] <;> rfl
  · have w := effect.writes.2.1
    change t.regValue .rsi = stackPtr s + (if form = .slices then 240 else 208) at w
    rw [w, state.rsp]
    rcases eligible with rfl | rfl <;> simp only [Form.frameBytes, reduceIte, BitVec.sub_eq_add_neg,
      BitVec.add_assoc] <;> rfl
  · exact effect.writes.2.2

end Sha2.Proofs.Wrapper512.Finish
