import Sha3.Proofs.Finalize.Output.Basic

namespace Sha3.Proofs.Finalize.Output

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add movR32M32LegacyEffect
  movM32R32Effect
attribute [local x86_local] movR32M32LegacyEffect_local movM32R32Effect_local

local macro "output_begin " step:term:max ptr:term:max off:num delta:num
    hc:term:max hb:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_first ?k $step ?sub ?pre ?av ?boundary
  case pre =>
    intro s hp
    have hstate : (Operand.reg 3 : Operand 64).read s = $ptr := hp.state
    x86_norm at hstate
    refine ⟨hp.rip, ?_⟩
    x86_norm [hstate]
    simpa only [BitVec.add_zero] using hp.stateRead $off 8 (by decide)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case sub =>
    intro x hx
    apply $hc x
    first
    | exact (codeRange_mem_of_drop $delta (by decide +kernel)) x hx
    | exact (codeRange_mem_of_take (by decide +kernel)) x hx
  case boundary =>
    intros
    x86_norm
    apply $hb _ (by simp)
  case' k => x86_norm))

local macro "output_load " step:term:max ptr:term:max off:num width:num delta:num
    hc:term:max hb:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hstate : (Operand.reg 3 : Operand 64).read s = $ptr := hp.state
    have hout := hp.pointer
    x86_norm at hstate hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine LoadPre.of_holds he (ho true) (by x86_norm) (fun _ _ obs => AddrMode.addr_obs obs _ _) ?_
      x86_norm [hstate, hout]
      simpa only [BitVec.add_zero] using hp.stateRead $off $width (by decide)
    · exact Effect.Avoids.of_noMem (by
        simp [movR64M64Effect, movR32M32LegacyEffect, Effect.components, Component.Covers]) _
  case sub =>
    intro x hx
    apply $hc x
    exact (codeRange_mem_of_drop $delta (by decide +kernel)) x hx
  case boundary =>
    intros
    x86_norm
    apply $hb _ (by simp)
  case' k => x86_norm))

local macro "output_store " step:term:max ptr:term:max off:num width:num delta:num
    hc:term:max hb:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hstate : (Operand.reg 3 : Operand 64).read s = $ptr := hp.state
    have hout := hp.pointer
    x86_norm at hstate hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine StorePreReadable.of_holds he (ho true) (by x86_norm) ?_ ?_
      · x86_norm [hstate, hout]
        simpa only [BitVec.add_zero] using hp.outputRead $off ($width / 8) (by decide)
      · x86_norm [hstate, hout]
        simpa only [BitVec.add_zero, BitVec.add_assoc] using
          hp.store_tables $off ($width / 8) (by decide)
    · x86_norm [hstate, hout]
      simpa only [BitVec.add_zero] using hp.store_avoids $off (n := $width) _ _ (by decide)
  case sub =>
    intro x hx
    apply $hc x
    exact (codeRange_mem_of_drop $delta (by decide +kernel)) x hx
  case boundary =>
    intros
    x86_norm
    apply $hb _ (by simp)
  case' k => x86_norm))

def output224Bytes : List UInt8 :=
  [0x48, 0x8b, 0x3, 0x49, 0x89, 0x6, 0x48, 0x8b, 0x43, 0x8, 0x49, 0x89,
    0x46, 0x8, 0x48, 0x8b, 0x43, 0x10, 0x49, 0x89, 0x46, 0x10, 0x8b, 0x43,
    0x18, 0x41, 0x89, 0x46, 0x18]

def output224Effect (p ptr out : BitVec 64) (s : RamState) : Effect where
  rip := (p + 29)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), ((Operand.mem (ptr + 24) : Operand 32).read s).setWidth 64⟩,
    ⟨(Operand.mem out : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (ptr + 16) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 32), (Operand.mem (ptr + 24) : Operand 32).read s⟩]

set_option maxHeartbeats 1600000 in
theorem output224_advance [Bindings] (p ptr out : BitVec 64) (boundary : ReturnBoundary)
    (code : CodeMap) (hcode : ∀ x ∈ codeRange p output224Bytes, x ∈ code)
    (hboundary : ∀ q ∈ [(p + 3), (p + 6), (p + 10), (p + 14), (p + 18), (p + 22), (p + 25),
      (p + 29)],
      q ≠ boundary.rip) :
    AdvanceTriple boundary 8 (OutputPre p ptr out 28 (.reg 14) code) code
      (Effect.post (output224Effect p ptr out)) := by
  output_begin
    (show StepEffect _ _ (movR64M64Effect p 0 (.base 3 .none)) from
      (mov_r64_m64_effect_step p 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 0 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 3) 0 (.base 14 .none)) from
      (mov_m64_r64_effect_step_of_readable (p + 3) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 64 3 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 6) 0 (.base 3 (.d8 8))) from
      (mov_r64_m64_effect_step (p + 6) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 8 6 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 10) 0 (.base 14 (.d8 8))) from
      (mov_m64_r64_effect_step_of_readable (p + 10) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 64 10 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 14) 0 (.base 3 (.d8 16))) from
      (mov_r64_m64_effect_step (p + 14) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 8 14 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 18) 0 (.base 14 (.d8 16))) from
      (mov_m64_r64_effect_step_of_readable (p + 18) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 64 18 hcode hboundary
  output_load
    (show StepEffect _ _ (movR32M32LegacyEffect (p + 22) 0 (.base 3 (.d8 24))) from
      (mov_r32_m32_legacy_effect_step (p + 22) 0 (.base 3 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 4 22 hcode hboundary
  output_store
    (show StepEffect _ _ (movM32R32Effect (p + 25) 0 (.base 14 (.d8 24))) from
      (mov_m32_r32_effect_step_of_readable (p + 25) 0x41
        (by unfold RexNoWPrefix; decide +kernel) 0 (.base 14 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 32 25 hcode hboundary
  apply AdvanceTriple.block_end
  intro s t hp he
  have hstate : (Operand.reg 3 : Operand 64).read s = ptr := hp.state
  have hout := hp.pointer
  x86_norm at hstate hout
  apply he.weaken
  · x86_norm [output224Effect]
  · x86_norm [output224Effect, hstate, hout, hp.load_store, hp.load_store_zero, hp.load_store_base,
      BitVec.setWidth_setWidth_of_le,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i
    cases i <;> x86_norm [output224Effect]
  · x86_norm [output224Effect, hstate, hout]

def output256Bytes : List UInt8 :=
  [0x48, 0x8b, 0x43, 0x18, 0x49, 0x89, 0x46, 0x18, 0x48, 0x8b, 0x43, 0x10,
    0x49, 0x89, 0x46, 0x10, 0x48, 0x8b, 0x3, 0x48, 0x8b, 0x4b, 0x8, 0x49,
    0x89, 0x4e, 0x8, 0x49, 0x89, 0x6]

def output256Effect (p ptr out : BitVec 64) (s : RamState) : Effect where
  rip := (p + 30)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem out : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (ptr + 16) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (ptr + 24) : Operand 64).read s⟩]

set_option maxHeartbeats 1600000 in
theorem output256_advance [Bindings] (p ptr out : BitVec 64) (boundary : ReturnBoundary)
    (code : CodeMap) (hcode : ∀ x ∈ codeRange p output256Bytes, x ∈ code)
    (hboundary : ∀ q ∈ [(p + 4), (p + 8), (p + 12), (p + 16), (p + 19), (p + 23), (p + 27),
      (p + 30)],
      q ≠ boundary.rip) :
    AdvanceTriple boundary 8 (OutputPre p ptr out 32 (.reg 14) code) code
      (Effect.post (output256Effect p ptr out)) := by
  output_begin
    (show StepEffect _ _ (movR64M64Effect p 0 (.base 3 (.d8 24))) from
      (mov_r64_m64_effect_step p 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 0 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 4) 0 (.base 14 (.d8 24))) from
      (mov_m64_r64_effect_step_of_readable (p + 4) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 64 4 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 8) 0 (.base 3 (.d8 16))) from
      (mov_r64_m64_effect_step (p + 8) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 8 8 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 12) 0 (.base 14 (.d8 16))) from
      (mov_m64_r64_effect_step_of_readable (p + 12) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 64 12 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 16) 0 (.base 3 .none)) from
      (mov_r64_m64_effect_step (p + 16) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 8 16 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 19) 1 (.base 3 (.d8 8))) from
      (mov_r64_m64_effect_step (p + 19) 0x48
        (by unfold RexWPrefix; decide +kernel) 1 (.base 3 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 8 19 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 23) 1 (.base 14 (.d8 8))) from
      (mov_m64_r64_effect_step_of_readable (p + 23) 0x49
        (by unfold RexWPrefix; decide +kernel) 1 (.base 14 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 64 23 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 27) 0 (.base 14 .none)) from
      (mov_m64_r64_effect_step_of_readable (p + 27) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 64 27 hcode hboundary
  apply AdvanceTriple.block_end
  intro s t hp he
  have hstate : (Operand.reg 3 : Operand 64).read s = ptr := hp.state
  have hout := hp.pointer
  x86_norm at hstate hout
  apply he.weaken
  · x86_norm [output256Effect]
  · x86_norm [output256Effect, hstate, hout, hp.load_store, hp.load_store_zero, hp.load_store_base,
      BitVec.setWidth_setWidth_of_le,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i
    cases i <;> x86_norm [output256Effect]
  · x86_norm [output256Effect, hstate, hout]

def output384Bytes : List UInt8 :=
  [0x48, 0x8b, 0x43, 0x28, 0x49, 0x89, 0x46, 0x28, 0x48, 0x8b, 0x43, 0x20,
    0x49, 0x89, 0x46, 0x20, 0x48, 0x8b, 0x43, 0x18, 0x49, 0x89, 0x46, 0x18,
    0x48, 0x8b, 0x43, 0x10, 0x49, 0x89, 0x46, 0x10, 0x48, 0x8b, 0x3, 0x48,
    0x8b, 0x4b, 0x8, 0x49, 0x89, 0x4e, 0x8, 0x49, 0x89, 0x6]

def output384Effect (p ptr out : BitVec 64) (s : RamState) : Effect where
  rip := (p + 46)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem out : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (ptr + 16) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (ptr + 24) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (ptr + 32) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (ptr + 40) : Operand 64).read s⟩]

set_option maxHeartbeats 1600000 in
theorem output384_advance [Bindings] (p ptr out : BitVec 64) (boundary : ReturnBoundary)
    (code : CodeMap) (hcode : ∀ x ∈ codeRange p output384Bytes, x ∈ code)
    (hboundary : ∀ q ∈ [(p + 4), (p + 8), (p + 12), (p + 16), (p + 20), (p + 24), (p + 28),
      (p + 32), (p + 35), (p + 39), (p + 43), (p + 46)],
      q ≠ boundary.rip) :
    AdvanceTriple boundary 12 (OutputPre p ptr out 48 (.reg 14) code) code
      (Effect.post (output384Effect p ptr out)) := by
  output_begin
    (show StepEffect _ _ (movR64M64Effect p 0 (.base 3 (.d8 40))) from
      (mov_r64_m64_effect_step p 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 40))
        (by decide +kernel) rfl rfl))
    ptr 40 0 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 4) 0 (.base 14 (.d8 40))) from
      (mov_m64_r64_effect_step_of_readable (p + 4) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 40))
        (by decide +kernel) rfl rfl))
    ptr 40 64 4 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 8) 0 (.base 3 (.d8 32))) from
      (mov_r64_m64_effect_step (p + 8) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 32))
        (by decide +kernel) rfl rfl))
    ptr 32 8 8 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 12) 0 (.base 14 (.d8 32))) from
      (mov_m64_r64_effect_step_of_readable (p + 12) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 32))
        (by decide +kernel) rfl rfl))
    ptr 32 64 12 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 16) 0 (.base 3 (.d8 24))) from
      (mov_r64_m64_effect_step (p + 16) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 8 16 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 20) 0 (.base 14 (.d8 24))) from
      (mov_m64_r64_effect_step_of_readable (p + 20) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 64 20 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 24) 0 (.base 3 (.d8 16))) from
      (mov_r64_m64_effect_step (p + 24) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 8 24 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 28) 0 (.base 14 (.d8 16))) from
      (mov_m64_r64_effect_step_of_readable (p + 28) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 64 28 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 32) 0 (.base 3 .none)) from
      (mov_r64_m64_effect_step (p + 32) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 8 32 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 35) 1 (.base 3 (.d8 8))) from
      (mov_r64_m64_effect_step (p + 35) 0x48
        (by unfold RexWPrefix; decide +kernel) 1 (.base 3 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 8 35 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 39) 1 (.base 14 (.d8 8))) from
      (mov_m64_r64_effect_step_of_readable (p + 39) 0x49
        (by unfold RexWPrefix; decide +kernel) 1 (.base 14 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 64 39 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 43) 0 (.base 14 .none)) from
      (mov_m64_r64_effect_step_of_readable (p + 43) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 64 43 hcode hboundary
  apply AdvanceTriple.block_end
  intro s t hp he
  have hstate : (Operand.reg 3 : Operand 64).read s = ptr := hp.state
  have hout := hp.pointer
  x86_norm at hstate hout
  apply he.weaken
  · x86_norm [output384Effect]
  · x86_norm [output384Effect, hstate, hout, hp.load_store, hp.load_store_zero, hp.load_store_base,
      BitVec.setWidth_setWidth_of_le,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i
    cases i <;> x86_norm [output384Effect]
  · x86_norm [output384Effect, hstate, hout]

def output512Bytes : List UInt8 :=
  [0x48, 0x8b, 0x43, 0x38, 0x49, 0x89, 0x46, 0x38, 0x48, 0x8b, 0x43, 0x30,
    0x49, 0x89, 0x46, 0x30, 0x48, 0x8b, 0x43, 0x28, 0x49, 0x89, 0x46, 0x28,
    0x48, 0x8b, 0x43, 0x20, 0x49, 0x89, 0x46, 0x20, 0x48, 0x8b, 0x43, 0x18,
    0x49, 0x89, 0x46, 0x18, 0x48, 0x8b, 0x43, 0x10, 0x49, 0x89, 0x46, 0x10,
    0x48, 0x8b, 0x3, 0x48, 0x8b, 0x4b, 0x8, 0x49, 0x89, 0x4e, 0x8, 0x49,
    0x89, 0x6]

def output512Effect (p ptr out : BitVec 64) (s : RamState) : Effect where
  rip := (p + 62)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem out : Operand 64), (Operand.mem ptr : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (ptr + 8) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (ptr + 16) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (ptr + 24) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (ptr + 32) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (ptr + 40) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 48) : Operand 64), (Operand.mem (ptr + 48) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 56) : Operand 64), (Operand.mem (ptr + 56) : Operand 64).read s⟩]

set_option maxHeartbeats 1600000 in
theorem output512_advance [Bindings] (p ptr out : BitVec 64) (boundary : ReturnBoundary)
    (code : CodeMap) (hcode : ∀ x ∈ codeRange p output512Bytes, x ∈ code)
    (hboundary : ∀ q ∈ [(p + 4), (p + 8), (p + 12), (p + 16), (p + 20), (p + 24), (p + 28),
      (p + 32), (p + 36), (p + 40), (p + 44), (p + 48), (p + 51), (p + 55), (p + 59), (p + 62)],
      q ≠ boundary.rip) :
    AdvanceTriple boundary 16 (OutputPre p ptr out 64 (.reg 14) code) code
      (Effect.post (output512Effect p ptr out)) := by
  output_begin
    (show StepEffect _ _ (movR64M64Effect p 0 (.base 3 (.d8 56))) from
      (mov_r64_m64_effect_step p 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 56))
        (by decide +kernel) rfl rfl))
    ptr 56 0 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 4) 0 (.base 14 (.d8 56))) from
      (mov_m64_r64_effect_step_of_readable (p + 4) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 56))
        (by decide +kernel) rfl rfl))
    ptr 56 64 4 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 8) 0 (.base 3 (.d8 48))) from
      (mov_r64_m64_effect_step (p + 8) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 48))
        (by decide +kernel) rfl rfl))
    ptr 48 8 8 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 12) 0 (.base 14 (.d8 48))) from
      (mov_m64_r64_effect_step_of_readable (p + 12) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 48))
        (by decide +kernel) rfl rfl))
    ptr 48 64 12 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 16) 0 (.base 3 (.d8 40))) from
      (mov_r64_m64_effect_step (p + 16) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 40))
        (by decide +kernel) rfl rfl))
    ptr 40 8 16 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 20) 0 (.base 14 (.d8 40))) from
      (mov_m64_r64_effect_step_of_readable (p + 20) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 40))
        (by decide +kernel) rfl rfl))
    ptr 40 64 20 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 24) 0 (.base 3 (.d8 32))) from
      (mov_r64_m64_effect_step (p + 24) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 32))
        (by decide +kernel) rfl rfl))
    ptr 32 8 24 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 28) 0 (.base 14 (.d8 32))) from
      (mov_m64_r64_effect_step_of_readable (p + 28) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 32))
        (by decide +kernel) rfl rfl))
    ptr 32 64 28 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 32) 0 (.base 3 (.d8 24))) from
      (mov_r64_m64_effect_step (p + 32) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 8 32 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 36) 0 (.base 14 (.d8 24))) from
      (mov_m64_r64_effect_step_of_readable (p + 36) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 24))
        (by decide +kernel) rfl rfl))
    ptr 24 64 36 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 40) 0 (.base 3 (.d8 16))) from
      (mov_r64_m64_effect_step (p + 40) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 8 40 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 44) 0 (.base 14 (.d8 16))) from
      (mov_m64_r64_effect_step_of_readable (p + 44) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 (.d8 16))
        (by decide +kernel) rfl rfl))
    ptr 16 64 44 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 48) 0 (.base 3 .none)) from
      (mov_r64_m64_effect_step (p + 48) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.base 3 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 8 48 hcode hboundary
  output_load
    (show StepEffect _ _ (movR64M64Effect (p + 51) 1 (.base 3 (.d8 8))) from
      (mov_r64_m64_effect_step (p + 51) 0x48
        (by unfold RexWPrefix; decide +kernel) 1 (.base 3 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 8 51 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 55) 1 (.base 14 (.d8 8))) from
      (mov_m64_r64_effect_step_of_readable (p + 55) 0x49
        (by unfold RexWPrefix; decide +kernel) 1 (.base 14 (.d8 8))
        (by decide +kernel) rfl rfl))
    ptr 8 64 55 hcode hboundary
  output_store
    (show StepEffect _ _ (movM64R64Effect (p + 59) 0 (.base 14 .none)) from
      (mov_m64_r64_effect_step_of_readable (p + 59) 0x49
        (by unfold RexWPrefix; decide +kernel) 0 (.base 14 .none)
        (by decide +kernel) rfl rfl))
    ptr 0 64 59 hcode hboundary
  apply AdvanceTriple.block_end
  intro s t hp he
  have hstate : (Operand.reg 3 : Operand 64).read s = ptr := hp.state
  have hout := hp.pointer
  x86_norm at hstate hout
  apply he.weaken
  · x86_norm [output512Effect]
  · x86_norm [output512Effect, hstate, hout, hp.load_store, hp.load_store_zero, hp.load_store_base,
      BitVec.setWidth_setWidth_of_le,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i
    cases i <;> x86_norm [output512Effect]
  · x86_norm [output512Effect, hstate, hout]

end Sha3.Proofs.Finalize.Output
