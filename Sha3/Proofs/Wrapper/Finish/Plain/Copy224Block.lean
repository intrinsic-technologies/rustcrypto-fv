import Sha3.Proofs.Wrapper.Finish.Plain.Copy
import Sha3.Proofs.Finalize.Output.Basic
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def copy224StoreEffect (p : BitVec 64) (am : AddrMode) : RamState → Effect :=
  storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
    (fun s ↦ (Operand.reg 0 : Operand 32).read s)

theorem copy224StoreEffect_local {p : BitVec 64} {am : AddrMode} :
    Effect.Local (copy224StoreEffect p am) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · simp [copy224StoreEffect, storeEffect, storeAddrAt, h.read_reg, AddrMode.addr_obs h]
  · simp [copy224StoreEffect, storeEffect, storeAddrAt, h.read_reg, AddrMode.addr_obs h]
  · simp [copy224StoreEffect, storeEffect, storeAddrAt, h.read_reg, AddrMode.addr_obs h]
  · cases i <;> simp_all [copy224StoreEffect, storeEffect, storeAddrAt, Effect.flag,
      StatusFlags.get,
      h.read_reg, AddrMode.addr_obs h]
  · simp [copy224StoreEffect, storeEffect, storeAddrAt, Write.Full, Operand.Full]

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add copy224StoreEffect
  movR32M32LegacyEffect
attribute [local x86_local] copy224StoreEffect_local movR32M32LegacyEffect_local

local macro "copy224_load " keccak:term:max mode:term:max step:term:max off:num delta:num : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hsp := hp.rsp
    change (Operand.reg 4 : Operand 64).read s = _ at hsp
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]) (fun _ _ obs => AddrMode.addr_obs obs _ _) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _⟩
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp]
    simpa only [BitVec.add_zero] using hp.stackRead $off 8 (by cases ($keccak) <;> decide)
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (((copy_image .sha224 $keccak $mode (by simp)).slice $delta (by decide +kernel)) x hx).2
  case boundary =>
    intro s t hp he
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
    exact hp.ne_returnBoundary (by apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]))

local macro "copy224_store " keccak:term:max mode:term:max step:term:max off:num delta:num width:num dest:ident tables:ident avoids:ident : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hsp := hp.rsp
    change (Operand.reg 4 : Operand 64).read s = _ at hsp
    have hout := hp.pointer
    change (outputOperand _ .sha224 $mode $keccak).read s = _ at hout
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine StorePreReadable.of_holds he (ho true) (by x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]) ?_ ?_
      · x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp, hout]
        simpa only [BitVec.add_zero] using hp.$dest $off ($width / 8) (by cases ($keccak) <;> decide)
      · x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp, hout]
        simpa only [BitVec.add_zero, BitVec.add_assoc] using hp.$tables $off ($width / 8) (by cases ($keccak) <;> decide)
    · x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp, hout]
      simpa only [BitVec.add_zero] using hp.$avoids $off (n := $width) _ _ (by cases ($keccak) <;> decide)
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (((copy_image .sha224 $keccak $mode (by simp)).slice $delta (by decide +kernel)) x hx).2
  case boundary =>
    intro s t hp he
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
    exact hp.ne_returnBoundary (by apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]))

def copy224Effect (p base out : BitVec 64) (mode : Mode := .plain) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 (copyOffset .sha224 56 mode)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), ((Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 32).read s).setWidth 64⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
  ] ++ (if mode = .digest then [] else [⟨(Operand.reg 7 : Operand 64), out⟩]) ++ [
    ⟨(Operand.mem (base + 64) : Operand 32), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 32).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 32), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 32).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩]

def copy224PrefixEffect (p base out : BitVec 64) (mode : Mode := .plain) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 (copyOffset .sha224 42 mode)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), ((Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 32).read s).setWidth 64⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
  ] ++ (if mode = .digest then [] else [⟨(Operand.reg 7 : Operand 64), out⟩]) ++ [
    ⟨(Operand.mem (base + 64) : Operand 32), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 32).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩]

attribute [local x86_compose] copy224PrefixEffect

local macro "copy224_prefix_proof " initial:ident _inputs:ident _split:ident out:ident _digest:ident keccak:ident hcode:ident mode:term:max o24:num o16:num a0:term:max o0:num o8:num d22:num d27:num d32:num _d37:num _d42:num _d45:num _d49:num _d53:num _ptr:num pointerLoad:tactic : tactic => `(tactic| (
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR32M32LegacyEffect (callAddress $mode .sha224 $keccak + 5) 0 (.sib 4 none 0 (.d8 $o24))) from
      (mov_r32_m32_legacy_effect_step (callAddress $mode .sha224 $keccak + 5)
        0 (.sib 4 none 0 (.d8 $o24)) (by decide +kernel) rfl rfl)) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact $hcode x ((codeRange_mem_of_take (by decide +kernel)) x hx)
  case pre =>
    intro s hp
    have hsp : (Operand.reg 4 : Operand 64).read s = frameBase $initial .sha224 $mode $keccak := hp.rsp
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp
    refine ⟨hp.rip, ?_⟩
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp]
    exact hp.stackRead $o24 4 (by cases ($keccak) <;> decide)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR32M32LegacyEffect, Effect.components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
    exact hp.ne_returnBoundary (by apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
  copy224_store $keccak $mode (show StepEffect _ _ (copy224StoreEffect (callAddress $mode .sha224 $keccak + 5 + 4) (.sib 4 none 0 (.d8 64))) from
      (mov_m32_r32_legacy_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + 4)
        0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)) 64 4 32 stackRead stack_tables stack_store_avoids
  copy224_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha224 $keccak + 5 + 8) 1 (.sib 4 none 0 (.d8 $o16))) from
      (mov_r64_m64_effect_step (callAddress $mode .sha224 $keccak + 5 + 8) 0x48 (by unfold RexWPrefix; decide +kernel)
        1 (.sib 4 none 0 (.d8 $o16)) (by decide +kernel) rfl rfl)) $o16 8
  copy224_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha224 $keccak + 5 + 13) 1 (.sib 4 none 0 (.d8 56))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + 13) 0x48 (by unfold RexWPrefix; decide +kernel)
        1 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)) 56 13 64 stackRead stack_tables stack_store_avoids
  copy224_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha224 $keccak + 5 + 18) 2 (.sib 4 none 0 $a0)) from
      (mov_r64_m64_effect_step (callAddress $mode .sha224 $keccak + 5 + 18) 0x48 (by unfold RexWPrefix; decide +kernel)
        2 (.sib 4 none 0 $a0) (by decide +kernel) rfl rfl)) $o0 18
  copy224_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha224 $keccak + 5 + $d22) 6 (.sib 4 none 0 (.d8 $o8))) from
      (mov_r64_m64_effect_step (callAddress $mode .sha224 $keccak + 5 + $d22) 0x48 (by unfold RexWPrefix; decide +kernel)
        6 (.sib 4 none 0 (.d8 $o8)) (by decide +kernel) rfl rfl)) $o8 $d22
  copy224_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha224 $keccak + 5 + $d27) 6 (.sib 4 none 0 (.d8 48))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + $d27) 0x48 (by unfold RexWPrefix; decide +kernel)
        6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)) 48 $d27 64 stackRead stack_tables stack_store_avoids
  copy224_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha224 $keccak + 5 + $d32) 2 (.sib 4 none 0 (.d8 40))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + $d32) 0x48 (by unfold RexWPrefix; decide +kernel)
        2 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)) 40 $d32 64 stackRead stack_tables stack_store_avoids
  $pointerLoad
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp : (Operand.reg 4 : Operand 64).read s = frameBase $initial .sha224 $mode $keccak := hp.rsp
  have hout := hp.pointer
  change (outputOperand $initial .sha224 $mode $keccak).read s = $out at hout
  x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp hout
  apply he.weaken
  · x86_norm [Mode.frameSize, copy224PrefixEffect, copyOffset, digestOffset]
  · x86_norm [Mode.frameSize, copy224PrefixEffect, copyOffset, digestOffset, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external, BitVec.setWidth_setWidth_of_le]
  · intro i; cases i <;> x86_norm [Mode.frameSize, copy224PrefixEffect, copyOffset, digestOffset]
  · x86_norm [Mode.frameSize, copy224PrefixEffect, copyOffset, digestOffset, hsp, hout]
))

set_option maxHeartbeats 2400000 in
theorem copy224_prefix_block [Bindings] (initial : RamState) (inputs : Array Input) (split : Nat)
    (out : BitVec 64) (digest : Vector UInt8 28) (keccak : Bool := false)
    (mode : Mode := .plain)
    (hcode : ∀ x ∈ codeRange (callAddress mode .sha224 keccak + 5) (copyBytes .sha224 mode), x ∈ Extracted.programImage)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl)
    :
    AdvanceTriple (returnBoundary initial) (copySteps .sha224 mode - 4)
      (CopyPre initial .sha224 inputs split out digest (keccak := keccak) (mode := mode)) Extracted.programImage
      (Effect.post (copy224PrefixEffect (callAddress mode .sha224 keccak + 5)
        (frameBase initial .sha224 mode keccak) out mode)) := by
  rcases hMode with rfl | rfl
  · copy224_prefix_proof initial inputs split out digest keccak hcode .plain 24 16 .none 0 8 22 27 32 37 42 45 49 53 7 (copy224_load keccak .plain (show StepEffect _ _ (movR64M64Effect (callAddress .plain .sha224 keccak + 5 + 37) 7 (.sib 4 none 0 (.d8 32))) from
      (mov_r64_m64_effect_step (callAddress .plain .sha224 keccak + 5 + 37) 0x48 (by unfold RexWPrefix; decide +kernel)
        7 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)) 32 37)
  · copy224_prefix_proof initial inputs split out digest keccak hcode .digest 32 24 (.d8 8) 8 16 23 28 33 38 38 41 45 49 3 (skip)

local macro "copy224_full_proof " initial:ident inputs:ident split:ident out:ident digest:ident keccak:ident hcode:ident mode:term:max _o24:num _o16:num _a0:term:max _o0:num _o8:num _d22:num _d27:num _d32:num _d37:num d42:num d45:num d49:num d53:num ptr:num _pointerLoad:tactic : tactic => `(tactic| (
  have hPrefix := copy224_prefix_block $initial $inputs $split $out $digest $keccak $mode $hcode (by simp)
  revert hPrefix
  x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
  copy224_store $keccak $mode (show StepEffect _ _ (copy224StoreEffect (callAddress $mode .sha224 $keccak + 5 + $d42) (.base $ptr (.d8 24))) from
      (mov_m32_r32_legacy_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + $d42)
        0 (.base $ptr (.d8 24)) (by decide +kernel) rfl rfl)) 24 $d42 32 outputRead output_tables output_store_avoids
  copy224_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha224 $keccak + 5 + $d45) 1 (.base $ptr (.d8 16))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + $d45) 0x48 (by unfold RexWPrefix; decide +kernel)
        1 (.base $ptr (.d8 16)) (by decide +kernel) rfl rfl)) 16 $d45 64 outputRead output_tables output_store_avoids
  copy224_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha224 $keccak + 5 + $d49) 6 (.base $ptr (.d8 8))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + $d49) 0x48 (by unfold RexWPrefix; decide +kernel)
        6 (.base $ptr (.d8 8)) (by decide +kernel) rfl rfl)) 8 $d49 64 outputRead output_tables output_store_avoids
  copy224_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha224 $keccak + 5 + $d53) 2 (.base $ptr .none)) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha224 $keccak + 5 + $d53) 0x48 (by unfold RexWPrefix; decide +kernel)
        2 (.base $ptr .none) (by decide +kernel) rfl rfl)) 0 $d53 64 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp : (Operand.reg 4 : Operand 64).read s = frameBase $initial .sha224 $mode $keccak := hp.rsp
  have hout := hp.pointer
  change (outputOperand $initial .sha224 $mode $keccak).read s = $out at hout
  x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp hout
  apply he.weaken
  · x86_norm [Mode.frameSize, copy224Effect, copyOffset, digestOffset]
  · x86_norm [Mode.frameSize, copy224Effect, copyOffset, digestOffset, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external, BitVec.setWidth_setWidth_of_le]
  · intro i; cases i <;> x86_norm [Mode.frameSize, copy224Effect, copyOffset, digestOffset]
  · x86_norm [Mode.frameSize, copy224Effect, copyOffset, digestOffset, hsp, hout]
))

set_option maxHeartbeats 2400000 in
theorem copy224_block [Bindings] (initial : RamState) (inputs : Array Input) (split : Nat)
    (out : BitVec 64) (digest : Vector UInt8 28) (keccak : Bool := false)
    (mode : Mode := .plain)
    (hcode : ∀ x ∈ codeRange (callAddress mode .sha224 keccak + 5) (copyBytes .sha224 mode), x ∈ Extracted.programImage)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl)
    :
    AdvanceTriple (returnBoundary initial) (copySteps .sha224 mode)
      (CopyPre initial .sha224 inputs split out digest (keccak := keccak) (mode := mode)) Extracted.programImage
      (Effect.post (copy224Effect (callAddress mode .sha224 keccak + 5)
        (frameBase initial .sha224 mode keccak) out mode)) := by
  rcases hMode with rfl | rfl
  · copy224_full_proof initial inputs split out digest keccak hcode .plain 24 16 .none 0 8 22 27 32 37 42 45 49 53 7 (skip)
  · copy224_full_proof initial inputs split out digest keccak hcode .digest 32 24 (.d8 8) 8 16 23 28 33 38 38 41 45 49 3 (skip)

set_option maxHeartbeats 800000 in
theorem copy224_advance [Bindings] {initial s : RamState} {inputs : Array Input} {split : Nat}
    {keccak : Bool} {mode : Mode} {out : BitVec 64} {digest : Vector UInt8 Variant.sha224.digestBytes}
    (hp : CopyPre initial .sha224 inputs split out digest s keccak mode) :
    ∃ t, Advances (returnBoundary initial) (copySteps .sha224 mode) s t ∧
      CopyPost initial .sha224 out digest s t keccak mode := by
  obtain ⟨t, ht, hr, _, he⟩ := copy224_block initial inputs split out digest keccak mode
    (fun x hx ↦ imageSections_mem_toCodeMap_of_fetchByte ((copy_image .sha224 keccak mode hp.mode) x hx).2)
    hp.mode s hp.invariant.ready hp.invariant.code hp
  refine ⟨t, ht, hp.post_of_effect hr he (hd := by rcases hp.mode with rfl | rfl <;> exact of_decide_eq_true rfl) ?_ ?_ ?_ ?_ ?_⟩
  · intro c hc address ha
    simp only [copy224Effect, Effect.components, List.map_append, List.mem_append,
      List.map_cons, List.map_nil, Write.component_reg, Write.component_mem,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst c; exact ha.elim
    · subst c; exact ha.elim
    · subst c; exact ha.elim
    · subst c; exact ha.elim
    · rcases hp.mode with rfl | rfl <;> simp only [reduceCtorEq, ite_true, ite_false,
        List.map_cons, List.map_nil, Write.component_reg, List.mem_cons,
        List.not_mem_nil, or_false] at h
      subst c; exact ha.elim
    · subst c; exact hp.stack_write (by cases keccak <;> decide) (by cases keccak <;> decide) ha
    · subst c; exact hp.stack_write (by cases keccak <;> decide) (by cases keccak <;> decide) ha
    · subst c; exact hp.stack_write (by cases keccak <;> decide) (by cases keccak <;> decide) ha
    · subst c; exact hp.stack_write (by cases keccak <;> decide) (by cases keccak <;> decide) ha
    · subst c; exact hp.output_write (by cases keccak <;> decide) ha
    · subst c; exact hp.output_write (by cases keccak <;> decide) ha
    · subst c; exact hp.output_write (by cases keccak <;> decide) ha
    · subst c; exact hp.output_write (by cases keccak <;> decide) ha
    · subst c; exact ha.elim
  · rcases hp.mode with rfl | rfl <;>
      simp [copy224Effect, Effect.components, Write.component, Operand.component]
  · intro register hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hp.mode with rfl | rfl <;>
      simp [copy224Effect, Effect.components, Write.component, Operand.component] <;> decide +kernel
  · rcases hp.mode with rfl | rfl <;> exact copy_end .sha224 keccak _ (by simp)
  · have hall := he.writes
    have h24 : memLoad t.external (out + 24) 32 = memLoad s.external
        (frameBase initial .sha224 mode keccak + BitVec.ofNat 64 (digestOffset mode + 24)) 32 := by
      rcases hp.mode with rfl | rfl <;> simp_all [copy224Effect, Write.AllHold, ← memLoad_external]
    have h16 : memLoad t.external (out + 16) 64 = memLoad s.external
        (frameBase initial .sha224 mode keccak + BitVec.ofNat 64 (digestOffset mode + 16)) 64 := by
      rcases hp.mode with rfl | rfl <;> simp_all [copy224Effect, Write.AllHold, ← memLoad_external]
    have h8 : memLoad t.external (out + 8) 64 = memLoad s.external
        (frameBase initial .sha224 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8)) 64 := by
      rcases hp.mode with rfl | rfl <;> simp_all [copy224Effect, Write.AllHold, ← memLoad_external]
    have h0 : memLoad t.external (out + 0) 64 = memLoad s.external
        (frameBase initial .sha224 mode keccak + BitVec.ofNat 64 (digestOffset mode + 0)) 64 := by
      rcases hp.mode with rfl | rfl <;> simp_all [copy224Effect, Write.AllHold, ← memLoad_external]
    intro i
    have hi := i.isLt
    change i.val < 28 at hi
    by_cases h : i.val < 8
    · simpa only [Nat.zero_add, BitVec.add_zero, Fin.getElem_fin] using
        hp.byte_of_load_eq he.agrees.grow 0 64 (by cases keccak <;> decide) h0 i.val h
    · by_cases h' : i.val < 16
      · have hh := hp.byte_of_load_eq he.agrees.grow 8 64 (by cases keccak <;> decide) h8 (i.val - 8) (by omega)
        simpa only [show 8 + (i.val - 8) = i.val by omega, Fin.getElem_fin] using hh
      · by_cases h'' : i.val < 24
        · have hh := hp.byte_of_load_eq he.agrees.grow 16 64 (by cases keccak <;> decide) h16 (i.val - 16) (by omega)
          simpa only [show 16 + (i.val - 16) = i.val by omega, Fin.getElem_fin] using hh
        · have hh := hp.byte_of_load_eq he.agrees.grow 24 32 (by cases keccak <;> decide) h24 (i.val - 24) (by omega)
          simpa only [show 24 + (i.val - 24) = i.val by omega, Fin.getElem_fin] using hh

end Sha3.Proofs.Wrapper.Finish.Plain
