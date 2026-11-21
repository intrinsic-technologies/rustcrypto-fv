import Sha3.Proofs.Wrapper.Finish.Plain.Copy
import Sha3.Proofs.Finalize.Output.Basic
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add

local macro "copy384_load " keccak:term:max mode:term:max step:term:max off:term:max delta:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte
      (((copy_image .sha384 $keccak $mode (by first | exact Or.inl rfl | exact Or.inr rfl)).slice (copyOffset .sha384 $delta $mode) (by decide +kernel)) x hx).2
  case mid =>
    intro s t hp he ho
    have hs := hp.rsp
    have hout := hp.pointer
    change (Operand.reg 4 : Operand 64).read s = _ at hs
    change (outputOperand _ .sha384 $mode $keccak).read s = _ at hout
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize] at hs hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine LoadPre.of_holds he (ho true) (by x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]) (fun _ _ obs => AddrMode.addr_obs obs _ _) ?_
      x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, hs, hout]
      simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.stackRead $off 8 (by cases ($keccak) <;> decide)
    · exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case boundary =>
    intro s t hp he
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]
    exact hp.ne_returnBoundary (by
      apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]))

local macro "copy384_store " keccak:term:max mode:term:max step:term:max off:term:max delta:term:max _kind:ident : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte
      (((copy_image .sha384 $keccak $mode (by first | exact Or.inl rfl | exact Or.inr rfl)).slice (copyOffset .sha384 $delta $mode) (by decide +kernel)) x hx).2
  case mid =>
    intro s t hp he ho
    have hs := hp.rsp
    have hout := hp.pointer
    change (Operand.reg 4 : Operand 64).read s = _ at hs
    change (outputOperand _ .sha384 $mode $keccak).read s = _ at hout
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize] at hs hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine StorePreReadable.of_holds he (ho true) (by x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]) ?_ ?_
      · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, hs, hout]
        first
        | simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.stackRead $off 8 (by cases ($keccak) <;> decide)
        | simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.outputRead $off 8 (by cases ($keccak) <;> decide)
      · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, hs, hout]
        first
        | simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero, BitVec.add_assoc] using hp.stack_tables $off 8 (by cases ($keccak) <;> decide)
        | simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero, BitVec.add_assoc] using hp.output_tables $off 8 (by cases ($keccak) <;> decide)
    · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, hs, hout]
      first
      | simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.stack_store_avoids $off (n := 64) _ _ (by cases ($keccak) <;> decide)
      | simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.output_store_avoids $off (n := 64) _ _ (by cases ($keccak) <;> decide)
  case boundary =>
    intro s t hp he
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]
    exact hp.ne_returnBoundary (by
      apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]))

def copy384Effect (initial : RamState) (out : BitVec 64) (s : RamState) (keccak : Bool := false) (mode : Mode := .plain) : Effect where
  rip := epilogueAddress mode .sha384 keccak
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 40)) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 32)) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩
    ] ++ (if mode = .digest then [] else [⟨(Operand.reg 9 : Operand 64), out⟩]) ++ [
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 56) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 64) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 72) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 80) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 88) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 32)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 32) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 32)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 96) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 40)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 40) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 40)) : Operand 64).read s⟩]

def copy384PrefixEffect (initial : RamState) (out : BitVec 64) (s : RamState) (keccak : Bool := false) (mode : Mode := .plain) : Effect where
  rip := callAddress mode .sha384 keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 64 mode)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 40)) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 32)) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.reg 7 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.reg 8 : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩
    ] ++ (if mode = .digest then [] else [⟨(Operand.reg 9 : Operand 64), out⟩]) ++ [
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 56) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 64) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 72) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 80) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 88) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 32)) : Operand 64).read s⟩,
    ⟨(Operand.mem (frameBase initial .sha384 mode keccak + 96) : Operand 64), (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 40)) : Operand 64).read s⟩]


attribute [local x86_compose] copy384PrefixEffect

local macro "copy384_prefix_block_proof " _initial:term:max _inputs:term:max _split:term:max out:term:max _digest:term:max keccak:term:max mode:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 0 $mode)) 0 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 40))))) from
      mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 0 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 40))))
        (by decide +kernel) rfl rfl) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte
      (((copy_image .sha384 $keccak $mode (by first | exact Or.inl rfl | exact Or.inr rfl)).slice 0 (by decide +kernel)) x hx).2
  case pre =>
    intro s hp
    refine ⟨hp.rip.trans (BitVec.add_zero _).symm, ?_⟩
    have hs := hp.rsp
    change (Operand.reg 4 : Operand 64).read s = _ at hs
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize] at hs
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, hs]
    exact hp.stackRead (digestOffset $mode + 40) 8 (by cases ($keccak) <;> decide)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]
    exact hp.ne_returnBoundary (by
      apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize]
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 5 $mode)) 0 (.sib 4 none 0 (.d8 96))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 5 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 96))
        (by decide +kernel) rfl rfl)
    96 5 stack
  copy384_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 10 $mode)) 1 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 32))))) from
      mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 10 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 32))))
        (by decide +kernel) rfl rfl)
    (digestOffset $mode + 32) 10
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 15 $mode)) 1 (.sib 4 none 0 (.d8 88))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 15 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 88))
        (by decide +kernel) rfl rfl)
    88 15 stack
  copy384_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 20 $mode)) 2 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 24))))) from
      mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 20 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 24))))
        (by decide +kernel) rfl rfl)
    (digestOffset $mode + 24) 20
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 25 $mode)) 2 (.sib 4 none 0 (.d8 80))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 25 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 80))
        (by decide +kernel) rfl rfl)
    80 25 stack
  copy384_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 30 $mode)) 6 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 16))))) from
      mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 30 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 16))))
        (by decide +kernel) rfl rfl)
    (digestOffset $mode + 16) 30
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 35 $mode)) 6 (.sib 4 none 0 (.d8 72))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 35 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 72))
        (by decide +kernel) rfl rfl)
    72 35 stack
  copy384_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 40 $mode)) 7 (.sib 4 none 0 (if $mode = .digest then .d8 8 else .none))) from
      mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 40 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (if $mode = .digest then .d8 8 else .none))
        (by decide +kernel) rfl rfl)
    (digestOffset $mode + 0) 40
  copy384_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 44 $mode)) 8 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 8))))) from
      mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 44 $mode)) 0x4c
        (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset $mode + 8))))
        (by decide +kernel) rfl rfl)
    (digestOffset $mode + 8) 44
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 49 $mode)) 8 (.sib 4 none 0 (.d8 64))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 49 $mode)) 0x4c
        (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 64))
        (by decide +kernel) rfl rfl)
    64 49 stack
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 54 $mode)) 7 (.sib 4 none 0 (.d8 56))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 54 $mode)) 0x48
        (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 56))
        (by decide +kernel) rfl rfl)
    56 54 stack
  first
  | (have : $mode = Mode.plain := rfl
     copy384_load $keccak $mode (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 59 $mode)) 9 (.sib 4 none 0 (.d8 48))) from
           mov_r64_m64_effect_step (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 59 $mode)) 0x4c
             (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 48))
             (by decide +kernel) rfl rfl)
         48 59)
  | skip
  apply AdvanceTriple.block_end
  intro s t hp he
  have hs := hp.rsp
  have hout := hp.pointer
  change (Operand.reg 4 : Operand 64).read s = _ at hs
  change (outputOperand _ .sha384 $mode $keccak).read s = $out at hout
  x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize] at hs hout
  apply he.weaken
  · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384PrefixEffect]
  · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384PrefixEffect, hs, hout, Operand.write_reg_external, Operand.write_mem_external]
  · intro i
    cases i <;> x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384PrefixEffect]
  · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384PrefixEffect, hs, hout]))

set_option maxHeartbeats 1600000 in
theorem copy384_prefix_block [Bindings] (initial : RamState) (inputs : Array Input) (split : Nat)
    (out : BitVec 64) (digest : Vector UInt8 Variant.sha384.digestBytes) (keccak : Bool := false) (mode : Mode := .plain)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl) :
    AdvanceTriple (returnBoundary initial) (13 - if mode = .digest then 1 else 0)
      (CopyPre initial .sha384 inputs split out digest (keccak := keccak) (mode := mode))
      Extracted.programImage
      (Effect.post (copy384PrefixEffect initial out (keccak := keccak) (mode := mode))) := by
  rcases hMode with rfl | rfl
  · copy384_prefix_block_proof initial inputs split out digest keccak Mode.plain
  · copy384_prefix_block_proof initial inputs split out digest keccak Mode.digest

local macro "copy384_block_proof " initial:term:max inputs:term:max split:term:max out:term:max digest:term:max keccak:term:max mode:term:max : tactic => `(tactic| (
  have hPrefix := copy384_prefix_block $initial $inputs $split $out $digest $keccak $mode (by first | exact Or.inl rfl | exact Or.inr rfl)
  revert hPrefix
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 64 $mode)) 0 (.base (if $mode = .digest then 3 else 9) (.d8 40))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 64 $mode)) (if $mode = .digest then 0x48 else 0x49)
        (by unfold RexWPrefix; decide +kernel) 0 (.base (if $mode = .digest then 3 else 9) (.d8 40))
        (by decide +kernel) rfl rfl)
    40 64 output
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 68 $mode)) 1 (.base (if $mode = .digest then 3 else 9) (.d8 32))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 68 $mode)) (if $mode = .digest then 0x48 else 0x49)
        (by unfold RexWPrefix; decide +kernel) 1 (.base (if $mode = .digest then 3 else 9) (.d8 32))
        (by decide +kernel) rfl rfl)
    32 68 output
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 72 $mode)) 2 (.base (if $mode = .digest then 3 else 9) (.d8 24))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 72 $mode)) (if $mode = .digest then 0x48 else 0x49)
        (by unfold RexWPrefix; decide +kernel) 2 (.base (if $mode = .digest then 3 else 9) (.d8 24))
        (by decide +kernel) rfl rfl)
    24 72 output
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 76 $mode)) 6 (.base (if $mode = .digest then 3 else 9) (.d8 16))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 76 $mode)) (if $mode = .digest then 0x48 else 0x49)
        (by unfold RexWPrefix; decide +kernel) 6 (.base (if $mode = .digest then 3 else 9) (.d8 16))
        (by decide +kernel) rfl rfl)
    16 76 output
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 80 $mode)) 8 (.base (if $mode = .digest then 3 else 9) (.d8 8))) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 80 $mode)) (if $mode = .digest then 0x4c else 0x4d)
        (by unfold RexWPrefix; decide +kernel) 0 (.base (if $mode = .digest then 3 else 9) (.d8 8))
        (by decide +kernel) rfl rfl)
    8 80 output
  copy384_store $keccak $mode (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 84 $mode)) 7 (.base (if $mode = .digest then 3 else 9) .none)) from
      mov_m64_r64_effect_step_of_readable (callAddress $mode .sha384 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha384 84 $mode)) (if $mode = .digest then 0x48 else 0x49)
        (by unfold RexWPrefix; decide +kernel) 7 (.base (if $mode = .digest then 3 else 9) .none)
        (by decide +kernel) rfl rfl)
    0 84 output
  apply AdvanceTriple.block_end
  intro s t hp he
  have hs := hp.rsp
  have hout := hp.pointer
  change (Operand.reg 4 : Operand 64).read s = _ at hs
  change (outputOperand _ .sha384 $mode $keccak).read s = $out at hout
  x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize] at hs hout
  apply he.weaken
  · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384Effect, epilogueAddress, callAddress, epilogueOffset, callOffset]
  · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384Effect, hs, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i
    cases i <;> x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384Effect]
  · x86_norm [digestOffset, copyOffset, outputOperand, outputSlot, Mode.outputSlotOffset, Mode.frameSize, copy384Effect, hs, hout]))

set_option maxHeartbeats 1600000 in
theorem copy384_block [Bindings] (initial : RamState) (inputs : Array Input) (split : Nat)
    (out : BitVec 64) (digest : Vector UInt8 Variant.sha384.digestBytes) (keccak : Bool := false) (mode : Mode := .plain)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl) :
    AdvanceTriple (returnBoundary initial) (19 - if mode = .digest then 1 else 0)
      (CopyPre initial .sha384 inputs split out digest (keccak := keccak) (mode := mode))
      Extracted.programImage
      (Effect.post (copy384Effect initial out (keccak := keccak) (mode := mode))) := by
  rcases hMode with rfl | rfl
  · copy384_block_proof initial inputs split out digest keccak Mode.plain
  · copy384_block_proof initial inputs split out digest keccak Mode.digest

set_option maxHeartbeats 1600000 in
theorem copy384_advance [Bindings] {initial s : RamState} {inputs : Array Input}
    {split : Nat} {keccak : Bool} {mode : Mode} {out : BitVec 64} {digest : Vector UInt8 Variant.sha384.digestBytes}
    (hp : CopyPre initial .sha384 inputs split out digest s keccak mode) :
    ∃ t, Advances (returnBoundary initial) (copySteps .sha384 mode) s t ∧
      CopyPost initial .sha384 out digest s t keccak mode := by
  obtain ⟨t, ht, hr, _, he⟩ := copy384_block initial inputs split out digest keccak mode hp.mode s hp.invariant.ready
    (CodeIn.of_loaded hp.invariant.loaded (SectionsLow.codeLow programSections_low)) hp
  refine ⟨t, ht, hp.post_of_effect hr he (hd := by rcases hp.mode with rfl | rfl <;> exact of_decide_eq_true rfl) ?_ ?_ ?_ rfl ?_⟩
  · intro c hc address ha
    simp only [copy384Effect, Effect.components, List.map_append, List.mem_append, List.not_mem_nil, or_false] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · simp only [List.map_cons, List.map_nil, Write.component_reg, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hEq | hEq | hEq | hEq | hEq | hEq
      all_goals subst c; exact ha.elim
    · split at hc <;> simp only [List.map_cons, List.map_nil, Write.component_reg, List.mem_cons, List.not_mem_nil, or_false] at hc
      all_goals first | exact hc.elim | subst c; exact ha.elim
    · simp only [List.map_cons, List.map_nil, Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq <;> subst c
      · exact hp.stack_write (offset := 56) (count := 8) (by cases keccak <;> decide) (by cases keccak <;> decide) ha
      · exact hp.output_write (offset := 0) (count := 8) (by decide) ha
      · exact hp.stack_write (offset := 64) (count := 8) (by cases keccak <;> decide) (by cases keccak <;> decide) ha
      · exact hp.output_write (offset := 8) (count := 8) (by decide) ha
      · exact hp.stack_write (offset := 72) (count := 8) (by cases keccak <;> decide) (by cases keccak <;> decide) ha
      · exact hp.output_write (offset := 16) (count := 8) (by decide) ha
      · exact hp.stack_write (offset := 80) (count := 8) (by cases keccak <;> decide) (by cases keccak <;> decide) ha
      · exact hp.output_write (offset := 24) (count := 8) (by decide) ha
      · exact hp.stack_write (offset := 88) (count := 8) (by cases keccak <;> decide) (by cases keccak <;> decide) ha
      · exact hp.output_write (offset := 32) (count := 8) (by decide) ha
      · exact hp.stack_write (offset := 96) (count := 8) (by cases keccak <;> decide) (by cases keccak <;> decide) ha
      · exact hp.output_write (offset := 40) (count := 8) (by decide) ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst c
      exact ha.elim
  · rcases hp.mode with hm | hm <;> simp [copy384Effect, Effect.components, hm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hEq | hEq | hEq | hEq | hEq | hEq <;> subst r <;> rcases hp.mode with hm | hm <;> simp [copy384Effect, Effect.components, hm] <;> decide +kernel
  · intro i
    have words (j : Nat) (hj : j < 6) :
        memLoad t.external (out + BitVec.ofNat 64 (8 * j)) 64 =
          memLoad s.external (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8 * j)) 64 := by
      have hw := Write.allHold_iff.mp he.writes
      apply hw ⟨(Operand.mem (out + BitVec.ofNat 64 (8 * j)) : Operand 64),
        (Operand.mem (frameBase initial .sha384 mode keccak + BitVec.ofNat 64 (digestOffset mode + 8 * j)) : Operand 64).read s⟩
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [copy384Effect]
    have hh := hp.byte_of_load_eq he.agrees.grow (8 * (i.val / 8)) 64
      (by have := i.isLt; change i.val < 48 at this; change 8 * (i.val / 8) + 8 ≤ 48; omega)
      (words (i.val / 8) (by have := i.isLt; change i.val < 48 at this; omega))
      (i.val % 8) (by omega)
    simpa only [Fin.getElem_fin, show 8 * (i.val / 8) + i.val % 8 = i.val by omega] using hh

end Sha3.Proofs.Wrapper.Finish.Plain
