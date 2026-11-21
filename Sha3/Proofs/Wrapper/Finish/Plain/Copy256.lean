import Sha3.Proofs.Wrapper.Finish.Plain.Copy
import Sha3.Proofs.Finalize.Output.Basic
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add

local macro "copy256_load " mode:term:max keccak:term:max step:term:max off:term:max delta:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hsp := hp.rsp
    change (Operand.reg 4 : Operand 64).read s = _ at hsp
    x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]) (fun _ _ obs => AddrMode.addr_obs obs _ _) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _⟩
    x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp]
    simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.stackRead $off 8 (by cases ($keccak) <;> decide)
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (((copy_image .sha256 $keccak $mode (by first | exact Or.inl rfl | exact Or.inr rfl)).slice (copyOffset .sha256 $delta $mode) (by decide +kernel)) x hx).2
  case boundary =>
    intro s t hp he
    x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
    exact hp.ne_returnBoundary (by apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]))

local macro "copy256_store " mode:term:max keccak:term:max step:term:max off:term:max delta:term:max dest:ident tables:ident avoids:ident : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case mid =>
    intro s t hp he ho
    have hsp := hp.rsp
    change (Operand.reg 4 : Operand 64).read s = _ at hsp
    have hout := hp.pointer
    skip
    x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset] at hsp hout
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_⟩
    · refine StorePreReadable.of_holds he (ho true) (by x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]) ?_ ?_
      · x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp, hout]
        simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.$dest $off 8 (by cases ($keccak) <;> decide)
      · x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp, hout]
        simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero, BitVec.add_assoc] using hp.$tables $off 8 (by cases ($keccak) <;> decide)
    · x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, hsp, hout]
      simpa only [digestOffset, reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.zero_add, BitVec.add_zero] using hp.$avoids $off (n := 64) _ _ (by cases ($keccak) <;> decide)
  case sub =>
    intro x hx
    exact imageSections_mem_toCodeMap_of_fetchByte (((copy_image .sha256 $keccak $mode (by first | exact Or.inl rfl | exact Or.inr rfl)).slice (copyOffset .sha256 $delta $mode) (by decide +kernel)) x hx).2
  case boundary =>
    intro s t hp he
    x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]
    exact hp.ne_returnBoundary (by apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [digestOffset, Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset]))

def copy256Effect (p base out : BitVec 64) (s : RamState) (mode : Mode := .plain) : Effect where
  rip := p + BitVec.ofNat 64 (copyOffset .sha256 59 mode)
  writes := [
    ⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.reg 1 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.reg 2 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.reg 6 : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ] ++ (if mode = .digest then [] else [⟨(Operand.reg 7 : Operand 64), out⟩]) ++ [
    ⟨(Operand.mem (base + 64) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 56) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 48) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (base + 40) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 24) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 24)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 16) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 16)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 8) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 8)) : Operand 64).read s⟩,
    ⟨(Operand.mem (out + 0) : Operand 64), (Operand.mem (base + BitVec.ofNat 64 (digestOffset mode + 0)) : Operand 64).read s⟩]

local macro "copy256_block_proof " initial:term:max keccak:term:max mode:term:max hcode:term:max : tactic => `(tactic| (
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha256 $keccak + 5) 0 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (24 + digestOffset $mode))))) from
      (mov_r64_m64_effect_step (callAddress $mode .sha256 $keccak + 5) 0x48 (by unfold RexWPrefix; decide +kernel)
        0 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (24 + digestOffset $mode)))) (by decide +kernel) rfl rfl)) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact $hcode x ((codeRange_mem_of_take (by decide +kernel)) x hx)
  case pre =>
    intro s hp
    have hsp : (Operand.reg 4 : Operand 64).read s = frameBase $initial .sha256 $mode $keccak := hp.rsp
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps] at hsp
    refine ⟨hp.rip, ?_⟩
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps, hsp]
    exact hp.stackRead (24 + digestOffset $mode) 8 (by cases ($keccak) <;> decide)
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR64M64Effect_components, Component.Covers]) _
  case boundary =>
    intro s hp
    x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps]
    exact hp.ne_returnBoundary (by apply Permutation.inProgram_permutation_address <;> cases ($keccak) <;> decide +kernel)
  case' k => x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps]
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 5 $mode)) 0 (.sib 4 none 0 (.d8 64))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 5 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)) 64 5 stackRead stack_tables stack_store_avoids
  copy256_load $mode $keccak (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 10 $mode)) 1 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (16 + digestOffset $mode))))) from
      (mov_r64_m64_effect_step (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 10 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        1 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (16 + digestOffset $mode)))) (by decide +kernel) rfl rfl)) (16 + digestOffset $mode) 10
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 15 $mode)) 1 (.sib 4 none 0 (.d8 56))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 15 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        1 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)) 56 15 stackRead stack_tables stack_store_avoids
  copy256_load $mode $keccak (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 20 $mode)) 2 (.sib 4 none 0 (if $mode = .digest then .d8 8 else .none))) from
      (mov_r64_m64_effect_step (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 20 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        2 (.sib 4 none 0 (if $mode = .digest then .d8 8 else .none)) (by decide +kernel) rfl rfl)) (0 + digestOffset $mode) 20
  copy256_load $mode $keccak (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 24 $mode)) 6 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (8 + digestOffset $mode))))) from
      (mov_r64_m64_effect_step (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 24 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        6 (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (8 + digestOffset $mode)))) (by decide +kernel) rfl rfl)) (8 + digestOffset $mode) 24
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 29 $mode)) 6 (.sib 4 none 0 (.d8 48))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 29 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        6 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)) 48 29 stackRead stack_tables stack_store_avoids
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 34 $mode)) 2 (.sib 4 none 0 (.d8 40))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 34 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        2 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)) 40 34 stackRead stack_tables stack_store_avoids
  first
  | (have : $mode = Mode.plain := rfl
     copy256_load $mode $keccak (show StepEffect _ _ (movR64M64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 39 $mode)) 7 (.sib 4 none 0 (.d8 32))) from
           (mov_r64_m64_effect_step (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 39 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
             7 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)) 32 39)
  | skip
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 44 $mode)) 0 (.base (if $mode = .digest then 3 else 7) (.d8 24))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 44 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        0 (.base (if $mode = .digest then 3 else 7) (.d8 24)) (by decide +kernel) rfl rfl)) 24 44 outputRead output_tables output_store_avoids
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 48 $mode)) 1 (.base (if $mode = .digest then 3 else 7) (.d8 16))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 48 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        1 (.base (if $mode = .digest then 3 else 7) (.d8 16)) (by decide +kernel) rfl rfl)) 16 48 outputRead output_tables output_store_avoids
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 52 $mode)) 6 (.base (if $mode = .digest then 3 else 7) (.d8 8))) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 52 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        6 (.base (if $mode = .digest then 3 else 7) (.d8 8)) (by decide +kernel) rfl rfl)) 8 52 outputRead output_tables output_store_avoids
  copy256_store $mode $keccak (show StepEffect _ _ (movM64R64Effect (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 56 $mode)) 2 (.base (if $mode = .digest then 3 else 7) .none)) from
      (mov_m64_r64_effect_step_of_readable (callAddress $mode .sha256 $keccak + 5 + BitVec.ofNat 64 (copyOffset .sha256 56 $mode)) 0x48 (by unfold RexWPrefix; decide +kernel)
        2 (.base (if $mode = .digest then 3 else 7) .none) (by decide +kernel) rfl rfl)) 0 56 outputRead output_tables output_store_avoids
  apply AdvanceTriple.block_end
  intro s t hp he
  have hsp : (Operand.reg 4 : Operand 64).read s = frameBase $initial .sha256 $mode $keccak := hp.rsp
  have hout := hp.pointer
  skip
  x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps] at hsp hout
  apply he.weaken
  · x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps, copy256Effect]
  · x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps, copy256Effect, hsp, hout, hp.load_output_store, hp.load_output_store_zero,
      Operand.write_reg_external, Operand.write_mem_external]
  · intro i; cases i <;> x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps, copy256Effect]
  · x86_norm [Mode.frameSize, outputOperand, outputSlot, Mode.outputSlotOffset, copyOffset, digestOffset, copySteps, copy256Effect, hsp, hout]
))

set_option maxHeartbeats 2400000 in
theorem copy256_block [Bindings] (initial : RamState) (inputs : Array Input) (split : Nat)
    (out : BitVec 64) (digest : Vector UInt8 32) (keccak : Bool := false) (mode : Mode := .plain)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl)
    (hcode : ∀ x ∈ codeRange (callAddress mode .sha256 keccak + 5) (copyBytes .sha256 mode), x ∈ Extracted.programImage)
    :
    AdvanceTriple (returnBoundary initial) (copySteps .sha256 mode)
      (CopyPre initial .sha256 inputs split out digest (keccak := keccak) (mode := mode)) Extracted.programImage
      (Effect.post (copy256Effect (callAddress mode .sha256 keccak + 5)
        (frameBase initial .sha256 mode keccak) out (mode := mode))) := by
  rcases hMode with rfl | rfl
  · copy256_block_proof initial keccak Mode.plain hcode
  · copy256_block_proof initial keccak Mode.digest hcode

local macro "copy256_advance_proof " initial:term:max s:term:max inputs:term:max split:term:max out:term:max digest:term:max keccak:term:max mode:term:max hp:term:max : tactic => `(tactic| (
  obtain ⟨t, ht, hr, _, he⟩ := copy256_block $initial $inputs $split $out $digest $keccak $mode ($hp).mode
    (fun x hx ↦ imageSections_mem_toCodeMap_of_fetchByte ((copy_image .sha256 $keccak $mode ($hp).mode) x hx).2)
    $s ($hp).invariant.ready ($hp).invariant.code $hp
  refine ⟨t, ht, ($hp).post_of_effect hr he ?_ ?_ ?_ ?_ ?_⟩
  · intro c hc address ha
    simp only [copy256Effect, Effect.components, List.map_cons, List.map_nil, List.map_append, List.mem_append, ite_true, ite_false, reduceCtorEq,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    repeat' (rcases hc with hc | hc)
    all_goals first
      | exact ha.elim
      | exact ($hp).stack_write (by cases ($keccak) <;> decide) (by cases ($keccak) <;> decide) ha
      | exact ($hp).output_write (by cases ($keccak) <;> decide) ha
  · simp [copy256Effect, Effect.components, Write.component, Operand.component]
  · intro register hregister
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hregister
    repeat' (rcases hregister with hregister | hregister)
    all_goals simp only [Effect.components, copy256Effect, BitVec.ofNat_eq_ofNat,
      Nat.add_zero, reduceCtorEq, ↓reduceIte, List.cons_append, List.nil_append,
      BitVec.add_zero, List.map_cons, Write.component, Operand.component, Nat.reduceDiv,
      List.map_nil, List.append_nil, List.mem_cons, Component.reg.injEq,
      List.not_mem_nil, or_self, or_false, not_or] <;> decide +kernel
  · exact copy_end .sha256 $keccak $mode ($hp).mode
  · have hall := he.writes
    simp only [copy256Effect, Write.AllHold, List.cons_append, List.nil_append, List.append_nil, ite_true, ite_false, reduceCtorEq, ← memLoad_external] at hall
    first
    | obtain ⟨_, _, _, _, _, _, _, _, _, h24, h16, h8, h0⟩ := hall
    | obtain ⟨_, _, _, _, _, _, _, _, h24, h16, h8, h0⟩ := hall
    intro i
    have hi := i.isLt
    change i.val < 32 at hi
    by_cases h : i.val < 8
    · simpa only [Fin.getElem_fin, Nat.zero_add, BitVec.add_zero] using
        ($hp).byte_of_load_eq he.agrees.grow 0 64 (by cases ($keccak) <;> decide) h0 i.val h
    · by_cases h' : i.val < 16
      · have hh := ($hp).byte_of_load_eq he.agrees.grow 8 64 (by cases ($keccak) <;> decide) h8 (i.val - 8) (by omega)
        simpa only [Fin.getElem_fin, show 8 + (i.val - 8) = i.val by omega] using hh
      · by_cases h'' : i.val < 24
        · have hh := ($hp).byte_of_load_eq he.agrees.grow 16 64 (by cases ($keccak) <;> decide) h16 (i.val - 16) (by omega)
          simpa only [Fin.getElem_fin, show 16 + (i.val - 16) = i.val by omega] using hh
        · have hh := ($hp).byte_of_load_eq he.agrees.grow 24 64 (by cases ($keccak) <;> decide) h24 (i.val - 24) (by omega)
          simpa only [Fin.getElem_fin, show 24 + (i.val - 24) = i.val by omega] using hh

))

set_option maxHeartbeats 1600000 in
theorem copy256_advance [Bindings] {initial s : RamState} {inputs : Array Input} {split : Nat}
    {keccak : Bool} {mode : Mode} {out : BitVec 64} {digest : Vector UInt8 Variant.sha256.digestBytes}
    (hp : CopyPre initial .sha256 inputs split out digest s keccak mode) :
    ∃ t, Advances (returnBoundary initial) (copySteps .sha256 mode) s t ∧
      CopyPost initial .sha256 out digest s t keccak mode := by
  rcases hp.mode with hMode | hMode <;> subst mode
  · copy256_advance_proof initial s inputs split out digest keccak Mode.plain hp
  · copy256_advance_proof initial s inputs split out digest keccak Mode.digest hp

end Sha3.Proofs.Wrapper.Finish.Plain
