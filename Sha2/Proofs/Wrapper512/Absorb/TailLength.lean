import Sha2.Proofs.Common.Instructions.ByteStore
import Sha2.Proofs.Common.Instructions.ByteStore.Legacy
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Dispatch.Run
import Sha2.Proofs.Wrapper512.Machine.Stages.Stack

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

def lengthOffset (v : Variant) (large : Bool) (form : Form := .slices) : Nat :=
  match form with
  | .slices | .digest => if large then 0x1e0 else 0x10a
  | .reset stage =>
    if stage.val = 0 then (if large then 0x1db else 0x113)
    else if stage.val = 1 then (if large then 0x388 else 0x2c0)
    else (match v with | .sha384 => 32 | .sha512 => 64 | _ => 0) +
      (if large then 0x6d0 else 0x60c)
  | .finalizeIntoReset false => if large then 0x1d7 else 0x107
  | .finalizeIntoReset true =>
    match v with
    | .sha384 => if large then 0x53c else 0x470
    | .sha512 => if large then 0x55c else 0x490
    | _ => if large then 0x51d else 0x451
  | .traitFinalizeIntoReset false => if large then 0x223 else 0x124
  | .traitFinalizeIntoReset true =>
    (match v with | .sha384 => 32 | .sha512 => 64 | _ => 0) +
      (if large then 0x5e0 else 0x4e3)

def lengthPC (v : Variant) (large : Bool) (form : Form := .slices) : BitVec 64 :=
  v.pc (lengthOffset v large form) form

def lengthRegister (large : Bool) (form : Form := .slices) : BitVec 5 :=
  match form with
  | .slices | .digest => if large then 5 else 3
  | .reset stage => if stage.val = 0 then (if large then 3 else 5) else (if large then 5 else 14)
  | .finalizeIntoReset second => if second then (if large then 5 else 13) else (if large then 3 else 5)
  | .traitFinalizeIntoReset second => if second then (if large then 14 else 12) else (if large then 12 else 14)

def lengthMode (form : Form) : AddrMode :=
  .sib 4 none 0 (match form with
    | .reset _ => .d8 127
    | _ => .d32 (BitVec.ofNat 32 (form.frameBytes - form.activeMemory.tail)))

def lengthCode (large : Bool) (form : Form := .slices) : List UInt8 :=
  (if lengthRegister large form = 3 then [] else
    [if (lengthRegister large form).toNat < 8 then 0x40 else 0x44]) ++
  [0x88, (lengthMode form).modrm ((lengthRegister large form).setWidth 3)] ++ (lengthMode form).tail

def lengthSize (large : Bool) (form : Form := .slices) : Nat := (lengthCode large form).length

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem store_length_step [Bindings] (v : Variant) (large : Bool) (form : Form := .slices) :
    StepEffect (StorePre (lengthPC v large form) (lengthSize large form)
      (fun s => rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail)) 1)
      (codeRange (lengthPC v large form) (lengthCode large form))
      (storeEffect (lengthPC v large form) (lengthSize large form)
        (fun s => rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail))
        (fun s => (Operand.reg (lengthRegister large form) : Operand 8).read s)) := by
  generalize lengthPC v large form = p
  cases large <;> cases form with
  | reset stage =>
    rcases stage with ⟨_ | _ | _ | n, h⟩
    all_goals try omega
    all_goals dsimp [lengthSize, lengthCode, lengthRegister, lengthMode, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory]
    all_goals first
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> first
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
  | slices | digest =>
    first
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 143)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 159)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 367)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_legacy_effect_step _ 3 (by decide) (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 4 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl
    | exact mov_m8_r8_effect_step _ 0x44 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d32 335)) (by decide +kernel) rfl rfl

theorem length_bytes (v : Variant) (large : Bool) (form : Form) (hd : form ≠ .digest) : Extracted.textBytes.toListFrom
    (v.textOffset form + lengthOffset v large form) (lengthSize large form) = lengthCode large form := by
  cases v <;> cases large <;> cases form with
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel
theorem length_bound (v : Variant) (large : Bool) (form : Form) (hd : form ≠ .digest) : v.textOffset form + lengthOffset v large form + lengthSize large form < 71757 := by
  cases v <;> cases large <;> cases form with
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel

set_option maxRecDepth 2048 in
theorem store_length_local [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form)
    (input : Preserved v initial s form) (large : Bool)
    (rip : s.RIP = lengthPC v large form) (hd : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧
      t.RIP = lengthPC v large form + BitVec.ofNat 64 (lengthSize large form) ∧
      t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? =
        some (UInt8.ofNat ((Operand.reg (lengthRegister large form) : Operand 8).read s).toNat) ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1, .rip] s t ∧
      Advances (returnBoundary initial) 1 s t := by
  have bytes := length_bytes v large form hd
  have codeBound := length_bound v large form hd
  have tail_stack : form.activeMemory.tail ≤ (v.routine form).minStackBytes := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have tail_pos : 1 ≤ form.activeMemory.tail := by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide
  have addr : rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail) = stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail := by
    change stackPtr s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail) = _
    rw [input.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    cases form <;> rfl
  have writable : MemWritable s (rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail)) 1 := by
    rw [addr]
    have readable := Dispatch.stack_sub_readable512 ctx (offset := form.activeMemory.tail) (len := 1)
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)
    apply MemWritable.of_not_reserved (by decide) readable.low
      (fun j hj => input.allocated _ (readable.mem j hj))
    intro j hj reserved
    exact (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes) (by cases form <;> simp [Variant.writeRegions, Form.writeRegionCount, Form.twoOutputs])).2 _
      (stackRegion_contains_sub ctx.stack.2.2.1 (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, Variant.routine, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory] <;> decide)
        (show (Component.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1).Covers _ from ⟨j,hj,rfl⟩))
      (.inr reserved)
  have apart : RangeApart (rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail)) 1 (lengthPC v large form) (lengthSize large form) := by
    rw [addr]
    exact Machine.Stages.stack_slot_codeApart ctx (offset := form.activeMemory.tail)
      (len := 1) (codeOffset := v.textOffset form + lengthOffset v large form)
      (codeLen := lengthSize large form) tail_stack (by omega) (Nat.le_of_lt codeBound)
  have code : CodeIn (codeRange (lengthPC v large form) (lengthCode large form)) s := by
    exact programText_slice (programLoaded_codeIn input.loaded)
      (v.textOffset form + lengthOffset v large form) _ (Nat.le_of_lt codeBound) bytes
  have nextState : lengthPC v large form + BitVec.ofNat 64 (lengthSize large form) ≠
      (returnBoundary initial).rip := by
    apply boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    change InProgram (Extracted.textAddress + BitVec.ofNat 64
      (v.textOffset form + lengthOffset v large form) + BitVec.ofNat 64 (lengthSize large form))
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ codeBound
  obtain ⟨t, run, ready, effect⟩ := (store_length_step v large form).advances
    (supportedMachine_readyToStep input.machine) code ⟨rip, writable, apart⟩ nextState
  have frame := effect.agrees
  simp only [storeEffect_components] at frame
  rw [addr] at frame
  refine ⟨t, preserved_of_agrees ctx input run ready frame ?_ (by simp),
    effect.rip, ?_, frame, run⟩
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases form with
      | slices => exact local_memory (form := .slices) (by decide) (by decide) (.inr (by decide)) a ha
      | digest => exact local_memory (form := .digest) (by decide) (by decide) (.inr (by decide)) a ha
      | reset stage =>
        exact local_memory (form := .reset stage) (by change 297 ≤ 976; decide) (by change 49 ≤ 297; decide)
          (by
            dsimp only
            simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
            intro slot hs
            rcases hs with rfl | rfl | rfl | rfl
            · dsimp only [Form.outputSlot]; split <;> simp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory] <;> unfold OffsetsApart <;> decide +kernel
            all_goals simp only [Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot]; unfold OffsetsApart; decide +kernel) a ha
      | finalizeIntoReset second =>
        cases second
        · exact local_memory (form := .finalizeIntoReset false) (by decide) (by decide) (by
            dsimp only
            simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
            intro slot hs
            rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
        · exact local_memory (form := .finalizeIntoReset true) (by decide) (by decide) (by
            dsimp only
            simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
            intro slot hs
            rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
      | traitFinalizeIntoReset second =>
        cases second
        · exact local_memory (form := .traitFinalizeIntoReset false) (by decide) (by decide) (by
            dsimp only
            simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
            intro slot hs
            rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
        · exact local_memory (form := .traitFinalizeIntoReset true) (by decide) (by decide) (by
            dsimp only
            simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
            intro slot hs
            rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha

    · exact ha.elim
  · have value := effect.writes
    change memLoad t.external (rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail)) 8 = _ at value
    have allocated : ∀ i < 1, (t.external[rspOf s + BitVec.ofNat 64 (form.frameBytes - form.activeMemory.tail) + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      exact effect.agrees.grow _ (writable.mem i hi)
    have byte := Bytes.of_memLoad (n := 8) allocated 0 (by decide)
    rw [value] at byte
    simpa only [BitVec.add_zero, addr, storedByte, Nat.mul_zero, Nat.shiftRight_zero] using byte

theorem store_length [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form)
    (input : Preserved v initial s form) (large : Bool)
    (rip : s.RIP = lengthPC v large form) (hd : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧
      t.RIP = lengthPC v large form + BitVec.ofNat 64 (lengthSize large form) ∧
      t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? =
        some (UInt8.ofNat ((Operand.reg (lengthRegister large form) : Operand 8).read s).toNat) ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail) 1, .rip] s t := by
  obtain ⟨t, preserved, rip, value, frame, _⟩ := store_length_local ctx input large rip hd
  exact ⟨t, preserved, rip, value, frame⟩

end Sha2.Proofs.Wrapper512.Absorb
