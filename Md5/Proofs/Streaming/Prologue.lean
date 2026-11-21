import Md5.Proofs.Streaming.Slices
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Frame
import Md5.Proofs.Block.Push
import Md5.Proofs.Buffered.Invariant
import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Rounds.Store.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import Md5.Proofs.Streaming.Instructions
import Md5.Proofs.Streaming.Memory

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

structure PrologueFrame (entry : BitVec 64) (budget : Nat) (s : RamState) : Prop where
  rip : s.RIP = entry
  stack : Stack.Valid s budget
  avoids : (Stack.region s budget).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)

def prologueChanges (initial : RamState) (budget : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 4, .reg 5, .reg 12, .reg 14, .reg 15, .flags, .rip,
    .mem (BitVec.ofNat 64 (Stack.region initial budget).start) budget]

structure PrologueStorage (frame context outputSlot pointerSlot lengthSlot budget : Nat)
    (outputRegister : Syntax.Reg) (initial final : RamState) : Prop where
  rsp : stackPtr final = stackPtr initial - BitVec.ofNat 64 (48 + frame)
  saved : ∀ i : Fin 6,
    (Operand.mem (stackPtr final + BitVec.ofNat 64 (frame + 8 * i.val)) : Operand 64).read final =
      (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val] : Operand 64).read initial
  output : (Operand.mem (stackPtr final + BitVec.ofNat 64 outputSlot) : Operand 64).read final =
    initial.regValue outputRegister
  pointer : (Operand.mem (stackPtr final + BitVec.ofNat 64 pointerSlot) : Operand 64).read final =
    initial.regValue .rdi
  length : (Operand.mem (stackPtr final + BitVec.ofNat 64 lengthSlot) : Operand 64).read final =
    initial.regValue .rdx
  returnSlot :
    (Operand.mem (stackPtr final + BitVec.ofNat 64 (frame + 48)) : Operand 64).read final =
      (Operand.mem (stackPtr initial) : Operand 64).read initial

structure PrologueCommon (frame context outputSlot pointerSlot lengthSlot budget : Nat)
    (outputRegister : Syntax.Reg) (initial final : RamState) : Prop extends
    PrologueStorage frame context outputSlot pointerSlot lengthSlot budget outputRegister
      initial final where
  absorbed : Buffered.Absorbed (stackPtr final + BitVec.ofNat 64 context) ByteArray.empty final
  agrees : AgreesExcept (prologueChanges initial budget) initial final
  memoryFrame : MemoryWriteFrame initial final #v[Stack.region initial budget]

structure SlicesProloguePost (initial : RamState) (inputs : Array Slices.Input)
    (final : RamState) : Prop extends
    PrologueCommon 296 192 168 176 184 OneMessage.digestSlices.minStackBytes .rcx initial final where
  rip : final.RIP = if inputs.size = 0 then 0x10042b else 0x10033d
  index : inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read final = 0
  count : inputs.size ≠ 0 →
    (Operand.reg 12 : Operand 64).read final = BitVec.ofNat 64 inputs.size

structure ResetProloguePost (initial : RamState) (inputs : Array Slices.Input)
    (first : Nat) (final : RamState) : Prop extends
    PrologueCommon 328 8 184 200 208 TwoMessages.digestSlicesReset.minStackBytes .r8 initial final where
  rip : final.RIP = if min first inputs.size = 0 then 0x1007a6 else 0x1006b8
  total : (Operand.mem (stackPtr final + 192) : Operand 64).read final =
    BitVec.ofNat 64 inputs.size
  bound : (Operand.reg 5 : Operand 64).read final = BitVec.ofNat 64 (min first inputs.size)
  count : (Operand.reg 12 : Operand 64).read final = BitVec.ofNat 64 inputs.size
  index : min first inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read final = 0
  empty : min first inputs.size = 0 →
    (Operand.reg 0 : Operand 64).read final = 0 ∧ (Operand.reg 14 : Operand 64).read final = 0

theorem PrologueFrame.slot_toNat {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset : Nat) (ho : offset ≤ budget) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
  have hstack := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hstack
  have hlt := (stackPtr s).isLt
  have hoffset : offset < 2^64 := Nat.lt_of_le_of_lt (Nat.le_trans ho hstack) hlt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset]
  omega

theorem PrologueFrame.slot_contains {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) (i : Nat) (hi : i < len) :
    (Stack.region s budget).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  have hb := h.stack.1
  have hu := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  change (stackPtr s).toNat - budget +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
  rw [BitVec.toNat_add, h.slot_toNat offset ho, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (stackPtr s).toNat - budget ≤ _ ∧
    _ < (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  constructor <;> omega

theorem PrologueFrame.writable {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) :
    Memory.MemWritable s (stackPtr s - BitVec.ofNat 64 offset) len := by
  refine ⟨?_, ?_, ?_⟩
  · have hb := h.stack.1
    have hu := h.stack.2.2.1
    change budget ≤ (stackPtr s).toNat at hu
    rw [h.slot_toNat offset ho]
    change (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
    omega
  · intro i hi
    exact Option.isSome_iff_exists.mpr (h.stack.2.1 _ (h.slot_contains offset len ho hl i hi))
  · intro i hi hin
    exact h.avoids _ (h.slot_contains offset len ho hl i hi) (.inr hin)

theorem PrologueFrame.avoids_mem {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) :
    ∀ x ∈ Extracted.programImage,
      ¬ (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers x.1 := by
  intro x hx ⟨i, hi, he⟩
  apply h.avoids x.1
  · rw [he]
    exact h.slot_contains offset len ho hl i hi
  · exact .inl ⟨x.2, hx⟩

theorem prologue_text_sub (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count), x ∈ Extracted.programImage := by
  intro x hx
  rw [← chunked_toList_slice _ _ _ h] at hx
  exact List.mem_flatMap.mpr ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp only [Extracted.programSections, List.mem_cons, true_or],
    codeRange_slice_subset _ _ offset count x hx⟩

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read pushAddr pushR64Effect pushEffect
  BitVec.sub_eq_add_neg

private theorem pushR64Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (pushR64Effect p len src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [pushR64Effect, pushEffect, pushAddr, stackPtr_read, h.read_reg]
  · exact congrArg some hi
  · simp [pushR64Effect, pushEffect, Write.Full, Operand.Full]

attribute [local x86_local] pushR64Effect_local

def prologuePushBytes : List UInt8 := [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53]

def prologuePushEffect (entry : BitVec 64) (s : RamState) : Effect where
  rip := entry + 10
  writes :=
    [⟨(.mem (stackPtr s - 8) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 16) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 32) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 40) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
     ⟨(.reg 4 : Operand 64), stackPtr s - 48⟩,
     ⟨(.mem (stackPtr s - 48) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]

macro "push_mid " offset:term "," sub:term : tactic => `(tactic| (
  intro s t h hE hO
  have hsp : pushAddr t = stackPtr s - BitVec.ofNat 64 $offset := by
    rw [pushAddr, stackPtr_read, ← (hO true).read_reg]
    x86_norm
  refine ⟨⟨hE.rip, ?_⟩, ?_⟩
  · rw [hsp]
    exact (h.writable $offset 8 (by omega) (by decide)).of_holds hE
  · intro x hx c hc hcov
    have hrange := h.avoids_mem $offset 8 (by omega) (by decide)
    have hsub := $sub
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc <;> subst c
    · exact hcov
    · rw [hsp] at hcov
      exact hrange x (hsub x hx) hcov
    · exact hcov))

set_option maxRecDepth 2048 in
theorem prologue_pushes [Bindings] (boundary : ReturnBoundary) (entry : BitVec 64)
    (budget : Nat) (hBudget : 48 ≤ budget)
    (hSub : ∀ x ∈ codeRange entry prologuePushBytes, x ∈ Extracted.programImage)
    (hBoundary : ∀ i : Nat, i ≤ 10 → entry + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PrologueFrame entry budget s)
      (codeRange entry prologuePushBytes) (prologuePushEffect entry) := by
  unfold prologuePushBytes at hSub ⊢
  md5_run_begin (Block.push_r64_effect_step entry 0x55 (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 8 8 (by omega) (by decide)⟩
  case av =>
    intro s h x hx c hc hcov
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · exact h.avoids_mem 8 8 (by omega) (by decide) x
        (hSub x hx) hcov
    · exact hcov
  case boundary => intro _ _; simpa only [pushR64Effect, pushEffect, BitVec.add_assoc, BitVec.reduceAdd] using hBoundary 1 (by decide)
  md5_run_then (Block.push_r64_rex_effect_step (entry + 1) 0x41 0x57
    (by unfold RexPrefix; decide) (by decide))
  case mid => push_mid 16, hSub
  case boundary => intro _ _; simpa only [pushR64Effect, pushEffect, BitVec.add_assoc, BitVec.reduceAdd] using hBoundary 3 (by decide)
  md5_run_then (Block.push_r64_rex_effect_step (entry + 3) 0x41 0x56
    (by unfold RexPrefix; decide) (by decide))
  case mid => push_mid 24, hSub
  case boundary => intro _ _; simpa only [pushR64Effect, pushEffect, BitVec.add_assoc, BitVec.reduceAdd] using hBoundary 5 (by decide)
  md5_run_then (Block.push_r64_rex_effect_step (entry + 5) 0x41 0x55
    (by unfold RexPrefix; decide) (by decide))
  case mid => push_mid 32, hSub
  case boundary => intro _ _; simpa only [pushR64Effect, pushEffect, BitVec.add_assoc, BitVec.reduceAdd] using hBoundary 7 (by decide)
  md5_run_then (Block.push_r64_rex_effect_step (entry + 7) 0x41 0x54
    (by unfold RexPrefix; decide) (by decide))
  case mid => push_mid 40, hSub
  case boundary => intro _ _; simpa only [pushR64Effect, pushEffect, BitVec.add_assoc, BitVec.reduceAdd] using hBoundary 9 (by decide)
  md5_run_then (Block.push_r64_effect_step (entry + 9) 0x53 (by decide))
  case mid => push_mid 48, hSub
  case boundary => intro _ _; simpa only [pushR64Effect, pushEffect, BitVec.add_assoc, BitVec.reduceAdd] using hBoundary 10 (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [prologuePushEffect]
  · x86_norm [prologuePushEffect]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [prologuePushEffect]
  · x86_norm [prologuePushEffect]

theorem PrologueFrame.apart {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) (p : BitVec 64) (bytes : List UInt8)
    (hSub : ∀ x ∈ codeRange p bytes, x ∈ Extracted.programImage) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len p bytes.length := by
  intro i hi j hj he
  exact h.avoids_mem offset len ho hl _ (hSub _ (mem_codeRange p bytes j hj))
    ⟨i, hi, he.symm⟩

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_compose] movM8Imm8Effect subR64Imm32Effect
attribute [local x86_local] movM8Imm8Effect_local

def slicesInitBytes : List UInt8 := [
    0x48, 0x81, 0xec, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8c, 0x24, 0xa8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xbc, 0x24, 0xb0,
    0x00, 0x00, 0x00, 0x48, 0xb8, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0x48,
    0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0xb8, 0x01, 0x23, 0x45, 0x67, 0x89,
    0xab, 0xcd, 0xef, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xc7, 0x84,
    0x24, 0x10, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x84, 0x24, 0xff, 0x00,
    0x00, 0x00, 0x00]

def slicesInitEffect (s : RamState) : Effect where
  rip := 0x1002f1
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 296⟩,
     ⟨(.mem (stackPtr s - 128) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 112) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 120) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 32) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.reg 0 : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 40) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 24) : Operand 64), 0⟩,
     ⟨(.mem (stackPtr s - 41) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

macro "init_store_mid " offset:term "," len:term "," sub:term "," blockSub:term : tactic =>
  `(tactic| (
    intro s t h hE hO
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.reduceNeg,
        BitVec.ofNat_eq_ofNat] using h.writable $offset $len (by decide +kernel) (by decide)
    · x86_norm
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.reduceNeg,
        BitVec.ofNat_eq_ofNat, Extracted.textAddress, BitVec.reduceAdd,
        Bytes.Chunked.toListFrom, List.length_map, List.length_range'] using
        h.apart $offset $len (by decide +kernel) (by decide) _ _ $sub
    · intro x hx c hc hcov
      have hc' : c = .mem (stackPtr s - BitVec.ofNat 64 $offset) $len ∨ c = .rip := by
        have hc := hc
        x86_norm at hc
        have hr := (hO true).read (.reg (4#5) : Operand 64) trivial
        rw [← hr] at hc
        x86_norm at hc
        simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.reduceNeg,
          BitVec.ofNat_eq_ofNat] using hc
      rcases hc' with hc' | hc' <;> subst c
      · exact h.avoids_mem $offset $len (by decide +kernel) (by decide) x
          ($blockSub x hx) hcov
      · exact hcov))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem slices_initialize [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x10029a 616)
      (codeRange 0x10029a slicesInitBytes) slicesInitEffect := by
  have hSub := prologue_text_sub 0x29a 87 (by decide +kernel)
  unfold slicesInitBytes
  have hFirst := sub_r64_imm32_effect_step 0x10029a 0x48 0xec 296
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (subR64Imm32Effect 0x10029a 4 296) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2a1 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x1002a1 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 168))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 7 (by decide +kernel)
  case mid => init_store_mid 128, 8, (prologue_text_sub 0x2a1 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2a9 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x1002a9 0x48
    (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 184))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 15 (by decide +kernel)
  case mid => init_store_mid 112, 8, (prologue_text_sub 0x2a9 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2b1 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x1002b1 0x48
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 176))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 23 (by decide +kernel)
  case mid => init_store_mid 120, 8, (prologue_text_sub 0x2b1 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2b9 (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x1002b9 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 31 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2c3 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x1002c3 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 264))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 41 (by decide +kernel)
  case mid => init_store_mid 32, 8, (prologue_text_sub 0x2c3 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2cb (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x1002cb 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 49 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2d5 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x1002d5 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 256))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 59 (by decide +kernel)
  case mid => init_store_mid 40, 8, (prologue_text_sub 0x2d5 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2dd (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_imm32_effect_step 0x1002dd 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 272))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 67 (by decide +kernel)
  case mid => init_store_mid 24, 8, (prologue_text_sub 0x2dd 12 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2e9 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m8_imm8_effect_step 0x1002e9
    (.sib 4 none 0 (.d32 255)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10029a) 79 (by decide +kernel)
  case mid => init_store_mid 41, 1, (prologue_text_sub 0x2e9 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2f1 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [slicesInitEffect]
  · x86_norm [slicesInitEffect]
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · intro i; cases i <;> x86_norm [slicesInitEffect]
  · x86_norm [slicesInitEffect]

def resetInitBytes : List UInt8 := [
    0x48, 0x81, 0xec, 0x48, 0x01, 0x00, 0x00, 0x4c, 0x89, 0x84, 0x24, 0xb8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xcd, 0x48, 0x89, 0x94, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x49, 0x89,
    0xf4, 0x48, 0x89, 0xbc, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x48, 0xb8, 0xfe, 0xdc, 0xba,
    0x98, 0x76, 0x54, 0x32, 0x10, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0xb8, 0x01, 0x23,
    0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0xc7, 0x44,
    0x24, 0x58, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x44, 0x24, 0x47, 0x00]

def resetInitEffect (s : RamState) : Effect where
  rip := 0x10065b
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 328⟩,
     ⟨(.mem (stackPtr s - 144) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
     ⟨(.reg 5 : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 120) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.reg 12 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 128) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 248) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.reg 0 : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 256) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 240) : Operand 64), 0⟩,
     ⟨(.mem (stackPtr s - 257) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem reset_initialize [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x10060a 648)
      (codeRange 0x10060a resetInitBytes) resetInitEffect := by
  have hSub := prologue_text_sub 0x60a 81 (by decide +kernel)
  unfold resetInitBytes
  have hFirst := sub_r64_imm32_effect_step 0x10060a 0x48 0xec 328
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (subR64Imm32Effect 0x10060a 4 328) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x611 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100611 0x4c (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 7 (by decide +kernel)
  case mid => init_store_mid 144, 8, (prologue_text_sub 0x611 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x619 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100619 0x48 0xcd (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 15 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x61c (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x10061c 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 208)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 18 (by decide +kernel)
  case mid => init_store_mid 120, 8, (prologue_text_sub 0x61c 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x624 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100624 0x49 0xf4 (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 26 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x627 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100627 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 200)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 29 (by decide +kernel)
  case mid => init_store_mid 128, 8, (prologue_text_sub 0x627 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x62f (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x10062f 0x48 0xb8 (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 37 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x639 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100639 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 80)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 47 (by decide +kernel)
  case mid => init_store_mid 248, 8, (prologue_text_sub 0x639 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x63e (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x10063e 0x48 0xb8 (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 52 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x648 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100648 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 62 (by decide +kernel)
  case mid => init_store_mid 256, 8, (prologue_text_sub 0x648 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x64d (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_imm32_effect_step 0x10064d 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 88)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 67 (by decide +kernel)
  case mid => init_store_mid 240, 8, (prologue_text_sub 0x64d 9 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x656 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m8_imm8_effect_step 0x100656 (.sib 4 none 0 (.d8 71)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x10060a) 76 (by decide +kernel)
  case mid => init_store_mid 257, 1, (prologue_text_sub 0x656 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x65b (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetInitEffect]
  · x86_norm [resetInitEffect]
    repeat constructor
  · intro i; cases i <;> x86_norm [resetInitEffect]
  · x86_norm [resetInitEffect]

theorem PrologueFrame.after_pushes {entry : BitVec 64} {budget : Nat} {s t : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 48 ≤ budget)
    (hE : (prologuePushEffect entry s).Holds s t) :
    PrologueFrame (entry + 10) (budget - 48) t := by
  have hRsp : stackPtr t = stackPtr s - 48 :=
    Write.allHold_iff.mp hE.writes ⟨(.reg 4 : Operand 64), stackPtr s - 48⟩
      (by simp [prologuePushEffect])
  have hNat : (stackPtr t).toNat = (stackPtr s).toNat - 48 := by
    rw [hRsp]
    exact h.slot_toNat 48 hBudget
  have hUnderflow := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hUnderflow
  have hContains (address : Nat) (ha : (Stack.region t (budget - 48)).Contains address) :
      (Stack.region s budget).Contains address := by
    change (stackPtr t).toNat - (budget - 48) ≤ address ∧
      address < (stackPtr t).toNat - (budget - 48) +
        ((stackPtr t).toNat + 8 - ((stackPtr t).toNat - (budget - 48))) at ha
    change (stackPtr s).toNat - budget ≤ address ∧
      address < (stackPtr s).toNat - budget +
        ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
    rw [hNat] at ha
    constructor <;> omega
  refine ⟨hE.rip, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hb := h.stack.1
    change (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < userAddressLimit at hb
    change (stackPtr t).toNat - (budget - 48) +
      ((stackPtr t).toNat + 8 - ((stackPtr t).toNat - (budget - 48))) < userAddressLimit
    rw [hNat]
    omega
  · intro address ha
    exact Option.isSome_iff_exists.mp (hE.agrees.grow address
      (Option.isSome_iff_exists.mpr (h.stack.2.1 address (hContains _ ha))))
  · change budget - 48 ≤ (stackPtr t).toNat
    omega
  · have halign := h.stack.2.2.2
    change (stackPtr s).toNat % 16 = 8 at halign
    change (stackPtr t).toNat % 16 = 8
    omega
  · intro address ha
    exact h.avoids address (hContains _ ha)

theorem prologue_covers_of_contains {region : MemoryRegion} {address : BitVec 64}
    (h : region.Contains address.toNat) :
    (Component.mem (BitVec.ofNat 64 region.start) region.size).Covers address := by
  refine ⟨address.toNat - region.start, ?_, ?_⟩
  · unfold MemoryRegion.Contains at h
    omega
  · rw [← BitVec.ofNat_add, Nat.add_sub_cancel' h.1,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem absorbed_empty_of_initial_words {s : RamState} (context : BitVec 64)
    (hReadable : MemReadable s (context + 64) 16)
    (hLow : (Operand.mem (context + 64) : Operand 64).read s = 0xefcdab8967452301)
    (hHigh : (Operand.mem (context + 72) : Operand 64).read s = 0x1032547698badcfe)
    (hPosition : (Operand.mem (context + 63) : Operand 8).read s = 0)
    (hBlocks : (Operand.mem (context + 80) : Operand 64).read s = 0) :
    Buffered.Absorbed context ByteArray.empty s := by
  have hLowBytes := Bytes.of_memLoad (n := 64)
    (fun i hi ↦ hReadable.mem i (by omega))
  change Bytes s.external (context + 64) 8
    (storedByte ((Operand.mem (context + 64) : Operand 64).read s)) at hLowBytes
  rw [hLow] at hLowBytes
  have hHighPresent : ∀ i < 8,
      (s.external[(context + 64) + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add] using hReadable.mem (8 + i) (by omega)
  have hHighBytes := Bytes.of_memLoad (n := 64) hHighPresent
  change Bytes s.external ((context + 64) + 8) 8
    (storedByte ((Operand.mem ((context + 64) + 8) : Operand 64).read s)) at hHighBytes
  simp only [BitVec.add_assoc, show (64 : BitVec 64) + 8 = 72 from rfl] at hHighBytes
  rw [hHigh] at hHighBytes
  have hWindow := hLowBytes.append (by
    simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hHighBytes)
  have hValues : ∀ i : Fin 16,
      (if i.val < 8 then storedByte (0xefcdab8967452301 : BitVec 64) i.val
        else storedByte (0x1032547698badcfe : BitVec 64) (i.val - 8)) =
      Standards.RFC.MD5.Buffer.initial.toBytes[i.val] := by
    decide +kernel
  refine ⟨?_, ?_, hPosition, hBlocks⟩
  · rw [Buffered.absorbedBuffer_empty]
    refine ⟨by simp only [MemoryRegion.HasLength, ByteArray.size, Vector.size_toArray], ?_⟩
    intro i
    have hi : i.val < 16 := by
      simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hm := (hWindow i.val (by omega)).trans (congrArg some (hValues ⟨i.val, hi⟩))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ByteArray.getElem_eq_getElem_data,
      Vector.getElem_toArray] using hm
  · change (⟨context.toNat, 0⟩ : MemoryRegion).HasBytes s.external ByteArray.empty
    exact ⟨rfl, fun i ↦ Fin.elim0 i⟩


private theorem slicesInitEffect_local : Effect.Local slicesInitEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [slicesInitEffect, stackPtr_read, h.read_reg]
  · cases i <;> rfl
  · simp [slicesInitEffect, Write.Full, Operand.Full]

private theorem resetInitEffect_local : Effect.Local resetInitEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [resetInitEffect, stackPtr_read, h.read_reg]
  · cases i <;> rfl
  · simp [resetInitEffect, Write.Full, Operand.Full]

attribute [local x86_local] slicesInitEffect_local resetInitEffect_local

theorem prologuePushEffect_avoids {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 48 ≤ budget) :
    (prologuePushEffect entry s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [prologuePushEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact h.avoids_mem 8 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 16 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 24 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 32 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 40 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 48 8 (by omega) (by decide) x hx hcov

theorem slicesInitEffect_avoids {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 128 ≤ budget) :
    (slicesInitEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [slicesInitEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact h.avoids_mem 128 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 112 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 120 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 32 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 40 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 24 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 41 1 (by omega) (by decide) x hx hcov

theorem resetInitEffect_avoids {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 257 ≤ budget) :
    (resetInitEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [resetInitEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact h.avoids_mem 144 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 120 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 128 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 248 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 256 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 240 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 257 1 (by omega) (by decide) x hx hcov

theorem prologue_boundary (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset + 10 < Extracted.textBytes.size) :
    ∀ i : Nat, i ≤ 10 →
      (Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 i ≠ boundary.rip := by
  intro i hi
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    text_address_ne_return hOutside (offset + i) (by omega)

theorem slices_initialized [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x100290 OneMessage.digestSlices.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (Effect.seq (prologuePushEffect 0x100290) slicesInitEffect s).Holds s t := by
  obtain ⟨n, u, hPush, hu, _, hEPush⟩ :=
    prologue_pushes boundary 0x100290 OneMessage.digestSlices.minStackBytes (by decide +kernel)
      (prologue_text_sub 0x290 10 (by decide +kernel))
      (prologue_boundary boundary hOutside 0x290 (by decide +kernel))
      s hReady (program_text_slice hCode 0x290 10 (by decide +kernel)) hFrame
  have hCodeU := hEPush.codeIn (prologuePushEffect_avoids hFrame (by decide +kernel)) hCode
  have hFrameU : PrologueFrame 0x10029a 616 u :=
    hFrame.after_pushes (by decide +kernel) hEPush
  obtain ⟨m, t, hInit, ht, _, hEInit⟩ :=
    slices_initialize boundary hOutside u hu
      (program_text_slice hCodeU 0x29a 87 (by decide +kernel)) hFrameU
  refine ⟨n + m, t, hPush.trans hInit, ht,
    hEInit.codeIn (slicesInitEffect_avoids hFrameU (by decide)) hCodeU, ?_⟩
  exact hEPush.seq slicesInitEffect_local
    (by simp [prologuePushEffect, Write.Full, Operand.Full]) hEInit

theorem reset_initialized [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x100600 TwoMessages.digestSlicesReset.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (Effect.seq (prologuePushEffect 0x100600) resetInitEffect s).Holds s t := by
  obtain ⟨n, u, hPush, hu, _, hEPush⟩ :=
    prologue_pushes boundary 0x100600 TwoMessages.digestSlicesReset.minStackBytes (by decide +kernel)
      (prologue_text_sub 0x600 10 (by decide +kernel))
      (prologue_boundary boundary hOutside 0x600 (by decide +kernel))
      s hReady (program_text_slice hCode 0x600 10 (by decide +kernel)) hFrame
  have hCodeU := hEPush.codeIn (prologuePushEffect_avoids hFrame (by decide +kernel)) hCode
  have hFrameU : PrologueFrame 0x10060a 648 u :=
    hFrame.after_pushes (by decide +kernel) hEPush
  obtain ⟨m, t, hInit, ht, _, hEInit⟩ :=
    reset_initialize boundary hOutside u hu
      (program_text_slice hCodeU 0x60a 81 (by decide +kernel)) hFrameU
  refine ⟨n + m, t, hPush.trans hInit, ht,
    hEInit.codeIn (resetInitEffect_avoids hFrameU (by decide)) hCodeU, ?_⟩
  exact hEPush.seq resetInitEffect_local
    (by simp [prologuePushEffect, Write.Full, Operand.Full]) hEInit

theorem PrologueFrame.covers_in_stack {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset) {address : BitVec 64}
    (hc : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers address) :
    (⟨(Stack.region s budget).start, budget⟩ : MemoryRegion).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  have hu := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  have hb := h.stack.1
  change (stackPtr s).toNat - budget +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
  rw [BitVec.toNat_add, h.slot_toNat offset ho, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (stackPtr s).toNat - budget ≤ _ ∧
    _ < (stackPtr s).toNat - budget + budget
  constructor <;> omega


theorem PrologueFrame.tight_bounded {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) :
    (⟨(Stack.region s budget).start, budget⟩ : MemoryRegion).Bounded := by
  have hb := h.stack.1
  have hu := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  change (stackPtr s).toNat - budget +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < userAddressLimit at hb
  change (stackPtr s).toNat - budget + budget < userAddressLimit
  omega

theorem prologue_memoryFrame {entry : BitVec 64} {budget : Nat} {s t : RamState}
    (hFrame : PrologueFrame entry budget s)
    (h : AgreesExcept (prologueChanges s budget) s t) :
    MemoryWriteFrame s t #v[Stack.region s budget] := by
  apply h.memoryWriteFrame
  intro c hc address hcov
  simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact False.elim hcov
  have hContains := contains_of_mem_covers hFrame.tight_bounded hcov
  refine ⟨Stack.region s budget, by simp, ?_⟩
  have hu := hFrame.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  change (stackPtr s).toNat - budget ≤ address.toNat ∧
    address.toNat < (stackPtr s).toNat - budget + budget at hContains
  change (stackPtr s).toNat - budget ≤ address.toNat ∧
    address.toNat < (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  constructor <;> omega

theorem prologue_return_read {entry : BitVec 64} {budget : Nat} {s t : RamState}
    (hFrame : PrologueFrame entry budget s)
    (h : AgreesExcept (prologueChanges s budget) s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  have hbyte : t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    apply h.byte
    intro c hc hcov
    simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try exact False.elim hcov
    have hContains := contains_of_mem_covers hFrame.tight_bounded hcov
    have hu := hFrame.stack.2.2.1
    change budget ≤ (stackPtr s).toNat at hu
    have hb := hFrame.stack.1
    change (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
    change (stackPtr s).toNat - budget ≤ _ ∧
      _ < (stackPtr s).toNat - budget + budget at hContains
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hContains
    omega
  change (t.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0
  rw [hbyte]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem slices_initialized_common {s t : RamState}
    (hFrame : PrologueFrame 0x100290 OneMessage.digestSlices.minStackBytes s)
    (hE : (Effect.seq (prologuePushEffect 0x100290) slicesInitEffect s).Holds s t) :
    PrologueCommon 296 192 168 176 184 OneMessage.digestSlices.minStackBytes .rcx s t := by
  have hWrites := hE.writes
  x86_norm [prologuePushEffect, slicesInitEffect] at hWrites
  rcases hWrites with ⟨h5, h15, h14, h13, h12, h3, hsp, hout, hlen, hptr,
    hhigh, hax, hlow, hblocks, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 344 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hAgrees : AgreesExcept (prologueChanges s OneMessage.digestSlices.minStackBytes) s t := by
    apply hE.agrees.widen
    · intro c hc hm
      cases c with
      | reg r =>
        x86_norm [prologuePushEffect, slicesInitEffect] at hc
        rcases hc with rfl | rfl <;> simp [prologueChanges]
      | mem a len => cases hm
      | flags => simp [prologueChanges]
      | rip => simp [prologueChanges]
      | _ => x86_norm [prologuePushEffect, slicesInitEffect] at hc
    · intro address c hc hcov
      have hContains : (⟨(Stack.region s OneMessage.digestSlices.minStackBytes).start,
          OneMessage.digestSlices.minStackBytes⟩ : MemoryRegion).Contains address.toNat := by
        x86_norm [prologuePushEffect, slicesInitEffect] at hc
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c
        · apply hFrame.covers_in_stack 8 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 16 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 24 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 32 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 40 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 48 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 176 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 160 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 168 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 80 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 88 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 72 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 89 1 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · exact False.elim hcov
      exact ⟨.mem (BitVec.ofNat 64 (Stack.region s OneMessage.digestSlices.minStackBytes).start)
        OneMessage.digestSlices.minStackBytes,
        by simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false, or_true],
        prologue_covers_of_contains
          (region := ⟨(Stack.region s OneMessage.digestSlices.minStackBytes).start,
            OneMessage.digestSlices.minStackBytes⟩) hContains⟩
  refine {
    rsp := hRsp
    absorbed := ?absorbed
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    agrees := hAgrees
    memoryFrame := ?memoryFrame
  }
  case absorbed =>
    apply absorbed_empty_of_initial_words (stackPtr t + 192)
    · have hr := (hFrame.writable 88 16 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 88) 16 :=
        ⟨hr.low, fun i hi ↦ hE.agrees.grow _ (hr.mem i hi)⟩
      simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using ht
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlow
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hhigh
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hposition
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hblocks
  case saved =>
    intro i
    finite_cases i
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[0] = 3#5 from by decide +kernel]
        using h3
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[1] = 12#5 from by decide +kernel]
        using h12
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[2] = 13#5 from by decide +kernel]
        using h13
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[3] = 14#5 from by decide +kernel]
        using h14
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[4] = 15#5 from by decide +kernel]
        using h15
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[5] = 5#5 from by decide +kernel]
        using h5
  case output =>
    change (Operand.mem (stackPtr t + 168) : Operand 64).read t =
      (Operand.reg 1 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hout
  case pointer =>
    change (Operand.mem (stackPtr t + 176) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hptr
  case length =>
    change (Operand.mem (stackPtr t + 184) : Operand 64).read t =
      (Operand.reg 2 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlen
  case returnSlot =>
    simpa only [hRsp, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceAdd]
      using prologue_return_read hFrame hAgrees
  case memoryFrame => exact prologue_memoryFrame hFrame hAgrees

private theorem prologueJmpEffect_local {p : BitVec 64} {len : Nat} {offset : BitVec 64} :
    Effect.Local (fun _ ↦ jmpEffect p len offset) := by
  refine ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    fun _ _ _ i hi ↦ congrArg some hi, ?_⟩
  intro t w hw
  cases hw

attribute [local x86_local] prologueJmpEffect_local
attribute [local x86_compose] jmpEffect branchTarget decR64Effect incR64Effect

def slicesNonemptyEffect (s : RamState) : Effect where
  rip := 0x10033d
  writes := [⟨(.reg 12 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
    ⟨(.reg 15 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem slices_nonempty_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1002fa)
      (codeRange 0x1002fa [0x49, 0x89, 0xf4, 0x45, 0x31, 0xff, 0xeb, 0x3b])
      slicesNonemptyEffect := by
  md5_run_begin (mov_r64_r64_effect_step 0x1002fa 0x49 0xf4
    (by unfold RexWPrefix; decide) (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x2fd (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x1002fd 0x45 0xff
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1002fa) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x300 (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x100300 0x3b (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x1002fa) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x33d (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [slicesNonemptyEffect]
  · x86_norm [slicesNonemptyEffect]
    constructor
    · rfl
    · change (0 : BitVec 64) =
        (((Operand.reg 15 : Operand 32).read s) ^^^ (Operand.reg 15 : Operand 32).read s).setWidth 64
      simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [slicesNonemptyEffect]
  · x86_norm [slicesNonemptyEffect]

theorem slices_branch [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1002f1) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (Operand.reg 6 : Operand 64).read s = 0 then 0x10042b else 0x10033d) ∧
      AgreesExcept [.reg 12, .reg 15, .flags, .rip] s t ∧
      ((Operand.reg 6 : Operand 64).read s ≠ 0 →
        (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s ∧
        (Operand.reg 15 : Operand 64).read t = 0) := by
  obtain ⟨u, hTest, hu, hETest⟩ :=
    (test_r64_r64_effect_step 0x1002f1 0x48 0xf6
      (by unfold RexWPrefix; decide) (by decide)).advances hReady
      (program_text_slice hCode 0x2f1 3 (by decide +kernel)) hRip
      (text_address_ne_return hOutside 0x2f4 (by decide +kernel))
  change (testR64R64Effect 0x1002f1 6 6 s).Holds s u at hETest
  have hCodeU := hETest.codeIn (testR64R64Effect_avoids _ _ _ _ _) hCode
  have hZF : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      decide ((Operand.reg 6 : Operand 64).read s = 0) := by
    simpa only [Effect.flag, testR64R64Effect, testFlags, StatusFlagsOutcome.get,
      StatusFlags.get, BitVec.and_self, FlagAllows, Bool.beq_eq_decide_eq] using hETest.flag .ZF
  obtain ⟨v, hJump, hv, hEJump⟩ :=
    (jcc_rel32_effect_step 0x1002f4 4 0x131).advances hu
      (program_text_slice hCodeU 0x2f4 6 (by decide +kernel))
      ⟨hETest.rip, fun _ ↦ by decide +kernel⟩ (by
        change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10042b else 0x1002fa) ≠ boundary.rip
        split
        · exact text_address_ne_return hOutside 0x42b (by decide +kernel)
        · exact text_address_ne_return hOutside 0x2fa (by decide +kernel))
  have hCodeV := hEJump.codeIn (branchEffect_avoids _ _ _ _) hCodeU
  have hBase : AgreesExcept [.flags, .rip] s v :=
    (hETest.agrees.trans hEJump.agrees).mono (by
      simp [testR64R64Effect, jccEffect, branchEffect, Effect.components])
  have hRipV := hEJump.rip
  change v.RIP = if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10042b else 0x1002fa at hRipV
  rw [hZF] at hRipV
  by_cases hEmpty : (Operand.reg 6 : Operand 64).read s = 0
  · refine ⟨2, v, hTest.trans hJump, hv, hCodeV, ?_, hBase.mono (by simp), ?_⟩
    · simpa only [hEmpty, decide_true, ite_true] using hRipV
    · intro h; exact False.elim (h hEmpty)
  · have hRipV' : v.RIP = 0x1002fa := by
      simpa only [hEmpty, decide_false, Bool.false_eq_true, ite_false] using hRipV
    obtain ⟨fuel, t, hTail, ht, _, hETail⟩ :=
      slices_nonempty_branch boundary hOutside v hv
        (program_text_slice hCodeV 0x2fa 8 (by decide +kernel)) hRipV'
    have hAgrees : AgreesExcept [.reg 12, .reg 15, .flags, .rip] s t :=
      (hBase.trans hETail.agrees).mono (by simp [slicesNonemptyEffect, Effect.components])
    refine ⟨2 + fuel, t, (hTest.trans hJump).trans hTail, ht,
      hETail.codeIn (Effect.Avoids.of_noMem (by
        simp [slicesNonemptyEffect, Effect.components, Component.Covers]) _) hCodeV,
      ?_, hAgrees, ?_⟩
    · simpa only [hEmpty, ite_false, slicesNonemptyEffect] using hETail.rip
    · intro _
      have hW := hETail.writes
      change (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read v ∧
        (Operand.reg 15 : Operand 64).read t = 0 at hW
      exact ⟨hW.1.trans (hBase.read (by simp)), hW.2⟩

def prologueTailChanges : List Component :=
  [.reg 0, .reg 1, .reg 5, .reg 12, .reg 14, .reg 15, .flags, .rip]

theorem PrologueStorage.of_external_eq
    {frame context outputSlot pointerSlot lengthSlot budget : Nat}
    {outputRegister : Syntax.Reg} {initial s t : RamState}
    (h : PrologueStorage frame context outputSlot pointerSlot lengthSlot budget outputRegister
      initial s) (hRsp : stackPtr t = stackPtr s) (hMemory : t.external = s.external) :
    PrologueStorage frame context outputSlot pointerSlot lengthSlot budget outputRegister
      initial t := by
  refine ⟨hRsp.trans h.rsp, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [hRsp, Operand.read, hMemory] using h.saved i
  · simpa only [hRsp, Operand.read, hMemory] using h.output
  · simpa only [hRsp, Operand.read, hMemory] using h.pointer
  · simpa only [hRsp, Operand.read, hMemory] using h.length
  · simpa only [hRsp, Operand.read, hMemory] using h.returnSlot

theorem absorbed_of_external_eq {context : BitVec 64} {message : ByteArray} {s t : RamState}
    (h : Buffered.Absorbed context message s) (hMemory : t.external = s.external) :
    Buffered.Absorbed context message t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hMemory]
    exact h.buffer
  · rw [hMemory]
    exact h.tail
  · simpa only [Operand.read, hMemory] using h.position
  · simpa only [Operand.read, hMemory] using h.blocks

theorem PrologueCommon.of_registers
    {frame context outputSlot pointerSlot lengthSlot budget : Nat}
    {outputRegister : Syntax.Reg} {initial s t : RamState}
    (h : PrologueCommon frame context outputSlot pointerSlot lengthSlot budget outputRegister
      initial s) (hTail : AgreesExcept prologueTailChanges s t) :
    PrologueCommon frame context outputSlot pointerSlot lengthSlot budget outputRegister
      initial t := by
  have hRsp : stackPtr t = stackPtr s := hTail.read (n := 64) (r := 4) (by simp [prologueTailChanges])
  have hMemory : t.external = s.external :=
    hTail.external (by simp [prologueTailChanges, Component.Covers])
  refine ⟨h.toPrologueStorage.of_external_eq hRsp hMemory, ?_, ?_, ?_⟩
  · rw [hRsp]
    exact absorbed_of_external_eq h.absorbed hMemory
  · apply (h.agrees.trans hTail).mono
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hc
    · simp only [prologueTailChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [prologueChanges]
  · intro address ha
    rw [hMemory]
    exact h.memoryFrame address ha


theorem slices_prologue_of_ready [bindings : Bindings] {s : RamState}
    {inputs : Array Slices.Input} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hCall : (OneMessage.ValidCall OneMessage.digestSlices) bindings s inputs)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ SlicesProloguePost s inputs t := by
  have hFrame : PrologueFrame 0x100290 OneMessage.digestSlices.minStackBytes s :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable, (hCall.stackSeparation.2 (Stack.region s OneMessage.digestSlices.minStackBytes) (by simp)).2⟩
  obtain ⟨n, u, hInit, hu, hCodeU, hE⟩ :=
    slices_initialized boundary hReady hCode hFrame hOutside
  have hCommon := slices_initialized_common hFrame hE
  obtain ⟨m, t, hBranch, ht, hCodeT, hRip, hAgrees, hNonempty⟩ :=
    slices_branch boundary hu hCodeU hE.rip hOutside
  have hCountPreserved : (Operand.reg 6 : Operand 64).read u =
      (Operand.reg 6 : Operand 64).read s :=
    hCommon.agrees.read (by simp [prologueChanges])
  have hCountNat : ((Operand.reg 6 : Operand 64).read u).toNat = inputs.size :=
    (congrArg BitVec.toNat hCountPreserved).trans hCall.inputsInMemory.countArgument
  have hZero : (Operand.reg 6 : Operand 64).read u = 0 ↔ inputs.size = 0 := by
    constructor
    · intro hz
      rw [hz] at hCountNat
      exact hCountNat.symm
    · intro hz
      apply BitVec.eq_of_toNat_eq
      exact hCountNat.trans hz
  have hCountValue : (Operand.reg 6 : Operand 64).read u = BitVec.ofNat 64 inputs.size := by
    have hh := congrArg (BitVec.ofNat 64) hCountNat
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh
  refine ⟨n + m, t, hInit.trans hBranch, ht, hCodeT, ?_⟩
  refine {
    toPrologueCommon := hCommon.of_registers (hAgrees.mono (by simp [prologueTailChanges]))
    rip := ?rip
    index := ?index
    count := ?count
  }
  case rip => simpa only [hZero] using hRip
  case index => intro h; exact (hNonempty (fun hz ↦ h (hZero.mp hz))).2
  case count => intro h; exact (hNonempty (fun hz ↦ h (hZero.mp hz))).1.trans hCountValue

theorem slices_prologue (bindings : Bindings) {s : RamState}
    {inputs : Array Slices.Input} (boundary : ReturnBoundary)
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hCall : (OneMessage.ValidCall OneMessage.digestSlices) bindings s inputs)
    (hOutside : ¬ InProgram boundary.rip) :
    letI := bindings
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ SlicesProloguePost s inputs t := by
  letI := bindings
  have hEntry := Md5.Proofs.entryReady bindings hBindings hMachine hCall.programLoaded
  exact slices_prologue_of_ready boundary hEntry.ready hEntry.code hCall hOutside

theorem reset_initialized_common {s t : RamState}
    (hFrame : PrologueFrame 0x100600 TwoMessages.digestSlicesReset.minStackBytes s)
    (hE : (Effect.seq (prologuePushEffect 0x100600) resetInitEffect s).Holds s t) :
    PrologueCommon 328 8 184 200 208 TwoMessages.digestSlicesReset.minStackBytes .r8 s t := by
  have hWrites := hE.writes
  x86_norm [prologuePushEffect, resetInitEffect] at hWrites
  rcases hWrites with ⟨h5, h15, h14, h13, h12, h3, hsp, hout, hbound, hlen, hcount, hptr,
    hhigh, hax, hlow, hblocks, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 376 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hAgrees : AgreesExcept (prologueChanges s TwoMessages.digestSlicesReset.minStackBytes) s t := by
    apply hE.agrees.widen
    · intro c hc hm
      cases c with
      | reg r =>
        x86_norm [prologuePushEffect, resetInitEffect] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> simp [prologueChanges]
      | mem a len => cases hm
      | flags => simp [prologueChanges]
      | rip => simp [prologueChanges]
      | _ => x86_norm [prologuePushEffect, resetInitEffect] at hc
    · intro address c hc hcov
      have hContains : (⟨(Stack.region s TwoMessages.digestSlicesReset.minStackBytes).start,
          TwoMessages.digestSlicesReset.minStackBytes⟩ : MemoryRegion).Contains address.toNat := by
        x86_norm [prologuePushEffect, resetInitEffect] at hc
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c
        · apply hFrame.covers_in_stack 8 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 16 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 24 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 32 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 40 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 48 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 192 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 168 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 176 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 296 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 304 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 288 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 305 1 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · exact False.elim hcov
      exact ⟨.mem (BitVec.ofNat 64 (Stack.region s TwoMessages.digestSlicesReset.minStackBytes).start)
        TwoMessages.digestSlicesReset.minStackBytes,
        by simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false, or_true],
        prologue_covers_of_contains
          (region := ⟨(Stack.region s TwoMessages.digestSlicesReset.minStackBytes).start,
            TwoMessages.digestSlicesReset.minStackBytes⟩) hContains⟩
  refine {
    rsp := hRsp
    absorbed := ?absorbed
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    agrees := hAgrees
    memoryFrame := ?memoryFrame
  }
  case absorbed =>
    apply absorbed_empty_of_initial_words (stackPtr t + 8)
    · have hr := (hFrame.writable 304 16 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 304) 16 :=
        ⟨hr.low, fun i hi ↦ hE.agrees.grow _ (hr.mem i hi)⟩
      simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using ht
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlow
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hhigh
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hposition
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hblocks
  case saved =>
    intro i
    finite_cases i
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[0] = 3#5 from by decide +kernel]
        using h3
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[1] = 12#5 from by decide +kernel]
        using h12
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[2] = 13#5 from by decide +kernel]
        using h13
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[3] = 14#5 from by decide +kernel]
        using h14
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[4] = 15#5 from by decide +kernel]
        using h15
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[5] = 5#5 from by decide +kernel]
        using h5
  case output =>
    change (Operand.mem (stackPtr t + 184) : Operand 64).read t =
      (Operand.reg 8 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hout
  case pointer =>
    change (Operand.mem (stackPtr t + 200) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hptr
  case length =>
    change (Operand.mem (stackPtr t + 208) : Operand 64).read t =
      (Operand.reg 2 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlen
  case returnSlot =>
    simpa only [hRsp, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceAdd]
      using prologue_return_read hFrame hAgrees
  case memoryFrame => exact prologue_memoryFrame hFrame hAgrees

def resetEmptyEffect (_ : RamState) : Effect where
  rip := 0x1007a6
  writes := [⟨(.reg 0 : Operand 64), 0⟩, ⟨(.reg 14 : Operand 64), 0⟩,
    ⟨(.reg 5 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem reset_empty_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100787)
      (codeRange 0x100787 [0x31, 0xc0, 0x45, 0x31, 0xf6, 0x31, 0xed, 0xeb, 0x16])
      resetEmptyEffect := by
  md5_run_begin (xor_r32_r32_effect_step 0x100787 0xc0 (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x789 (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x100789 0x45 0xf6
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100787) 2 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x78c (by decide +kernel)
  md5_run_then (xor_r32_r32_effect_step 0x10078c 0xed (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100787) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x78e (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x10078e 0x16 (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x100787) 7 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x7a6 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetEmptyEffect]
  · x86_norm [resetEmptyEffect]
    change (0 : BitVec 64) = (((Operand.reg 0 : Operand 32).read s) ^^^
      (Operand.reg 0 : Operand 32).read s).setWidth 64 ∧
      (0 : BitVec 64) = (((Operand.reg 14 : Operand 32).read s) ^^^
      (Operand.reg 14 : Operand 32).read s).setWidth 64 ∧
      (0 : BitVec 64) = (((Operand.reg 5 : Operand 32).read s) ^^^
      (Operand.reg 5 : Operand 32).read s).setWidth 64
    simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, and_self]
  · intro i; cases i <;> x86_norm [resetEmptyEffect]
  · x86_norm [resetEmptyEffect]

def resetClampPrefixEffect (s : RamState) : Effect where
  rip := 0x100682
  writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s - 1⟩,
    ⟨(.reg 0 : Operand 64), (Operand.reg 12 : Operand 64).read s - 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 5 : Operand 64).read s - 1)
    ((Operand.reg 12 : Operand 64).read s - 1)))

theorem reset_clamp_prefix [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100677)
      (codeRange 0x100677 [0x48, 0xff, 0xcd, 0x49, 0x8d, 0x44, 0x24, 0xff,
        0x48, 0x39, 0xc5]) resetClampPrefixEffect := by
  have hFirst := dec_r64_effect_step 0x100677 0x48 0xcd
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (decR64Effect 0x100677 5) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x67a (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x10067a 0x49
    (by unfold RexWPrefix; decide) 0 (.sib 12 none 0 (.d8 (-1)))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100677) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x67f (by decide +kernel)
  md5_run_then (cmp_r64_r64_effect_step 0x10067f 0x48 0xc5
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100677) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x682 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetClampPrefixEffect, decR64Effect]
  · x86_norm [resetClampPrefixEffect, decR64Effect]
  · intro i; cases i <;> x86_norm [resetClampPrefixEffect, decR64Effect]
  · x86_norm [resetClampPrefixEffect, decR64Effect]

theorem reset_count_store_common {initial s t : RamState}
    (hFrame : PrologueFrame 0x100600 TwoMessages.digestSlicesReset.minStackBytes initial)
    (h : PrologueCommon 328 8 184 200 208 TwoMessages.digestSlicesReset.minStackBytes .r8 initial s)
    (hTail : AgreesExcept [.mem (stackPtr s + 192) 8, .rip] s t) :
    PrologueCommon 328 8 184 200 208 TwoMessages.digestSlicesReset.minStackBytes .r8 initial t := by
  have hNat : (stackPtr s).toNat = (stackPtr initial).toNat - 376 := by
    rw [h.rsp]
    exact hFrame.slot_toNat 376 (by decide +kernel)
  have hUpper : (stackPtr s).toNat + 384 < 2^32 := by
    have hb := hFrame.stack.1
    have hu := hFrame.stack.2.2.1
    change TwoMessages.digestSlicesReset.minStackBytes ≤ (stackPtr initial).toNat at hu
    change (stackPtr initial).toNat - TwoMessages.digestSlicesReset.minStackBytes +
      ((stackPtr initial).toNat + 8 -
        ((stackPtr initial).toNat - TwoMessages.digestSlicesReset.minStackBytes)) < 2^32 at hb
    have hBudget : TwoMessages.digestSlicesReset.minStackBytes = 696 := by decide +kernel
    rw [hBudget] at hu hb
    omega
  have hAddress (offset : Nat) (ho : offset ≤ 384) :
      (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega),
      Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by omega)]
  have hContext : (stackPtr s + 8).toNat = (stackPtr s).toNat + 8 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hAddress 8 (by decide)
  have hRsp : stackPtr t = stackPtr s := hTail.read (n := 64) (r := 4) (by simp)
  have hStoreFrame : MemoryWriteFrame s t #v[⟨(stackPtr s).toNat + 192, 8⟩] := by
    apply hTail.memoryWriteFrame
    intro c hc address hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨⟨(stackPtr s).toNat + 192, 8⟩, by simp, ?_⟩
      apply contains_of_mem_covers (by
        change (stackPtr s).toNat + 192 + 8 < 2^32
        omega)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat] using hcov
    · exact False.elim hcov
  have hRead (offset bits : Nat) (ho : offset + bits / 8 ≤ 384)
      (hgap : offset + bits / 8 ≤ 192 ∨ 200 ≤ offset) :
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand bits).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand bits).read s := by
    apply memoryRead_of_memoryWriteFrame (region := ⟨(stackPtr s).toNat + offset, bits / 8⟩)
      hStoreFrame
    · change (stackPtr s).toNat + offset + bits / 8 < 2^32
      omega
    · rw [hAddress offset (by omega)]
      exact Nat.le_refl _
    · rw [hAddress offset (by omega)]
      exact Nat.le_refl _
    · intro r hr address ha hc
      have he : r = ⟨(stackPtr s).toNat + 192, 8⟩ := by simpa using hr
      subst r
      change (stackPtr s).toNat + offset ≤ address ∧
        address < (stackPtr s).toNat + offset + bits / 8 at ha
      change (stackPtr s).toNat + 192 ≤ address ∧
        address < (stackPtr s).toNat + 192 + 8 at hc
      omega
  have hTailWide : AgreesExcept (prologueChanges initial TwoMessages.digestSlicesReset.minStackBytes) s t := by
    apply hTail.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases hm
      · simp [prologueChanges]
    · intro address c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have hcov' : (Component.mem (stackPtr initial - 184) 8).Covers address := by
          simpa only [h.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Nat.reduceAdd] using hcov
        exact ⟨.mem (BitVec.ofNat 64 (Stack.region initial TwoMessages.digestSlicesReset.minStackBytes).start)
          TwoMessages.digestSlicesReset.minStackBytes, by simp [prologueChanges],
          prologue_covers_of_contains (region :=
            ⟨(Stack.region initial TwoMessages.digestSlicesReset.minStackBytes).start,
              TwoMessages.digestSlicesReset.minStackBytes⟩)
            (hFrame.covers_in_stack 184 8 (by decide +kernel) (by decide) hcov')⟩
      · exact False.elim hcov
  have hAgrees : AgreesExcept (prologueChanges initial TwoMessages.digestSlicesReset.minStackBytes) initial t :=
    (h.agrees.trans hTailWide).mono (by simp)
  refine {
    rsp := hRsp.trans h.rsp
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    absorbed := ?absorbed
    agrees := hAgrees
    memoryFrame := prologue_memoryFrame hFrame hAgrees
  }
  case saved =>
    intro i
    rw [hRsp]
    exact (hRead (328 + 8 * i.val) 64 (by have := i.isLt; omega) (by omega)).trans (h.saved i)
  case output =>
    rw [hRsp]
    exact (hRead 184 64 (by decide) (by decide)).trans h.output
  case pointer =>
    rw [hRsp]
    exact (hRead 200 64 (by decide) (by decide)).trans h.pointer
  case length =>
    rw [hRsp]
    exact (hRead 208 64 (by decide) (by decide)).trans h.length
  case returnSlot =>
    rw [hRsp]
    exact (hRead 376 64 (by decide) (by decide)).trans h.returnSlot
  case absorbed =>
    rw [hRsp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Md5.Proofs.hasBytes_of_memoryWriteFrame hStoreFrame h.absorbed.buffer
      · change (stackPtr s + 8).toNat + 64 + 16 < 2^32
        rw [hContext]
        omega
      · intro r hr address ha hc
        have he : r = ⟨(stackPtr s).toNat + 192, 8⟩ := by simpa using hr
        subst r
        change (stackPtr s + 8).toNat + 64 ≤ address ∧
          address < (stackPtr s + 8).toNat + 64 + 16 at ha
        rw [hContext] at ha
        change (stackPtr s).toNat + 192 ≤ address ∧
          address < (stackPtr s).toNat + 192 + 8 at hc
        omega
    · change (⟨(stackPtr s + 8).toNat, 0⟩ : MemoryRegion).HasBytes t.external ByteArray.empty
      exact ⟨rfl, fun i ↦ Fin.elim0 i⟩
    · calc
        (Operand.mem (stackPtr s + 8 + 63) : Operand 8).read t =
            (Operand.mem (stackPtr s + 8 + 63) : Operand 8).read s := by
          simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            hRead 71 8 (by decide) (by decide)
        _ = _ := h.absorbed.position
    · calc
        (Operand.mem (stackPtr s + 8 + 80) : Operand 64).read t =
            (Operand.mem (stackPtr s + 8 + 80) : Operand 64).read s := by
          simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            hRead 88 64 (by decide) (by decide)
        _ = _ := h.absorbed.blocks

def resetClampSuffixEffect (s : RamState) : Effect where
  rip := 0x1006b8
  writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s + 1⟩,
    ⟨(.reg 15 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem reset_clamp_suffix [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100686)
      (codeRange 0x100686 [0x48, 0xff, 0xc5, 0x45, 0x31, 0xff, 0xeb, 0x2a])
      resetClampSuffixEffect := by
  have hFirst := inc_r64_effect_step 0x100686 0x48 0xc5
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (incR64Effect 0x100686 5) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x689 (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x100689 0x45 0xff
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100686) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x68c (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x10068c 0x2a (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x100686) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x6b8 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetClampSuffixEffect]
  · x86_norm [resetClampSuffixEffect]
    change (0 : BitVec 64) = (((Operand.reg 15 : Operand 32).read s) ^^^
      (Operand.reg 15 : Operand 32).read s).setWidth 64
    simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [resetClampSuffixEffect]
  · x86_norm [resetClampSuffixEffect]

theorem reset_clamp_value (first count : BitVec 64) (hf : first ≠ 0) (hc : count ≠ 0) :
    (if !(cmpSpec (first - 1) (count - 1)).CF then count - 1 else first - 1) + 1 =
      BitVec.ofNat 64 (min first.toNat count.toNat) := by
  have hfp : 0 < first.toNat := by
    by_cases hz : first.toNat = 0
    · exact False.elim (hf (BitVec.eq_of_toNat_eq hz))
    · omega
  have hcp : 0 < count.toNat := by
    by_cases hz : count.toNat = 0
    · exact False.elim (hc (BitVec.eq_of_toNat_eq hz))
    · omega
  have hFirst : (first - 1).toNat = first.toNat - 1 := by
    simp only [BitVec.toNat_sub, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    have := first.isLt
    omega
  have hCount : (count - 1).toNat = count.toNat - 1 := by
    simp only [BitVec.toNat_sub, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    have := count.isLt
    omega
  simp only [cmpSpec, subSpec, hFirst, hCount]
  by_cases hle : first.toNat ≤ count.toNat
  · rw [Nat.min_eq_left hle]
    by_cases hlt : first.toNat - 1 < count.toNat - 1
    · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      simp only [BitVec.sub_add_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have heq : count = first := BitVec.eq_of_toNat_eq (by omega)
      subst count
      simp only [Nat.lt_irrefl, decide_false, Bool.not_false, ite_true,
        BitVec.sub_add_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have hlt : ¬ first.toNat - 1 < count.toNat - 1 := by omega
    rw [Nat.min_eq_right (by omega)]
    simp only [hlt, decide_false, Bool.not_false, ite_true,
      BitVec.sub_add_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem reset_clamp_branch [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100677) (hOutside : ¬ InProgram boundary.rip)
    (hFirst : (Operand.reg 5 : Operand 64).read s ≠ 0)
    (hCount : (Operand.reg 12 : Operand 64).read s ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x1006b8 ∧
      (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64
        (min ((Operand.reg 5 : Operand 64).read s).toNat
          ((Operand.reg 12 : Operand 64).read s).toNat) ∧
      (Operand.reg 15 : Operand 64).read t = 0 ∧
      AgreesExcept [.reg 0, .reg 5, .reg 15, .flags, .rip] s t := by
  obtain ⟨n, u, hPrefix, hu, _, hEPrefix⟩ :=
    reset_clamp_prefix boundary hOutside s hReady
      (program_text_slice hCode 0x677 11 (by decide +kernel)) hRip
  have hCodeU := hEPrefix.codeIn (Effect.Avoids.of_noMem (by
    simp [resetClampPrefixEffect, Effect.components, Component.Covers]) _) hCode
  obtain ⟨v, hMove, hv, hEMove⟩ :=
    (cmovae_rbp_rax_effect_step 0x100682).advances hu
      (program_text_slice hCodeU 0x682 4 (by decide +kernel)) hEPrefix.rip
      (text_address_ne_return hOutside 0x686 (by decide +kernel))
  have hCodeV := hEMove.codeIn (Effect.Avoids.of_noMem (by
    simp [cmovaeR64R64Effect, Effect.components, Component.Covers]) _) hCodeU
  obtain ⟨m, t, hSuffix, ht, _, hESuffix⟩ :=
    reset_clamp_suffix boundary hOutside v hv
      (program_text_slice hCodeV 0x686 8 (by decide +kernel)) hEMove.rip
  have hW := hEPrefix.writes
  change (Operand.reg 5 : Operand 64).read u = (Operand.reg 5 : Operand 64).read s - 1 ∧
    (Operand.reg 0 : Operand 64).read u = (Operand.reg 12 : Operand 64).read s - 1 at hW
  have hCF : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      (cmpSpec ((Operand.reg 5 : Operand 64).read s - 1)
        ((Operand.reg 12 : Operand 64).read s - 1)).CF := by
    simpa only [Effect.flag, resetClampPrefixEffect, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, FlagAllows] using hEPrefix.flag .CF
  have hBP := hEMove.writes
  change (Operand.reg 5 : Operand 64).read v =
    if !(StatusFlags.ofRFLAGS u.RFLAGS).CF then (Operand.reg 0 : Operand 64).read u
    else (Operand.reg 5 : Operand 64).read u at hBP
  rw [hCF, hW.1, hW.2] at hBP
  have hWSuffix := hESuffix.writes
  change (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read v + 1 ∧
    (Operand.reg 15 : Operand 64).read t = 0 at hWSuffix
  refine ⟨n + 1 + m, t, (hPrefix.trans hMove).trans hSuffix, ht,
    hESuffix.codeIn (Effect.Avoids.of_noMem (by
      simp [resetClampSuffixEffect, Effect.components, Component.Covers]) _) hCodeV,
    hESuffix.rip, ?_, hWSuffix.2, ?_⟩
  · rw [hWSuffix.1, hBP]
    exact reset_clamp_value _ _ hFirst hCount
  · exact ((hEPrefix.agrees.trans hEMove.agrees).trans hESuffix.agrees).mono (by
      simp [resetClampPrefixEffect, cmovaeR64R64Effect, resetClampSuffixEffect, Effect.components])

private theorem mergeGPR8_setWidth (value : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 value old).setWidth 8 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, decide_true, Bool.true_and,
    mergeGPR, show ¬ (8 : Nat) = 32 from by decide, ite_false,
    getLsbD_setSlice old 0 8 value i (by omega), Nat.zero_le, Nat.zero_add,
    hi, and_self, ite_true, Nat.sub_zero]

private theorem mergeGPR8_overwrite (a b : BitVec 8) (old : BitVec 64) :
    mergeGPR 8 a (mergeGPR 8 b old) = mergeGPR 8 a old := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mergeGPR, show ¬ (8 : Nat) = 32 from by decide, ite_false]
  rw [getLsbD_setSlice _ 0 8 a i hi, getLsbD_setSlice _ 0 8 a i hi,
    getLsbD_setSlice old 0 8 b i hi]
  split <;> rfl

attribute [local x86_compose] mergeGPR8_setWidth mergeGPR8_overwrite

def resetDispatchPrefixEffect (first count : BitVec 64) (s : RamState) : Effect :=
  let a : BitVec 8 := if first = 0 then 1 else 0
  let b : BitVec 8 := if count = 0 then 1 else 0
  { rip := 0x100669
    writes := [⟨(.reg 0 : Operand 64), mergeGPR 8 a ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), mergeGPR 8 (b ||| a) ((Operand.reg 1 : Operand 64).read s)⟩]
    flags := some (andFlags (b ||| a)) }

theorem reset_dispatch_prefix [Bindings] (first count : BitVec 64)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10065b ∧ (Operand.reg 1 : Operand 64).read s = first ∧
        (Operand.reg 6 : Operand 64).read s = count)
      (codeRange 0x10065b [0x48, 0x85, 0xc9, 0x0f, 0x94, 0xc0, 0x48,
        0x85, 0xf6, 0x0f, 0x94, 0xc1, 0x08, 0xc1])
      (resetDispatchPrefixEffect first count) := by
  have hTestA := test_r64_r64_effect_step 0x10065b 0x48 0xc9
    (by unfold RexWPrefix; decide) (by decide)
  change StepEffect _ _ (testR64R64Effect 0x10065b 1 1) at hTestA
  have hTestB := test_r64_r64_effect_step 0x100661 0x48 0xf6
    (by unfold RexWPrefix; decide) (by decide)
  change StepEffect _ _ (testR64R64Effect 0x100661 6 6) at hTestB
  md5_run_begin hTestA
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x65e (by decide +kernel)
  md5_run_then (sete_al_fixed_effect_step 0x10065e (decide (first = 0)))
  case sub => exact codeRange_mem_of_drop (p := 0x10065b) 3 (by decide +kernel)
  case mid =>
    intro s t h hE _
    refine ⟨⟨hE.rip, ?_⟩, setzR8FixedEffect_avoids _ _ _ _ _⟩
    simpa only [Effect.flag, testR64R64Effect, testFlags, StatusFlagsOutcome.get,
      StatusFlags.get, FlagAllows, BitVec.and_self, Bool.beq_eq_decide_eq, h.2.1]
      using hE.flag .ZF
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x661 (by decide +kernel)
  md5_run_then hTestB
  case sub => exact codeRange_mem_of_drop (p := 0x10065b) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x664 (by decide +kernel)
  md5_run_then (sete_cl_fixed_effect_step 0x100664 (decide (count = 0)))
  case sub => exact codeRange_mem_of_drop (p := 0x10065b) 9 (by decide +kernel)
  case mid =>
    intro s t h hE _
    refine ⟨⟨hE.rip, ?_⟩, setzR8FixedEffect_avoids _ _ _ _ _⟩
    have hz := hE.flag .ZF
    x86_norm [Effect.flag, testFlags, StatusFlagsOutcome.get, StatusFlags.get, FlagAllows,
      BitVec.and_self, Bool.beq_eq_decide_eq, h.2.2] at hz
    exact hz
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x667 (by decide +kernel)
  md5_run_then (or_cl_al_effect_step 0x100667)
  case sub => exact codeRange_mem_of_drop (p := 0x10065b) 12 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x669 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t h hE
  apply hE.weaken
  · x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]
  · x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]
  · intro i; cases i <;> x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]
  · x86_norm [resetDispatchPrefixEffect, decide_eq_true_iff]

def resetCountEffect (s : RamState) : Effect where
  rip := 0x100671
  writes := [⟨(.mem (stackPtr s + 192) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩]

theorem reset_count_effect_step [Bindings] :
    StepEffect (Memory.StorePre 0x100669 8 (fun s ↦ stackPtr s + 192) 8)
      (codeRange 0x100669 [0x48, 0x89, 0xb4, 0x24, 0xc0, 0, 0, 0]) resetCountEffect := by
  exact Buffered.Stores.mov_m64_r64_effect_step 0x100669 0x48
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 192))
    (by decide) (by decide) (by decide)

theorem reset_dispatch_zero_value (first count : BitVec 64) :
    (((if count = 0 then (1 : BitVec 8) else 0) |||
      (if first = 0 then 1 else 0)) == 0) = decide (¬ (first = 0 ∨ count = 0)) := by
  by_cases hf : first = 0 <;> by_cases hc : count = 0
  all_goals
    simp only [BitVec.ofNat_eq_ofNat] at hf hc ⊢
    simp [hf, hc]

theorem reset_dispatched [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x100600 TwoMessages.digestSlicesReset.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      PrologueCommon 328 8 184 200 208 TwoMessages.digestSlicesReset.minStackBytes .r8 s t ∧
      t.RIP = (if (Operand.reg 1 : Operand 64).read s = 0 ∨
        (Operand.reg 6 : Operand 64).read s = 0 then 0x100787 else 0x100677) ∧
      (Operand.reg 5 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s ∧
      (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s ∧
      (Operand.mem (stackPtr t + 192) : Operand 64).read t =
        (Operand.reg 6 : Operand 64).read s := by
  obtain ⟨n, u, hInit, hu, hCodeU, hE⟩ :=
    reset_initialized boundary hReady hCode hFrame hOutside
  have hCommonU := reset_initialized_common hFrame hE
  have hFirstU : (Operand.reg 1 : Operand 64).read u =
      (Operand.reg 1 : Operand 64).read s :=
    hE.agrees.read (by x86_norm [prologuePushEffect, resetInitEffect])
  have hCountU : (Operand.reg 6 : Operand 64).read u =
      (Operand.reg 6 : Operand 64).read s :=
    hE.agrees.read (by x86_norm [prologuePushEffect, resetInitEffect])
  have hW := hE.writes
  x86_norm [prologuePushEffect, resetInitEffect] at hW
  rcases hW with ⟨_, _, _, _, _, _, _, _, hBP, _, hN, _, _, _, _, _, _⟩
  obtain ⟨m, v, hPrefix, hv, _, hEPrefix⟩ :=
    reset_dispatch_prefix ((Operand.reg 1 : Operand 64).read s)
      ((Operand.reg 6 : Operand 64).read s) boundary hOutside u hu
      (program_text_slice hCodeU 0x65b 14 (by decide +kernel)) ⟨hE.rip, hFirstU, hCountU⟩
  have hCodeV := hEPrefix.codeIn (Effect.Avoids.of_noMem (by
    simp [resetDispatchPrefixEffect, Effect.components, Component.Covers]) _) hCodeU
  have hPrefixAgrees : AgreesExcept prologueTailChanges u v := hEPrefix.agrees.mono (by
    simp [prologueTailChanges, resetDispatchPrefixEffect, Effect.components])
  have hCommonV := hCommonU.of_registers hPrefixAgrees
  have hStoreAddress : stackPtr v + 192 = stackPtr s - 184 := by
    rw [hCommonV.rsp]
    simp only [Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have hWrite : Memory.MemWritable v (stackPtr v + 192) 8 := by
    rw [hStoreAddress]
    have hw := hFrame.writable 184 8 (by decide +kernel) (by decide)
    exact ⟨hw.low, fun i hi ↦ hCommonV.agrees.grow _ (hw.bytes i hi), hw.tables⟩
  have hApart : RangeApart (stackPtr v + 192) 8 0x100669 8 := by
    rw [hStoreAddress]
    exact hFrame.apart 184 8 (by decide +kernel) (by decide) 0x100669
      [0x48, 0x89, 0xb4, 0x24, 0xc0, 0, 0, 0]
      (prologue_text_sub 0x669 8 (by decide +kernel))
  obtain ⟨w, hStore, hw, hEStore⟩ := reset_count_effect_step.advances hv
    (program_text_slice hCodeV 0x669 8 (by decide +kernel))
    ⟨hEPrefix.rip, hWrite, hApart⟩
    (text_address_ne_return hOutside 0x671 (by decide +kernel))
  have hStoreAgrees : AgreesExcept [.mem (stackPtr v + 192) 8, .rip] v w := by
    simpa [resetCountEffect, Effect.components] using hEStore.agrees
  have hStoreRsp : stackPtr w = stackPtr v := hStoreAgrees.read (n := 64) (r := 4) (by simp)
  have hCommonW := reset_count_store_common hFrame hCommonV hStoreAgrees
  have hCodeW := hEStore.codeIn (by
    intro x hx c hc hcov
    have hc' : c = .mem (stackPtr v + 192) 8 ∨ c = .rip := by
      simpa [resetCountEffect, Effect.components] using hc
    rcases hc' with rfl | rfl
    · apply hFrame.avoids_mem 184 8 (by decide +kernel) (by decide) x hx
      rw [hStoreAddress] at hcov
      simpa only [BitVec.ofNat_eq_ofNat] using hcov
    · exact False.elim hcov) hCodeV
  have hZFPrefix : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (((if (Operand.reg 6 : Operand 64).read s = 0 then (1 : BitVec 8) else 0) |||
        (if (Operand.reg 1 : Operand 64).read s = 0 then 1 else 0)) == 0) := by
    simpa only [Effect.flag, resetDispatchPrefixEffect, andFlags,
      StatusFlagsOutcome.get, StatusFlags.get, FlagAllows] using hEPrefix.flag .ZF
  have hZFW : (StatusFlags.ofRFLAGS w.RFLAGS).ZF =
      decide (¬ ((Operand.reg 1 : Operand 64).read s = 0 ∨
        (Operand.reg 6 : Operand 64).read s = 0)) := by
    have hZFStore : (StatusFlags.ofRFLAGS w.RFLAGS).ZF = (StatusFlags.ofRFLAGS v.RFLAGS).ZF := by
      simpa only [Effect.flag, resetCountEffect, StatusFlagsOutcome.get,
        StatusFlags.get, FlagAllows] using hEStore.flag .ZF
    exact hZFStore.trans (hZFPrefix.trans (reset_dispatch_zero_value _ _))
  obtain ⟨t, hJump, ht, hEJump⟩ :=
    (jcc_rel32_effect_step 0x100671 5 0x110).advances hw
      (program_text_slice hCodeW 0x671 6 (by decide +kernel))
      ⟨hEStore.rip, fun _ ↦ by decide +kernel⟩ (by
        change (if !(StatusFlags.ofRFLAGS w.RFLAGS).ZF then 0x100787 else 0x100677) ≠ boundary.rip
        split
        · exact text_address_ne_return hOutside 0x787 (by decide +kernel)
        · exact text_address_ne_return hOutside 0x677 (by decide +kernel))
  have hJumpAgrees : AgreesExcept [.rip] w t := hEJump.agrees
  have hJumpRsp : stackPtr t = stackPtr w := hJumpAgrees.read (n := 64) (r := 4) (by simp)
  have hCommonT := hCommonW.of_registers (hJumpAgrees.mono (by simp [prologueTailChanges]))
  refine ⟨n + m + 1 + 1, t, ((hInit.trans hPrefix).trans hStore).trans hJump,
    ht, hEJump.codeIn (branchEffect_avoids _ _ _ _) hCodeW, hCommonT, ?_, ?_, ?_, ?_⟩
  · have hr := hEJump.rip
    change t.RIP = if !(StatusFlags.ofRFLAGS w.RFLAGS).ZF then 0x100787 else 0x100677 at hr
    rw [hZFW] at hr
    simpa only [decide_not, Bool.not_not, decide_eq_true_iff] using hr
  · exact (hJumpAgrees.read (n := 64) (r := 5) (by simp)).trans
      ((hStoreAgrees.read (n := 64) (r := 5) (by simp)).trans
        ((hEPrefix.agrees.read (n := 64) (r := 5) (by
          simp [resetDispatchPrefixEffect, Effect.components])).trans hBP))
  · exact (hJumpAgrees.read (n := 64) (r := 12) (by simp)).trans
      ((hStoreAgrees.read (n := 64) (r := 12) (by simp)).trans
        ((hEPrefix.agrees.read (n := 64) (r := 12) (by
          simp [resetDispatchPrefixEffect, Effect.components])).trans hN))
  · have hMemory := hJumpAgrees.external (by simp [Component.Covers])
    rw [hJumpRsp, hStoreRsp]
    have hStored : (Operand.mem (stackPtr v + 192) : Operand 64).read w =
        (Operand.reg 6 : Operand 64).read v := hEStore.writes
    have hCountV : (Operand.reg 6 : Operand 64).read v =
        (Operand.reg 6 : Operand 64).read u := hEPrefix.agrees.read (by
      simp [resetDispatchPrefixEffect, Effect.components])
    simpa only [Operand.read, hMemory] using hStored.trans (hCountV.trans hCountU)

theorem reset_prologue_of_ready [bindings : Bindings] {s : RamState}
    {inputs : Array Slices.Input} {first : Nat} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings s inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ ResetProloguePost s inputs first t := by
  have hFrame : PrologueFrame 0x100600 TwoMessages.digestSlicesReset.minStackBytes s :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable,
      (hCall.separation.2 (Stack.region s TwoMessages.digestSlicesReset.minStackBytes) (by simp)).2⟩
  obtain ⟨n, u, hDispatch, hu, hCodeU, hCommonU, hRipU, hBPU, hCountU, hTotalU⟩ :=
    reset_dispatched boundary hReady hCode hFrame hOutside
  have hFirstNat : ((Operand.reg 1 : Operand 64).read s).toNat = first := hCall.firstCountArgumentMatchesFirst
  have hCountNat : ((Operand.reg 6 : Operand 64).read s).toNat = inputs.size :=
    hCall.inputsInMemory.countArgument
  have hFirstZero : (Operand.reg 1 : Operand 64).read s = 0 ↔ first = 0 := by
    rw [BitVec.toNat_eq, hFirstNat]
    rfl
  have hCountZero : (Operand.reg 6 : Operand 64).read s = 0 ↔ inputs.size = 0 := by
    rw [BitVec.toNat_eq, hCountNat]
    rfl
  have hCountValue : (Operand.reg 6 : Operand 64).read s = BitVec.ofNat 64 inputs.size := by
    have hh := congrArg (BitVec.ofNat 64) hCountNat
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh
  have hEmptyIff : ((Operand.reg 1 : Operand 64).read s = 0 ∨
      (Operand.reg 6 : Operand 64).read s = 0) ↔ min first inputs.size = 0 := by
    rw [hFirstZero, hCountZero, Nat.min_eq_zero_iff]
  obtain ⟨m, t, hTail, ht, hCodeT, hRipT, hBPT, hIndexT, hEmptyT, hTailAgrees⟩ :
      ∃ m t, Advances boundary m u t ∧ ReadyToStep t ∧
        CodeIn Extracted.programImage t ∧
        t.RIP = (if min first inputs.size = 0 then 0x1007a6 else 0x1006b8) ∧
        (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64 (min first inputs.size) ∧
        (min first inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read t = 0) ∧
        (min first inputs.size = 0 → (Operand.reg 0 : Operand 64).read t = 0 ∧
          (Operand.reg 14 : Operand 64).read t = 0) ∧
        AgreesExcept [.reg 0, .reg 5, .reg 14, .reg 15, .flags, .rip] u t := by
    by_cases hEmpty : min first inputs.size = 0
    · have hRip : u.RIP = 0x100787 := by
        simpa only [hEmptyIff.mpr hEmpty, ite_true] using hRipU
      obtain ⟨m, t, hTail, ht, _, hETail⟩ := reset_empty_branch boundary hOutside u hu
        (program_text_slice hCodeU 0x787 9 (by decide +kernel)) hRip
      have hW := hETail.writes
      change (Operand.reg 0 : Operand 64).read t = 0 ∧
        (Operand.reg 14 : Operand 64).read t = 0 ∧
        (Operand.reg 5 : Operand 64).read t = 0 at hW
      refine ⟨m, t, hTail, ht, hETail.codeIn (Effect.Avoids.of_noMem (by
        simp [resetEmptyEffect, Effect.components, Component.Covers]) _) hCodeU,
        ?_, ?_, ?_, ?_, hETail.agrees.mono (by
          simp [resetEmptyEffect, Effect.components])⟩
      · simpa only [hEmpty, ite_true, resetEmptyEffect] using hETail.rip
      · simpa only [hEmpty, BitVec.ofNat_eq_ofNat] using hW.2.2
      · intro h; exact False.elim (h hEmpty)
      · intro _; exact ⟨hW.1, hW.2.1⟩
    · have hOriginal : ¬ ((Operand.reg 1 : Operand 64).read s = 0 ∨
          (Operand.reg 6 : Operand 64).read s = 0) := fun hz ↦ hEmpty (hEmptyIff.mp hz)
      have hRip : u.RIP = 0x100677 := by simpa only [hOriginal, ite_false] using hRipU
      have hFirstNonzero : (Operand.reg 5 : Operand 64).read u ≠ 0 :=
        fun hz ↦ hOriginal (.inl (hBPU.symm.trans hz))
      have hCountNonzero : (Operand.reg 12 : Operand 64).read u ≠ 0 :=
        fun hz ↦ hOriginal (.inr (hCountU.symm.trans hz))
      obtain ⟨m, t, hTail, ht, hCodeT, hRipT, hBound, hIndex, hAgrees⟩ :=
        reset_clamp_branch boundary hu hCodeU hRip hOutside hFirstNonzero hCountNonzero
      refine ⟨m, t, hTail, ht, hCodeT, ?_, ?_, fun _ ↦ hIndex,
        fun hz ↦ False.elim (hEmpty hz), hAgrees.mono (by simp)⟩
      · simpa only [hEmpty, ite_false] using hRipT
      · rw [hBPU, hCountU, hFirstNat, hCountNat] at hBound
        exact hBound
  have hCommonT := hCommonU.of_registers (hTailAgrees.mono (by simp [prologueTailChanges]))
  have hRspTail : stackPtr t = stackPtr u :=
    hTailAgrees.read (n := 64) (r := 4) (by simp)
  have hMemory : t.external = u.external :=
    hTailAgrees.external (by simp [Component.Covers])
  refine ⟨n + m, t, hDispatch.trans hTail, ht, hCodeT, ?_⟩
  refine {
    toPrologueCommon := hCommonT
    rip := hRipT
    total := ?total
    bound := hBPT
    count := ?count
    index := hIndexT
    empty := hEmptyT
  }
  case total =>
    rw [hRspTail]
    simpa only [Operand.read, hMemory] using hTotalU.trans hCountValue
  case count =>
    exact (hTailAgrees.read (n := 64) (r := 12) (by simp)).trans (hCountU.trans hCountValue)

theorem reset_prologue (bindings : Bindings) {s : RamState}
    {inputs : Array Slices.Input} {first : Nat} (boundary : ReturnBoundary)
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings s inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    letI := bindings
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ ResetProloguePost s inputs first t := by
  letI := bindings
  have hEntry := Md5.Proofs.entryReady bindings hBindings hMachine hCall.programLoaded
  exact reset_prologue_of_ready boundary hEntry.ready hEntry.code hCall hOutside

structure finalizeResetProloguePost (initial : RamState) (inputs : Array Slices.Input)
    (first : Nat) (final : RamState) : Prop extends
    PrologueCommon 312 8 184 200 208 TwoMessages.finalizeIntoResetSlices.minStackBytes .r8 initial final where
  rip : final.RIP = if min first inputs.size = 0 then 0x100e56 else 0x100d68
  total : (Operand.mem (stackPtr final + 192) : Operand 64).read final =
    BitVec.ofNat 64 inputs.size
  bound : (Operand.reg 5 : Operand 64).read final = BitVec.ofNat 64 (min first inputs.size)
  count : (Operand.reg 12 : Operand 64).read final = BitVec.ofNat 64 inputs.size
  index : min first inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read final = 0
  empty : min first inputs.size = 0 →
    (Operand.reg 0 : Operand 64).read final = 0 ∧ (Operand.reg 14 : Operand 64).read final = 0

def finalizeResetInitBytes : List UInt8 := [
    0x48, 0x81, 0xec, 0x38, 0x01, 0x00, 0x00, 0x4c, 0x89, 0x84, 0x24, 0xb8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xcd, 0x48, 0x89, 0x94, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x49, 0x89,
    0xf4, 0x48, 0x89, 0xbc, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x48, 0xb8, 0xfe, 0xdc, 0xba,
    0x98, 0x76, 0x54, 0x32, 0x10, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0xb8, 0x01, 0x23,
    0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0xc7, 0x44,
    0x24, 0x58, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x44, 0x24, 0x47, 0x00]

def finalizeResetInitEffect (s : RamState) : Effect where
  rip := 0x100d0b
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 312⟩,
     ⟨(.mem (stackPtr s - 128) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
     ⟨(.reg 5 : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 104) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.reg 12 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 112) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s - 232) : Operand 64), 0x1032547698badcfe⟩,
     ⟨(.reg 0 : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 240) : Operand 64), 0xefcdab8967452301⟩,
     ⟨(.mem (stackPtr s - 224) : Operand 64), 0⟩,
     ⟨(.mem (stackPtr s - 241) : Operand 8), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem finalizeReset_initialize [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PrologueFrame 0x100cba 632)
      (codeRange 0x100cba finalizeResetInitBytes) finalizeResetInitEffect := by
  have hSub := prologue_text_sub 0xcba 81 (by decide +kernel)
  unfold finalizeResetInitBytes
  have hFirst := sub_r64_imm32_effect_step 0x100cba 0x48 0xec 312
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (subR64Imm32Effect 0x100cba 4 312) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcc1 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100cc1 0x4c (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 7 (by decide +kernel)
  case mid => init_store_mid 128, 8, (prologue_text_sub 0xcc1 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcc9 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100cc9 0x48 0xcd (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 15 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xccc (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100ccc 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 208)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 18 (by decide +kernel)
  case mid => init_store_mid 104, 8, (prologue_text_sub 0xccc 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcd4 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100cd4 0x49 0xf4 (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 26 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcd7 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100cd7 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 200)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 29 (by decide +kernel)
  case mid => init_store_mid 112, 8, (prologue_text_sub 0xcd7 8 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcdf (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x100cdf 0x48 0xb8 (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 37 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xce9 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100ce9 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 80)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 47 (by decide +kernel)
  case mid => init_store_mid 232, 8, (prologue_text_sub 0xce9 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcee (by decide +kernel)
  md5_run_then (mov_r64_imm64_effect_step 0x100cee 0x48 0xb8 (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 52 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcf8 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_r64_effect_step 0x100cf8 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 62 (by decide +kernel)
  case mid => init_store_mid 240, 8, (prologue_text_sub 0xcf8 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xcfd (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m64_imm32_effect_step 0x100cfd 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 88)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 67 (by decide +kernel)
  case mid => init_store_mid 224, 8, (prologue_text_sub 0xcfd 9 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd06 (by decide +kernel)
  md5_run_then (Buffered.Stores.mov_m8_imm8_effect_step 0x100d06 (.sib 4 none 0 (.d8 71)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x100cba) 76 (by decide +kernel)
  case mid => init_store_mid 241, 1, (prologue_text_sub 0xd06 5 (by decide +kernel)), hSub
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd0b (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [finalizeResetInitEffect]
  · x86_norm [finalizeResetInitEffect]
    repeat constructor
  · intro i; cases i <;> x86_norm [finalizeResetInitEffect]
  · x86_norm [finalizeResetInitEffect]

private theorem finalizeResetInitEffect_local : Effect.Local finalizeResetInitEffect := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [finalizeResetInitEffect, stackPtr_read, h.read_reg]
  · cases i <;> rfl
  · simp [finalizeResetInitEffect, Write.Full, Operand.Full]

attribute [local x86_local] finalizeResetInitEffect_local

theorem finalizeResetInitEffect_avoids {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (hBudget : 241 ≤ budget) :
    (finalizeResetInitEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  simp only [finalizeResetInitEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | exact h.avoids_mem 128 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 104 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 112 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 232 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 240 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 224 8 (by omega) (by decide) x hx hcov
    | exact h.avoids_mem 241 1 (by omega) (by decide) x hx hcov

theorem finalizeReset_initialized [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x100cb0 TwoMessages.finalizeIntoResetSlices.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (Effect.seq (prologuePushEffect 0x100cb0) finalizeResetInitEffect s).Holds s t := by
  obtain ⟨n, u, hPush, hu, _, hEPush⟩ :=
    prologue_pushes boundary 0x100cb0 TwoMessages.finalizeIntoResetSlices.minStackBytes (by decide +kernel)
      (prologue_text_sub 0xcb0 10 (by decide +kernel))
      (prologue_boundary boundary hOutside 0xcb0 (by decide +kernel))
      s hReady (program_text_slice hCode 0xcb0 10 (by decide +kernel)) hFrame
  have hCodeU := hEPush.codeIn (prologuePushEffect_avoids hFrame (by decide +kernel)) hCode
  have hFrameU : PrologueFrame 0x100cba 632 u :=
    hFrame.after_pushes (by decide +kernel) hEPush
  obtain ⟨m, t, hInit, ht, _, hEInit⟩ :=
    finalizeReset_initialize boundary hOutside u hu
      (program_text_slice hCodeU 0xcba 81 (by decide +kernel)) hFrameU
  refine ⟨n + m, t, hPush.trans hInit, ht,
    hEInit.codeIn (finalizeResetInitEffect_avoids hFrameU (by decide)) hCodeU, ?_⟩
  exact hEPush.seq finalizeResetInitEffect_local
    (by simp [prologuePushEffect, Write.Full, Operand.Full]) hEInit

theorem finalizeReset_initialized_common {s t : RamState}
    (hFrame : PrologueFrame 0x100cb0 TwoMessages.finalizeIntoResetSlices.minStackBytes s)
    (hE : (Effect.seq (prologuePushEffect 0x100cb0) finalizeResetInitEffect s).Holds s t) :
    PrologueCommon 312 8 184 200 208 TwoMessages.finalizeIntoResetSlices.minStackBytes .r8 s t := by
  have hWrites := hE.writes
  x86_norm [prologuePushEffect, finalizeResetInitEffect] at hWrites
  rcases hWrites with ⟨h5, h15, h14, h13, h12, h3, hsp, hout, hbound, hlen, hcount, hptr,
    hhigh, hax, hlow, hblocks, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 360 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hAgrees : AgreesExcept (prologueChanges s TwoMessages.finalizeIntoResetSlices.minStackBytes) s t := by
    apply hE.agrees.widen
    · intro c hc hm
      cases c with
      | reg r =>
        x86_norm [prologuePushEffect, finalizeResetInitEffect] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> simp [prologueChanges]
      | mem a len => cases hm
      | flags => simp [prologueChanges]
      | rip => simp [prologueChanges]
      | _ => x86_norm [prologuePushEffect, finalizeResetInitEffect] at hc
    · intro address c hc hcov
      have hContains : (⟨(Stack.region s TwoMessages.finalizeIntoResetSlices.minStackBytes).start,
          TwoMessages.finalizeIntoResetSlices.minStackBytes⟩ : MemoryRegion).Contains address.toNat := by
        x86_norm [prologuePushEffect, finalizeResetInitEffect] at hc
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c
        · apply hFrame.covers_in_stack 8 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 16 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 24 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 32 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 40 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 48 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 176 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 152 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 160 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 280 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 288 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 272 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 289 1 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · exact False.elim hcov
      exact ⟨.mem (BitVec.ofNat 64 (Stack.region s TwoMessages.finalizeIntoResetSlices.minStackBytes).start)
        TwoMessages.finalizeIntoResetSlices.minStackBytes,
        by simp only [prologueChanges, List.mem_cons, List.not_mem_nil, or_false, or_true],
        prologue_covers_of_contains
          (region := ⟨(Stack.region s TwoMessages.finalizeIntoResetSlices.minStackBytes).start,
            TwoMessages.finalizeIntoResetSlices.minStackBytes⟩) hContains⟩
  refine {
    rsp := hRsp
    absorbed := ?absorbed
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    agrees := hAgrees
    memoryFrame := ?memoryFrame
  }
  case absorbed =>
    apply absorbed_empty_of_initial_words (stackPtr t + 8)
    · have hr := (hFrame.writable 288 16 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 288) 16 :=
        ⟨hr.low, fun i hi ↦ hE.agrees.grow _ (hr.mem i hi)⟩
      simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using ht
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlow
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hhigh
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hposition
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hblocks
  case saved =>
    intro i
    finite_cases i
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[0] = 3#5 from by decide +kernel]
        using h3
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[1] = 12#5 from by decide +kernel]
        using h12
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[2] = 13#5 from by decide +kernel]
        using h13
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[3] = 14#5 from by decide +kernel]
        using h14
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[4] = 15#5 from by decide +kernel]
        using h15
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[5] = 5#5 from by decide +kernel]
        using h5
  case output =>
    change (Operand.mem (stackPtr t + 184) : Operand 64).read t =
      (Operand.reg 8 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hout
  case pointer =>
    change (Operand.mem (stackPtr t + 200) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hptr
  case length =>
    change (Operand.mem (stackPtr t + 208) : Operand 64).read t =
      (Operand.reg 2 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlen
  case returnSlot =>
    simpa only [hRsp, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceAdd]
      using prologue_return_read hFrame hAgrees
  case memoryFrame => exact prologue_memoryFrame hFrame hAgrees

def finalizeResetEmptyEffect (_ : RamState) : Effect where
  rip := 0x100e56
  writes := [⟨(.reg 0 : Operand 64), 0⟩, ⟨(.reg 14 : Operand 64), 0⟩,
    ⟨(.reg 5 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem finalizeReset_empty_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100e37)
      (codeRange 0x100e37 [0x31, 0xc0, 0x45, 0x31, 0xf6, 0x31, 0xed, 0xeb, 0x16])
      finalizeResetEmptyEffect := by
  md5_run_begin (xor_r32_r32_effect_step 0x100e37 0xc0 (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe39 (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x100e39 0x45 0xf6
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100e37) 2 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe3c (by decide +kernel)
  md5_run_then (xor_r32_r32_effect_step 0x100e3c 0xed (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100e37) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe3e (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x100e3e 0x16 (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x100e37) 7 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe56 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [finalizeResetEmptyEffect]
  · x86_norm [finalizeResetEmptyEffect]
    change (0 : BitVec 64) = (((Operand.reg 0 : Operand 32).read s) ^^^
      (Operand.reg 0 : Operand 32).read s).setWidth 64 ∧
      (0 : BitVec 64) = (((Operand.reg 14 : Operand 32).read s) ^^^
      (Operand.reg 14 : Operand 32).read s).setWidth 64 ∧
      (0 : BitVec 64) = (((Operand.reg 5 : Operand 32).read s) ^^^
      (Operand.reg 5 : Operand 32).read s).setWidth 64
    simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, and_self]
  · intro i; cases i <;> x86_norm [finalizeResetEmptyEffect]
  · x86_norm [finalizeResetEmptyEffect]

def finalizeResetClampPrefixEffect (s : RamState) : Effect where
  rip := 0x100d32
  writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s - 1⟩,
    ⟨(.reg 0 : Operand 64), (Operand.reg 12 : Operand 64).read s - 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 5 : Operand 64).read s - 1)
    ((Operand.reg 12 : Operand 64).read s - 1)))

theorem finalizeReset_clamp_prefix [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100d27)
      (codeRange 0x100d27 [0x48, 0xff, 0xcd, 0x49, 0x8d, 0x44, 0x24, 0xff,
        0x48, 0x39, 0xc5]) finalizeResetClampPrefixEffect := by
  have hFirst := dec_r64_effect_step 0x100d27 0x48 0xcd
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (decR64Effect 0x100d27 5) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd2a (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x100d2a 0x49
    (by unfold RexWPrefix; decide) 0 (.sib 12 none 0 (.d8 (-1)))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100d27) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd2f (by decide +kernel)
  md5_run_then (cmp_r64_r64_effect_step 0x100d2f 0x48 0xc5
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100d27) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd32 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [finalizeResetClampPrefixEffect, decR64Effect]
  · x86_norm [finalizeResetClampPrefixEffect, decR64Effect]
  · intro i; cases i <;> x86_norm [finalizeResetClampPrefixEffect, decR64Effect]
  · x86_norm [finalizeResetClampPrefixEffect, decR64Effect]

theorem finalizeReset_count_store_common {initial s t : RamState}
    (hFrame : PrologueFrame 0x100cb0 TwoMessages.finalizeIntoResetSlices.minStackBytes initial)
    (h : PrologueCommon 312 8 184 200 208 TwoMessages.finalizeIntoResetSlices.minStackBytes .r8 initial s)
    (hTail : AgreesExcept [.mem (stackPtr s + 192) 8, .rip] s t) :
    PrologueCommon 312 8 184 200 208 TwoMessages.finalizeIntoResetSlices.minStackBytes .r8 initial t := by
  have hNat : (stackPtr s).toNat = (stackPtr initial).toNat - 360 := by
    rw [h.rsp]
    exact hFrame.slot_toNat 360 (by decide +kernel)
  have hUpper : (stackPtr s).toNat + 368 < 2^32 := by
    have hb := hFrame.stack.1
    have hu := hFrame.stack.2.2.1
    change TwoMessages.finalizeIntoResetSlices.minStackBytes ≤ (stackPtr initial).toNat at hu
    change (stackPtr initial).toNat - TwoMessages.finalizeIntoResetSlices.minStackBytes +
      ((stackPtr initial).toNat + 8 -
        ((stackPtr initial).toNat - TwoMessages.finalizeIntoResetSlices.minStackBytes)) < 2^32 at hb
    have hBudget : TwoMessages.finalizeIntoResetSlices.minStackBytes = 680 := by decide +kernel
    rw [hBudget] at hu hb
    omega
  have hAddress (offset : Nat) (ho : offset ≤ 368) :
      (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega),
      Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by omega)]
  have hContext : (stackPtr s + 8).toNat = (stackPtr s).toNat + 8 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hAddress 8 (by decide)
  have hRsp : stackPtr t = stackPtr s := hTail.read (n := 64) (r := 4) (by simp)
  have hStoreFrame : MemoryWriteFrame s t #v[⟨(stackPtr s).toNat + 192, 8⟩] := by
    apply hTail.memoryWriteFrame
    intro c hc address hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨⟨(stackPtr s).toNat + 192, 8⟩, by simp, ?_⟩
      apply contains_of_mem_covers (by
        change (stackPtr s).toNat + 192 + 8 < 2^32
        omega)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat] using hcov
    · exact False.elim hcov
  have hRead (offset bits : Nat) (ho : offset + bits / 8 ≤ 368)
      (hgap : offset + bits / 8 ≤ 192 ∨ 200 ≤ offset) :
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand bits).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand bits).read s := by
    apply memoryRead_of_memoryWriteFrame (region := ⟨(stackPtr s).toNat + offset, bits / 8⟩)
      hStoreFrame
    · change (stackPtr s).toNat + offset + bits / 8 < 2^32
      omega
    · rw [hAddress offset (by omega)]
      exact Nat.le_refl _
    · rw [hAddress offset (by omega)]
      exact Nat.le_refl _
    · intro r hr address ha hc
      have he : r = ⟨(stackPtr s).toNat + 192, 8⟩ := by simpa using hr
      subst r
      change (stackPtr s).toNat + offset ≤ address ∧
        address < (stackPtr s).toNat + offset + bits / 8 at ha
      change (stackPtr s).toNat + 192 ≤ address ∧
        address < (stackPtr s).toNat + 192 + 8 at hc
      omega
  have hTailWide : AgreesExcept (prologueChanges initial TwoMessages.finalizeIntoResetSlices.minStackBytes) s t := by
    apply hTail.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases hm
      · simp [prologueChanges]
    · intro address c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have hcov' : (Component.mem (stackPtr initial - 168) 8).Covers address := by
          simpa only [h.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Nat.reduceAdd] using hcov
        exact ⟨.mem (BitVec.ofNat 64 (Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes).start)
          TwoMessages.finalizeIntoResetSlices.minStackBytes, by simp [prologueChanges],
          prologue_covers_of_contains (region :=
            ⟨(Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes).start,
              TwoMessages.finalizeIntoResetSlices.minStackBytes⟩)
            (hFrame.covers_in_stack 168 8 (by decide +kernel) (by decide) hcov')⟩
      · exact False.elim hcov
  have hAgrees : AgreesExcept (prologueChanges initial TwoMessages.finalizeIntoResetSlices.minStackBytes) initial t :=
    (h.agrees.trans hTailWide).mono (by simp)
  refine {
    rsp := hRsp.trans h.rsp
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    absorbed := ?absorbed
    agrees := hAgrees
    memoryFrame := prologue_memoryFrame hFrame hAgrees
  }
  case saved =>
    intro i
    rw [hRsp]
    exact (hRead (312 + 8 * i.val) 64 (by have := i.isLt; omega) (by omega)).trans (h.saved i)
  case output =>
    rw [hRsp]
    exact (hRead 184 64 (by decide) (by decide)).trans h.output
  case pointer =>
    rw [hRsp]
    exact (hRead 200 64 (by decide) (by decide)).trans h.pointer
  case length =>
    rw [hRsp]
    exact (hRead 208 64 (by decide) (by decide)).trans h.length
  case returnSlot =>
    rw [hRsp]
    exact (hRead 360 64 (by decide) (by decide)).trans h.returnSlot
  case absorbed =>
    rw [hRsp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Md5.Proofs.hasBytes_of_memoryWriteFrame hStoreFrame h.absorbed.buffer
      · change (stackPtr s + 8).toNat + 64 + 16 < 2^32
        rw [hContext]
        omega
      · intro r hr address ha hc
        have he : r = ⟨(stackPtr s).toNat + 192, 8⟩ := by simpa using hr
        subst r
        change (stackPtr s + 8).toNat + 64 ≤ address ∧
          address < (stackPtr s + 8).toNat + 64 + 16 at ha
        rw [hContext] at ha
        change (stackPtr s).toNat + 192 ≤ address ∧
          address < (stackPtr s).toNat + 192 + 8 at hc
        omega
    · change (⟨(stackPtr s + 8).toNat, 0⟩ : MemoryRegion).HasBytes t.external ByteArray.empty
      exact ⟨rfl, fun i ↦ Fin.elim0 i⟩
    · calc
        (Operand.mem (stackPtr s + 8 + 63) : Operand 8).read t =
            (Operand.mem (stackPtr s + 8 + 63) : Operand 8).read s := by
          simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            hRead 71 8 (by decide) (by decide)
        _ = _ := h.absorbed.position
    · calc
        (Operand.mem (stackPtr s + 8 + 80) : Operand 64).read t =
            (Operand.mem (stackPtr s + 8 + 80) : Operand 64).read s := by
          simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            hRead 88 64 (by decide) (by decide)
        _ = _ := h.absorbed.blocks

def finalizeResetClampSuffixEffect (s : RamState) : Effect where
  rip := 0x100d68
  writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s + 1⟩,
    ⟨(.reg 15 : Operand 64), 0⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem finalizeReset_clamp_suffix [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100d36)
      (codeRange 0x100d36 [0x48, 0xff, 0xc5, 0x45, 0x31, 0xff, 0xeb, 0x2a])
      finalizeResetClampSuffixEffect := by
  have hFirst := inc_r64_effect_step 0x100d36 0x48 0xc5
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  change StepEffect _ _ (incR64Effect 0x100d36 5) at hFirst
  md5_run_begin hFirst
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd39 (by decide +kernel)
  md5_run_then (xor_r32_r32_rex_effect_step 0x100d39 0x45 0xff
    (by unfold RexNoWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100d36) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd3c (by decide +kernel)
  md5_run_then (jmp_rel8_effect_step 0x100d3c 0x2a (by decide +kernel))
  case mid => intro s t _ hE _; exact ⟨hE.rip, jmpEffect_avoids _ _ _ _⟩
  case sub => exact codeRange_mem_of_drop (p := 0x100d36) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd68 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [finalizeResetClampSuffixEffect]
  · x86_norm [finalizeResetClampSuffixEffect]
    change (0 : BitVec 64) = (((Operand.reg 15 : Operand 32).read s) ^^^
      (Operand.reg 15 : Operand 32).read s).setWidth 64
    simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [finalizeResetClampSuffixEffect]
  · x86_norm [finalizeResetClampSuffixEffect]

theorem finalizeReset_clamp_branch [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100d27) (hOutside : ¬ InProgram boundary.rip)
    (hFirst : (Operand.reg 5 : Operand 64).read s ≠ 0)
    (hCount : (Operand.reg 12 : Operand 64).read s ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x100d68 ∧
      (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64
        (min ((Operand.reg 5 : Operand 64).read s).toNat
          ((Operand.reg 12 : Operand 64).read s).toNat) ∧
      (Operand.reg 15 : Operand 64).read t = 0 ∧
      AgreesExcept [.reg 0, .reg 5, .reg 15, .flags, .rip] s t := by
  obtain ⟨n, u, hPrefix, hu, _, hEPrefix⟩ :=
    finalizeReset_clamp_prefix boundary hOutside s hReady
      (program_text_slice hCode 0xd27 11 (by decide +kernel)) hRip
  have hCodeU := hEPrefix.codeIn (Effect.Avoids.of_noMem (by
    simp [finalizeResetClampPrefixEffect, Effect.components, Component.Covers]) _) hCode
  obtain ⟨v, hMove, hv, hEMove⟩ :=
    (cmovae_rbp_rax_effect_step 0x100d32).advances hu
      (program_text_slice hCodeU 0xd32 4 (by decide +kernel)) hEPrefix.rip
      (text_address_ne_return hOutside 0xd36 (by decide +kernel))
  have hCodeV := hEMove.codeIn (Effect.Avoids.of_noMem (by
    simp [cmovaeR64R64Effect, Effect.components, Component.Covers]) _) hCodeU
  obtain ⟨m, t, hSuffix, ht, _, hESuffix⟩ :=
    finalizeReset_clamp_suffix boundary hOutside v hv
      (program_text_slice hCodeV 0xd36 8 (by decide +kernel)) hEMove.rip
  have hW := hEPrefix.writes
  change (Operand.reg 5 : Operand 64).read u = (Operand.reg 5 : Operand 64).read s - 1 ∧
    (Operand.reg 0 : Operand 64).read u = (Operand.reg 12 : Operand 64).read s - 1 at hW
  have hCF : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      (cmpSpec ((Operand.reg 5 : Operand 64).read s - 1)
        ((Operand.reg 12 : Operand 64).read s - 1)).CF := by
    simpa only [Effect.flag, finalizeResetClampPrefixEffect, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, FlagAllows] using hEPrefix.flag .CF
  have hBP := hEMove.writes
  change (Operand.reg 5 : Operand 64).read v =
    if !(StatusFlags.ofRFLAGS u.RFLAGS).CF then (Operand.reg 0 : Operand 64).read u
    else (Operand.reg 5 : Operand 64).read u at hBP
  rw [hCF, hW.1, hW.2] at hBP
  have hWSuffix := hESuffix.writes
  change (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read v + 1 ∧
    (Operand.reg 15 : Operand 64).read t = 0 at hWSuffix
  refine ⟨n + 1 + m, t, (hPrefix.trans hMove).trans hSuffix, ht,
    hESuffix.codeIn (Effect.Avoids.of_noMem (by
      simp [finalizeResetClampSuffixEffect, Effect.components, Component.Covers]) _) hCodeV,
    hESuffix.rip, ?_, hWSuffix.2, ?_⟩
  · rw [hWSuffix.1, hBP]
    exact reset_clamp_value _ _ hFirst hCount
  · exact ((hEPrefix.agrees.trans hEMove.agrees).trans hESuffix.agrees).mono (by
      simp [finalizeResetClampPrefixEffect, cmovaeR64R64Effect, finalizeResetClampSuffixEffect, Effect.components])

def finalizeResetDispatchPrefixEffect (first count : BitVec 64) (s : RamState) : Effect :=
  let a : BitVec 8 := if first = 0 then 1 else 0
  let b : BitVec 8 := if count = 0 then 1 else 0
  { rip := 0x100d19
    writes := [⟨(.reg 0 : Operand 64), mergeGPR 8 a ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), mergeGPR 8 (b ||| a) ((Operand.reg 1 : Operand 64).read s)⟩]
    flags := some (andFlags (b ||| a)) }

theorem finalizeReset_dispatch_prefix [Bindings] (first count : BitVec 64)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x100d0b ∧ (Operand.reg 1 : Operand 64).read s = first ∧
        (Operand.reg 6 : Operand 64).read s = count)
      (codeRange 0x100d0b [0x48, 0x85, 0xc9, 0x0f, 0x94, 0xc0, 0x48,
        0x85, 0xf6, 0x0f, 0x94, 0xc1, 0x08, 0xc1])
      (finalizeResetDispatchPrefixEffect first count) := by
  have hTestA := test_r64_r64_effect_step 0x100d0b 0x48 0xc9
    (by unfold RexWPrefix; decide) (by decide)
  change StepEffect _ _ (testR64R64Effect 0x100d0b 1 1) at hTestA
  have hTestB := test_r64_r64_effect_step 0x100d11 0x48 0xf6
    (by unfold RexWPrefix; decide) (by decide)
  change StepEffect _ _ (testR64R64Effect 0x100d11 6 6) at hTestB
  md5_run_begin hTestA
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd0e (by decide +kernel)
  md5_run_then (sete_al_fixed_effect_step 0x100d0e (decide (first = 0)))
  case sub => exact codeRange_mem_of_drop (p := 0x100d0b) 3 (by decide +kernel)
  case mid =>
    intro s t h hE _
    refine ⟨⟨hE.rip, ?_⟩, setzR8FixedEffect_avoids _ _ _ _ _⟩
    simpa only [Effect.flag, testR64R64Effect, testFlags, StatusFlagsOutcome.get,
      StatusFlags.get, FlagAllows, BitVec.and_self, Bool.beq_eq_decide_eq, h.2.1]
      using hE.flag .ZF
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd11 (by decide +kernel)
  md5_run_then hTestB
  case sub => exact codeRange_mem_of_drop (p := 0x100d0b) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd14 (by decide +kernel)
  md5_run_then (sete_cl_fixed_effect_step 0x100d14 (decide (count = 0)))
  case sub => exact codeRange_mem_of_drop (p := 0x100d0b) 9 (by decide +kernel)
  case mid =>
    intro s t h hE _
    refine ⟨⟨hE.rip, ?_⟩, setzR8FixedEffect_avoids _ _ _ _ _⟩
    have hz := hE.flag .ZF
    x86_norm [Effect.flag, testFlags, StatusFlagsOutcome.get, StatusFlags.get, FlagAllows,
      BitVec.and_self, Bool.beq_eq_decide_eq, h.2.2] at hz
    exact hz
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd17 (by decide +kernel)
  md5_run_then (or_cl_al_effect_step 0x100d17)
  case sub => exact codeRange_mem_of_drop (p := 0x100d0b) 12 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd19 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t h hE
  apply hE.weaken
  · x86_norm [finalizeResetDispatchPrefixEffect, decide_eq_true_iff]
  · x86_norm [finalizeResetDispatchPrefixEffect, decide_eq_true_iff]
  · intro i; cases i <;> x86_norm [finalizeResetDispatchPrefixEffect, decide_eq_true_iff]
  · x86_norm [finalizeResetDispatchPrefixEffect, decide_eq_true_iff]

def finalizeResetCountEffect (s : RamState) : Effect where
  rip := 0x100d21
  writes := [⟨(.mem (stackPtr s + 192) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩]

theorem finalizeReset_count_effect_step [Bindings] :
    StepEffect (Memory.StorePre 0x100d19 8 (fun s ↦ stackPtr s + 192) 8)
      (codeRange 0x100d19 [0x48, 0x89, 0xb4, 0x24, 0xc0, 0, 0, 0]) finalizeResetCountEffect := by
  exact Buffered.Stores.mov_m64_r64_effect_step 0x100d19 0x48
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 192))
    (by decide) (by decide) (by decide)

theorem finalizeReset_dispatched [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hFrame : PrologueFrame 0x100cb0 TwoMessages.finalizeIntoResetSlices.minStackBytes s)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      PrologueCommon 312 8 184 200 208 TwoMessages.finalizeIntoResetSlices.minStackBytes .r8 s t ∧
      t.RIP = (if (Operand.reg 1 : Operand 64).read s = 0 ∨
        (Operand.reg 6 : Operand 64).read s = 0 then 0x100e37 else 0x100d27) ∧
      (Operand.reg 5 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s ∧
      (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s ∧
      (Operand.mem (stackPtr t + 192) : Operand 64).read t =
        (Operand.reg 6 : Operand 64).read s := by
  obtain ⟨n, u, hInit, hu, hCodeU, hE⟩ :=
    finalizeReset_initialized boundary hReady hCode hFrame hOutside
  have hCommonU := finalizeReset_initialized_common hFrame hE
  have hFirstU : (Operand.reg 1 : Operand 64).read u =
      (Operand.reg 1 : Operand 64).read s :=
    hE.agrees.read (by x86_norm [prologuePushEffect, finalizeResetInitEffect])
  have hCountU : (Operand.reg 6 : Operand 64).read u =
      (Operand.reg 6 : Operand 64).read s :=
    hE.agrees.read (by x86_norm [prologuePushEffect, finalizeResetInitEffect])
  have hW := hE.writes
  x86_norm [prologuePushEffect, finalizeResetInitEffect] at hW
  rcases hW with ⟨_, _, _, _, _, _, _, _, hBP, _, hN, _, _, _, _, _, _⟩
  obtain ⟨m, v, hPrefix, hv, _, hEPrefix⟩ :=
    finalizeReset_dispatch_prefix ((Operand.reg 1 : Operand 64).read s)
      ((Operand.reg 6 : Operand 64).read s) boundary hOutside u hu
      (program_text_slice hCodeU 0xd0b 14 (by decide +kernel)) ⟨hE.rip, hFirstU, hCountU⟩
  have hCodeV := hEPrefix.codeIn (Effect.Avoids.of_noMem (by
    simp [finalizeResetDispatchPrefixEffect, Effect.components, Component.Covers]) _) hCodeU
  have hPrefixAgrees : AgreesExcept prologueTailChanges u v := hEPrefix.agrees.mono (by
    simp [prologueTailChanges, finalizeResetDispatchPrefixEffect, Effect.components])
  have hCommonV := hCommonU.of_registers hPrefixAgrees
  have hStoreAddress : stackPtr v + 192 = stackPtr s - 168 := by
    rw [hCommonV.rsp]
    simp only [Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have hWrite : Memory.MemWritable v (stackPtr v + 192) 8 := by
    rw [hStoreAddress]
    have hw := hFrame.writable 168 8 (by decide +kernel) (by decide)
    exact ⟨hw.low, fun i hi ↦ hCommonV.agrees.grow _ (hw.bytes i hi), hw.tables⟩
  have hApart : RangeApart (stackPtr v + 192) 8 0x100d19 8 := by
    rw [hStoreAddress]
    exact hFrame.apart 168 8 (by decide +kernel) (by decide) 0x100d19
      [0x48, 0x89, 0xb4, 0x24, 0xc0, 0, 0, 0]
      (prologue_text_sub 0xd19 8 (by decide +kernel))
  obtain ⟨w, hStore, hw, hEStore⟩ := finalizeReset_count_effect_step.advances hv
    (program_text_slice hCodeV 0xd19 8 (by decide +kernel))
    ⟨hEPrefix.rip, hWrite, hApart⟩
    (text_address_ne_return hOutside 0xd21 (by decide +kernel))
  have hStoreAgrees : AgreesExcept [.mem (stackPtr v + 192) 8, .rip] v w := by
    simpa [finalizeResetCountEffect, Effect.components] using hEStore.agrees
  have hStoreRsp : stackPtr w = stackPtr v := hStoreAgrees.read (n := 64) (r := 4) (by simp)
  have hCommonW := finalizeReset_count_store_common hFrame hCommonV hStoreAgrees
  have hCodeW := hEStore.codeIn (by
    intro x hx c hc hcov
    have hc' : c = .mem (stackPtr v + 192) 8 ∨ c = .rip := by
      simpa [finalizeResetCountEffect, Effect.components] using hc
    rcases hc' with rfl | rfl
    · apply hFrame.avoids_mem 168 8 (by decide +kernel) (by decide) x hx
      rw [hStoreAddress] at hcov
      simpa only [BitVec.ofNat_eq_ofNat] using hcov
    · exact False.elim hcov) hCodeV
  have hZFPrefix : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (((if (Operand.reg 6 : Operand 64).read s = 0 then (1 : BitVec 8) else 0) |||
        (if (Operand.reg 1 : Operand 64).read s = 0 then 1 else 0)) == 0) := by
    simpa only [Effect.flag, finalizeResetDispatchPrefixEffect, andFlags,
      StatusFlagsOutcome.get, StatusFlags.get, FlagAllows] using hEPrefix.flag .ZF
  have hZFW : (StatusFlags.ofRFLAGS w.RFLAGS).ZF =
      decide (¬ ((Operand.reg 1 : Operand 64).read s = 0 ∨
        (Operand.reg 6 : Operand 64).read s = 0)) := by
    have hZFStore : (StatusFlags.ofRFLAGS w.RFLAGS).ZF = (StatusFlags.ofRFLAGS v.RFLAGS).ZF := by
      simpa only [Effect.flag, finalizeResetCountEffect, StatusFlagsOutcome.get,
        StatusFlags.get, FlagAllows] using hEStore.flag .ZF
    exact hZFStore.trans (hZFPrefix.trans (reset_dispatch_zero_value _ _))
  obtain ⟨t, hJump, ht, hEJump⟩ :=
    (jcc_rel32_effect_step 0x100d21 5 0x110).advances hw
      (program_text_slice hCodeW 0xd21 6 (by decide +kernel))
      ⟨hEStore.rip, fun _ ↦ by decide +kernel⟩ (by
        change (if !(StatusFlags.ofRFLAGS w.RFLAGS).ZF then 0x100e37 else 0x100d27) ≠ boundary.rip
        split
        · exact text_address_ne_return hOutside 0xe37 (by decide +kernel)
        · exact text_address_ne_return hOutside 0xd27 (by decide +kernel))
  have hJumpAgrees : AgreesExcept [.rip] w t := hEJump.agrees
  have hJumpRsp : stackPtr t = stackPtr w := hJumpAgrees.read (n := 64) (r := 4) (by simp)
  have hCommonT := hCommonW.of_registers (hJumpAgrees.mono (by simp [prologueTailChanges]))
  refine ⟨n + m + 1 + 1, t, ((hInit.trans hPrefix).trans hStore).trans hJump,
    ht, hEJump.codeIn (branchEffect_avoids _ _ _ _) hCodeW, hCommonT, ?_, ?_, ?_, ?_⟩
  · have hr := hEJump.rip
    change t.RIP = if !(StatusFlags.ofRFLAGS w.RFLAGS).ZF then 0x100e37 else 0x100d27 at hr
    rw [hZFW] at hr
    simpa only [decide_not, Bool.not_not, decide_eq_true_iff] using hr
  · exact (hJumpAgrees.read (n := 64) (r := 5) (by simp)).trans
      ((hStoreAgrees.read (n := 64) (r := 5) (by simp)).trans
        ((hEPrefix.agrees.read (n := 64) (r := 5) (by
          simp [finalizeResetDispatchPrefixEffect, Effect.components])).trans hBP))
  · exact (hJumpAgrees.read (n := 64) (r := 12) (by simp)).trans
      ((hStoreAgrees.read (n := 64) (r := 12) (by simp)).trans
        ((hEPrefix.agrees.read (n := 64) (r := 12) (by
          simp [finalizeResetDispatchPrefixEffect, Effect.components])).trans hN))
  · have hMemory := hJumpAgrees.external (by simp [Component.Covers])
    rw [hJumpRsp, hStoreRsp]
    have hStored : (Operand.mem (stackPtr v + 192) : Operand 64).read w =
        (Operand.reg 6 : Operand 64).read v := hEStore.writes
    have hCountV : (Operand.reg 6 : Operand 64).read v =
        (Operand.reg 6 : Operand 64).read u := hEPrefix.agrees.read (by
      simp [finalizeResetDispatchPrefixEffect, Effect.components])
    simpa only [Operand.read, hMemory] using hStored.trans (hCountV.trans hCountU)

theorem finalizeReset_prologue_of_ready [bindings : Bindings] {s : RamState}
    {inputs : Array Slices.Input} {first : Nat} (boundary : ReturnBoundary)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hCall : (TwoMessages.ValidCall TwoMessages.finalizeIntoResetSlices) bindings s inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ finalizeResetProloguePost s inputs first t := by
  have hFrame : PrologueFrame 0x100cb0 TwoMessages.finalizeIntoResetSlices.minStackBytes s :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable,
      (hCall.separation.2 (Stack.region s TwoMessages.finalizeIntoResetSlices.minStackBytes) (by simp)).2⟩
  obtain ⟨n, u, hDispatch, hu, hCodeU, hCommonU, hRipU, hBPU, hCountU, hTotalU⟩ :=
    finalizeReset_dispatched boundary hReady hCode hFrame hOutside
  have hFirstNat : ((Operand.reg 1 : Operand 64).read s).toNat = first := hCall.firstCountArgumentMatchesFirst
  have hCountNat : ((Operand.reg 6 : Operand 64).read s).toNat = inputs.size :=
    hCall.inputsInMemory.countArgument
  have hFirstZero : (Operand.reg 1 : Operand 64).read s = 0 ↔ first = 0 := by
    rw [BitVec.toNat_eq, hFirstNat]
    rfl
  have hCountZero : (Operand.reg 6 : Operand 64).read s = 0 ↔ inputs.size = 0 := by
    rw [BitVec.toNat_eq, hCountNat]
    rfl
  have hCountValue : (Operand.reg 6 : Operand 64).read s = BitVec.ofNat 64 inputs.size := by
    have hh := congrArg (BitVec.ofNat 64) hCountNat
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh
  have hEmptyIff : ((Operand.reg 1 : Operand 64).read s = 0 ∨
      (Operand.reg 6 : Operand 64).read s = 0) ↔ min first inputs.size = 0 := by
    rw [hFirstZero, hCountZero, Nat.min_eq_zero_iff]
  obtain ⟨m, t, hTail, ht, hCodeT, hRipT, hBPT, hIndexT, hEmptyT, hTailAgrees⟩ :
      ∃ m t, Advances boundary m u t ∧ ReadyToStep t ∧
        CodeIn Extracted.programImage t ∧
        t.RIP = (if min first inputs.size = 0 then 0x100e56 else 0x100d68) ∧
        (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64 (min first inputs.size) ∧
        (min first inputs.size ≠ 0 → (Operand.reg 15 : Operand 64).read t = 0) ∧
        (min first inputs.size = 0 → (Operand.reg 0 : Operand 64).read t = 0 ∧
          (Operand.reg 14 : Operand 64).read t = 0) ∧
        AgreesExcept [.reg 0, .reg 5, .reg 14, .reg 15, .flags, .rip] u t := by
    by_cases hEmpty : min first inputs.size = 0
    · have hRip : u.RIP = 0x100e37 := by
        simpa only [hEmptyIff.mpr hEmpty, ite_true] using hRipU
      obtain ⟨m, t, hTail, ht, _, hETail⟩ := finalizeReset_empty_branch boundary hOutside u hu
        (program_text_slice hCodeU 0xe37 9 (by decide +kernel)) hRip
      have hW := hETail.writes
      change (Operand.reg 0 : Operand 64).read t = 0 ∧
        (Operand.reg 14 : Operand 64).read t = 0 ∧
        (Operand.reg 5 : Operand 64).read t = 0 at hW
      refine ⟨m, t, hTail, ht, hETail.codeIn (Effect.Avoids.of_noMem (by
        simp [finalizeResetEmptyEffect, Effect.components, Component.Covers]) _) hCodeU,
        ?_, ?_, ?_, ?_, hETail.agrees.mono (by
          simp [finalizeResetEmptyEffect, Effect.components])⟩
      · simpa only [hEmpty, ite_true, finalizeResetEmptyEffect] using hETail.rip
      · simpa only [hEmpty, BitVec.ofNat_eq_ofNat] using hW.2.2
      · intro h; exact False.elim (h hEmpty)
      · intro _; exact ⟨hW.1, hW.2.1⟩
    · have hOriginal : ¬ ((Operand.reg 1 : Operand 64).read s = 0 ∨
          (Operand.reg 6 : Operand 64).read s = 0) := fun hz ↦ hEmpty (hEmptyIff.mp hz)
      have hRip : u.RIP = 0x100d27 := by simpa only [hOriginal, ite_false] using hRipU
      have hFirstNonzero : (Operand.reg 5 : Operand 64).read u ≠ 0 :=
        fun hz ↦ hOriginal (.inl (hBPU.symm.trans hz))
      have hCountNonzero : (Operand.reg 12 : Operand 64).read u ≠ 0 :=
        fun hz ↦ hOriginal (.inr (hCountU.symm.trans hz))
      obtain ⟨m, t, hTail, ht, hCodeT, hRipT, hBound, hIndex, hAgrees⟩ :=
        finalizeReset_clamp_branch boundary hu hCodeU hRip hOutside hFirstNonzero hCountNonzero
      refine ⟨m, t, hTail, ht, hCodeT, ?_, ?_, fun _ ↦ hIndex,
        fun hz ↦ False.elim (hEmpty hz), hAgrees.mono (by simp)⟩
      · simpa only [hEmpty, ite_false] using hRipT
      · rw [hBPU, hCountU, hFirstNat, hCountNat] at hBound
        exact hBound
  have hCommonT := hCommonU.of_registers (hTailAgrees.mono (by simp [prologueTailChanges]))
  have hRspTail : stackPtr t = stackPtr u :=
    hTailAgrees.read (n := 64) (r := 4) (by simp)
  have hMemory : t.external = u.external :=
    hTailAgrees.external (by simp [Component.Covers])
  refine ⟨n + m, t, hDispatch.trans hTail, ht, hCodeT, ?_⟩
  refine {
    toPrologueCommon := hCommonT
    rip := hRipT
    total := ?total
    bound := hBPT
    count := ?count
    index := hIndexT
    empty := hEmptyT
  }
  case total =>
    rw [hRspTail]
    simpa only [Operand.read, hMemory] using hTotalU.trans hCountValue
  case count =>
    exact (hTailAgrees.read (n := 64) (r := 12) (by simp)).trans (hCountU.trans hCountValue)


end Md5.Proofs.Streaming
