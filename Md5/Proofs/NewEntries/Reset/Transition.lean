import Md5.Proofs.Streaming.Transport
import Md5.Proofs.Streaming.Prologue
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Lea.Triple

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Block Md5.Proofs.Buffered

attribute [local x86_compose] movM8Imm8Effect

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_local] movM8Imm8Effect_local

def resetBytes : List UInt8 :=
  [0x48, 0x8d, 0x44, 0x24, 0x60, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x38,
   0x48, 0xc7, 0x44, 0x24, 0x70, 0, 0, 0, 0, 0xc6, 0x44, 0x24, 0x5f, 0]

structure ResetPre (s : RamState) : Prop extends Finalize.Storage .slices s where
  rip : s.RIP = 0x1014e0

def resetEffect (s : RamState) : Effect where
  rip := 0x1014fa
  writes := [⟨(.reg 0 : Operand 64), stackPtr s + 96⟩,
    ⟨(.mem (stackPtr s + 104) : Operand 64), (.reg 2 : Operand 64).read s⟩,
    ⟨(.mem (stackPtr s + 96) : Operand 64), (.reg 7 : Operand 64).read s⟩,
    ⟨(.mem (stackPtr s + 112) : Operand 64), 0⟩,
    ⟨(.mem (stackPtr s + 95) : Operand 8), 0⟩]

set_option maxHeartbeats 400000 in
theorem reset_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ResetPre (codeRange 0x1014e0 resetBytes) resetEffect := by
  unfold resetBytes
  md5_run_begin (lea_r64_effect_step 0x1014e0 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide))
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14e5 (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step 0x1014e5 0x48
    (by unfold RexWPrefix; decide) 2 (.base 0 (.d8 8))
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1014e0) 5 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 104 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 104) (len := 8)
        (codeOffset := 0x14e5) (codeLen := 4) (by decide) (by decide +kernel)
    · have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      have ha : (.reg 0 : Operand 64).read t = stackPtr s + 96 := by
        have hh := (hO true).read_reg (n := 64) (0#5)
        x86_norm at hh
        exact hh.symm
      x86_avoid
      change RangeApart ((.reg 0 : Operand 64).read t + 8) 8 0x1014e0 26
      rw [ha]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact h.toStorage.stackApart (offset := 104) (len := 8)
          (codeOffset := 0x14e0) (codeLen := 26) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14e9 (by decide +kernel)
  md5_run_then (Stores.mov_m64_r64_effect_step 0x1014e9 0x48
    (by unfold RexWPrefix; decide) 7 (.base 0 .none)
    (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x1014e0) 9 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 96 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 96) (len := 8)
        (codeOffset := 0x14e9) (codeLen := 3) (by decide) (by decide +kernel)
    · have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      have ha : (.reg 0 : Operand 64).read t = stackPtr s + 96 := by
        have hh := (hO true).read_reg (n := 64) (0#5)
        x86_norm at hh
        exact hh.symm
      x86_avoid
      change RangeApart ((.reg 0 : Operand 64).read t) 8 0x1014e0 26
      rw [ha]
      exact h.toStorage.stackApart (offset := 96) (len := 8)
          (codeOffset := 0x14e0) (codeLen := 26) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14ec (by decide +kernel)
  md5_run_then (Stores.mov_m64_imm32_effect_step 0x1014ec 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 112))
    (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1014e0) 12 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 112 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 112) (len := 8)
        (codeOffset := 0x14ec) (codeLen := 9) (by decide) (by decide +kernel)
    · have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      have ha : (.reg 0 : Operand 64).read t = stackPtr s + 96 := by
        have hh := (hO true).read_reg (n := 64) (0#5)
        x86_norm at hh
        exact hh.symm
      x86_avoid
      change RangeApart (stackPtr t + 112) 8 0x1014e0 26
      rw [hsp]
      exact h.toStorage.stackApart (offset := 112) (len := 8)
          (codeOffset := 0x14e0) (codeLen := 26) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14f5 (by decide +kernel)
  md5_run_then (Stores.mov_m8_imm8_effect_step 0x1014f5
    (.sib 4 none 0 (.d8 95)) (by decide) (by decide) (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1014e0) 21 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 95 1 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 95) (len := 1)
        (codeOffset := 0x14f5) (codeLen := 5) (by decide) (by decide +kernel)
    · have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      have ha : (.reg 0 : Operand 64).read t = stackPtr s + 96 := by
        have hh := (hO true).read_reg (n := 64) (0#5)
        x86_norm at hh
        exact hh.symm
      x86_avoid
      change RangeApart (stackPtr t + 95) 1 0x1014e0 26
      rw [hsp]
      exact h.toStorage.stackApart (offset := 95) (len := 1)
          (codeOffset := 0x14e0) (codeLen := 26) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14fa (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [resetEffect]
  · x86_norm [resetEffect, BitVec.add_zero]
    simp [Operand.read_reg64, gprNumber, rexR]
  · intro i; cases i <;> x86_norm [resetEffect]
  · x86_norm [resetEffect, BitVec.add_zero]


theorem reset_absorbed {s t : RamState} (hs : Finalize.Storage .slices s)
    (he : (resetEffect s).Holds s t)
    (hLow : (.reg 7 : Operand 64).read s = 0xefcdab8967452301)
    (hHigh : (.reg 2 : Operand 64).read s = 0x1032547698badcfe) :
    Absorbed (stackPtr t + 32) ByteArray.empty t := by
  have hsp : stackPtr t = stackPtr s := he.agrees.read (n := 64) (r := 4)
    (by simp [resetEffect, Effect.components])
  have ht := hs.of_agrees he.agrees hsp
  apply Streaming.absorbed_empty_of_initial_words (stackPtr t + 32)
  · simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (ht.stackWritable 96 16 (by decide)).readable
  · have hl : (.mem (stackPtr s + 96) : Operand 64).read t =
        (.reg 7 : Operand 64).read s := he.writes.2.2.1
    rw [hsp, BitVec.add_assoc]
    exact hl.trans hLow
  · have hh : (.mem (stackPtr s + 104) : Operand 64).read t =
        (.reg 2 : Operand 64).read s := he.writes.2.1
    rw [hsp, BitVec.add_assoc]
    exact hh.trans hHigh
  · have hp : (.mem (stackPtr s + 95) : Operand 8).read t = 0 := he.writes.2.2.2.2
    rw [hsp, BitVec.add_assoc]
    exact hp
  · have hb : (.mem (stackPtr s + 112) : Operand 64).read t = 0 := he.writes.2.2.2.1
    rw [hsp, BitVec.add_assoc]
    exact hb



theorem reset_effect_covers {s : RamState} (hs : Finalize.Storage .slices s)
    {c : Component} (hc : c ∈ (resetEffect s).components) {address : BitVec 64}
    (hcov : c.Covers address) :
    (Finalize.Kind.stackRegion .slices s).Contains address.toNat := by
  simp only [resetEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.not_mem_nil,
    or_false, List.cons_append, List.nil_append, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov.elim
    | exact hs.stackCover (offset := 104) (len := 8) (by decide) hcov
    | exact hs.stackCover (offset := 96) (len := 8) (by decide) hcov
    | exact hs.stackCover (offset := 112) (len := 8) (by decide) hcov
    | exact hs.stackCover (offset := 95) (len := 1) (by decide) hcov

theorem reset_effect_avoids {s : RamState} (hs : Finalize.Storage .slices s) :
    (resetEffect s).Avoids Extracted.programImage := by
  intro x hx c hc hcov
  exact hs.stackAvoids x.1 (reset_effect_covers hs hc hcov) (.inl ⟨x.2, hx⟩)

theorem reset_frame {s t : RamState} (hs : Finalize.Storage .slices s)
    (he : (resetEffect s).Holds s t) :
    Prelude.MemoryWriteFrame s t #v[Finalize.Kind.stackRegion .slices s] := by
  apply he.agrees.memoryWriteFrame
  intro c hc address hcov
  exact ⟨_, by simp, reset_effect_covers hs hc hcov⟩

theorem reset_core_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hPre : ResetPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (resetEffect s).Holds s t := by
  obtain ⟨fuel, t, hr, ht, _, he⟩ := reset_execution boundary hOutside s hReady
    (program_text_slice hCode 0x14e0 26 (by decide +kernel)) hPre
  exact ⟨fuel, t, hr, ht, he.codeIn (reset_effect_avoids hPre.toStorage) hCode, he⟩


theorem reset_read {s t : RamState} (he : (resetEffect s).Holds s t)
    (offset : Nat) (hb : offset + 8 ≤ 2^64) (hgap : offset + 8 ≤ 95 ∨ 120 ≤ offset) :
    (.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
      (.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  have hsp : stackPtr t = stackPtr s := he.agrees.read (n := 64) (r := 4)
    (by simp [resetEffect, Effect.components])
  rw [hsp]
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply he.agrees.byte
  intro c hc hcov
  simp only [resetEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.not_mem_nil,
    or_false, List.cons_append, List.nil_append, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  all_goals
    obtain ⟨j, hj, heq⟩ := hcov
    first
    | exact RangeApart.offsets (stackPtr s) (a := offset) (len := 8)
        (b := 104) (count := 8) hb (by decide) (by omega) i hi j hj heq
    | exact RangeApart.offsets (stackPtr s) (a := offset) (len := 8)
        (b := 96) (count := 8) hb (by decide) (by omega) i hi j hj heq
    | exact RangeApart.offsets (stackPtr s) (a := offset) (len := 8)
        (b := 112) (count := 8) hb (by decide) (by omega) i hi j hj heq
    | exact RangeApart.offsets (stackPtr s) (a := offset) (len := 8)
        (b := 95) (count := 1) hb (by decide) (by omega) i hi j hj heq

theorem reset_storage {initial s t : RamState}
    (h : Streaming.PrologueStorage 312 32 288 16 24 680 .r8 initial s)
    (he : (resetEffect s).Holds s t) :
    Streaming.PrologueStorage 312 32 288 16 24 680 .r8 initial t := by
  apply Streaming.storage_of_reads h
    (he.agrees.read (n := 64) (r := 4) (by simp [resetEffect, Effect.components]))
  intro offset ho
  have hb : offset + 8 ≤ 368 ∧ (offset + 8 ≤ 95 ∨ 120 ≤ offset) := by
    simp only [Streaming.storageOffsets, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map, List.mem_range] at ho
    rcases ho with (rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> omega
  exact reset_read he offset (by omega) hb.2

end Md5.Proofs.NewEntries.Reset
