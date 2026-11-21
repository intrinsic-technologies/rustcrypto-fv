import Hkdf.Proofs.NewExpand.Expand.LoopState
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Instructions.ShiftLeft.Compose
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Prelude X86 X86.Machine
open X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions.ShiftLeft
open Hkdf.Proofs.Common.Machine

private def setupBytes : List UInt8 :=
  [0x49, 0x89, 0xcf, 0x48, 0x8b, 0x84, 0x24, 0xf0, 0, 0, 0, 0x48, 0x8d, 0x48, 0x40,
   0x48, 0x89, 0x8c, 0x24, 0xa8, 1, 0, 0, 0x48, 0x8b, 0x8c, 0x24, 0xf8, 0, 0, 0,
   0x48, 0xc1, 0xe1, 4, 0x48, 3, 0x8c, 0x24, 0xe8, 0, 0, 0,
   0x48, 0x89, 0x8c, 0x24, 0xb8, 1, 0, 0, 0x48, 0x83, 0xc0, 0x68,
   0x48, 0x89, 0x84, 0x24, 0xa0, 1, 0, 0, 0x31, 0xc0,
   0x4c, 0x8d, 0x25, 0x67, 0xea, 0xff, 0xff, 0x48, 0x8b, 0xac, 0x24, 0xe0, 0, 0, 0,
   0x48, 0xc7, 0x84, 0x24, 0, 1, 0, 0, 0, 0, 0, 0, 0xe9, 0x74, 2, 0, 0]

private def setupEffect (s : RamState) : Effect :=
  { rip := 0x10f586
    writes := [⟨(.reg 15 : Operand 64), s.regValue .rcx⟩,
      ⟨(.mem (stackPtr s + 424) : Operand 64), slot s 240 + 64⟩,
      ⟨(.reg 1 : Operand 64), (slot s 248 <<< 4) + slot s 232⟩,
      ⟨(.mem (stackPtr s + 440) : Operand 64), (slot s 248 <<< 4) + slot s 232⟩,
      ⟨(.mem (stackPtr s + 416) : Operand 64), slot s 240 + 104⟩,
      ⟨(.reg 0 : Operand 64), 0⟩,
      ⟨(.reg 12 : Operand 64), 0x10dd60⟩,
      ⟨(.reg 5 : Operand 64), slot s 224⟩,
      ⟨(.mem (stackPtr s + 256) : Operand 64), 0⟩]
    flags := some (StatusFlagsOutcome.ofFun fun _ => none) }

private structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f2b1
  readable : ∀ offset : Nat, offset ≤ 528 →
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset : Nat, offset ≤ 528 → offset % 8 = 0 →
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset : Nat, offset ≤ 528 → ∀ delta len : Nat, delta + len ≤ setupBytes.length →
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) 8
      (0x10f2b1 + BitVec.ofNat 64 delta) len

attribute [local x86_compose] shlR64Effect shlFlags stackPtr

set_option maxHeartbeats 1800000 in
private theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x10f2b1 setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10f2b1 0x49 0xcf (by simp [RexWPrefix]) rfl)
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf2b4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f2b4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 3 8
  case mid =>
    intro s t hp effect obs
    refine ⟨LoadPre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 240 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2bc (by decide))
  advance_then (lea_r64_effect_step 0x10f2bc 0x48 (by simp [RexWPrefix]) 1
    (.base 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 11 4
  case mid =>
    intro s t hp effect obs
    refine ⟨effect.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2c0 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f2c0 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 15 8
  case mid =>
    intro s t hp effect obs
    refine ⟨StorePre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 424 (by decide) (by decide)
    · x86_norm
      exact hp.codeApart 424 (by decide) 15 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 424 (by decide) 0 97 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2c8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f2c8 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 23 8
  case mid =>
    intro s t hp effect obs
    refine ⟨LoadPre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 248 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2d0 (by decide))
  advance_then (shl_r64_imm8_effect_step 0x10f2d0 0x48 0xe1 4 (by simp [RexWPrefix]) rfl rfl)
  case loc => exact shlR64Effect_local _ _ _ 4 (by decide)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 31 4
  case mid =>
    intro s t hp effect obs
    refine ⟨effect.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers, shlR64Effect_components]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2d4 (by decide))
  advance_then (add_r64_m64_effect_step 0x10f2d4 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 35 8
  case mid =>
    intro s t hp effect obs
    refine ⟨LoadPre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 232 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2dc (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f2dc 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 440)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 43 8
  case mid =>
    intro s t hp effect obs
    refine ⟨StorePre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 440 (by decide) (by decide)
    · x86_norm
      exact hp.codeApart 440 (by decide) 43 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 440 (by decide) 0 97 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2e4 (by decide))
  advance_then (add_r64_imm8_effect_step 0x10f2e4 0x48 0xc0 104 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 51 4
  case mid =>
    intro s t hp effect obs
    refine ⟨effect.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2e8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f2e8 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 416)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 55 8
  case mid =>
    intro s t hp effect obs
    refine ⟨StorePre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 416 (by decide) (by decide)
    · x86_norm
      exact hp.codeApart 416 (by decide) 55 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 416 (by decide) 0 97 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2f0 (by decide))
  advance_then (xor_r32_r32_effect_step 0x10f2f0 0xc0 rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 63 2
  case mid =>
    intro s t hp effect obs
    refine ⟨effect.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2f2 (by decide))
  advance_then (lea_r64_effect_step 0x10f2f2 0x4c (by simp [RexWPrefix]) 4
    (.rip 0xffffea67) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 65 7
  case mid =>
    intro s t hp effect obs
    refine ⟨effect.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2f9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f2f9 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 224)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 72 8
  case mid =>
    intro s t hp effect obs
    refine ⟨LoadPre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 224 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf301 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10f301 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 80 12
  case mid =>
    intro s t hp effect obs
    refine ⟨StorePre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 256 (by decide) (by decide)
    · x86_norm
      exact hp.codeApart 256 (by decide) 80 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 256 (by decide) 0 97 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf30d (by decide))
  advance_then (jmp_rel32_effect_step 0x10f30d 0x274 (by decide))
  case sub => exact codeRange_slice_subset 0x10f2b1 setupBytes 92 5
  case mid =>
    intro s t hp effect obs
    refine ⟨effect.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf586 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp effect
  apply effect.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, slot, BitVec.xor_self, BitVec.setWidth_zero]
    exact ⟨rfl, .inl ⟨rfl, rfl⟩, rfl, .inr (.inl ⟨rfl, rfl⟩),
      .inr (.inr (.inl ⟨rfl, rfl⟩)), rfl, .inr (.inr (.inr rfl))⟩
  · intro i; cases i <;> x86_norm [setupEffect, StatusFlagsOutcome.ofFun]
  · x86_norm [setupEffect]
    exact ⟨.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl)), .inr (.inr (.inr rfl))⟩

private theorem setup_store_covers {s : RamState} {c : Component} {a : BitVec 64}
    (member : c ∈ (setupEffect s).components) (covers : c.Covers a) :
    ∃ offset ∈ [424, 440, 416, 256], (Component.mem (stackPtr s + BitVec.ofNat 64 offset) 8).Covers a := by
  simp only [setupEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component_reg, Write.component_mem, Nat.reduceDiv,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact covers.elim | exact ⟨_, by decide, covers⟩

private theorem setup_agrees {s t : RamState} {start size : Nat}
    (effect : (setupEffect s).Holds s t) (bounded : start + size ≤ 2^64)
    (apart : ∀ offset ∈ [424, 440, 416, 256], start + size ≤ offset ∨ offset + 8 ≤ start) :
    (Component.mem (stackPtr s + BitVec.ofNat 64 start) size).Agrees s t := by
  intro i hi
  apply effect.agrees.memory
  intro c member covered
  obtain ⟨offset, offset_mem, j, hj, address⟩ := setup_store_covers member covered
  have bound : offset + 8 ≤ 2^64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at offset_mem
    omega
  exact RangeApart.offsets (stackPtr s) bounded bound (apart offset offset_mem) i hi j hj address

variable [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
  {key info : ByteArray} {ptr : BitVec 64} {length : Nat}

set_option maxHeartbeats 500000 in
theorem startLoop (pre : ExpandPre entry boundary key info ptr length)
    (state : DispatchState entry s boundary length) (pos : 0 < length) (bound : length ≤ 8160) :
    ∃ t, LoopState entry t boundary key info length 0 := by
  have address (offset : Nat) (h : offset ≤ 528) :
      stackPtr s + BitVec.ofNat 64 offset = stackPtr entry - BitVec.ofNat 64 (536 - offset) := by
    rw [show stackPtr s = stackPtr entry - 536 from state.sp]
    apply BitVec.eq_sub_iff_add_eq.mpr
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show offset + (536 - offset) = 536 by omega]
    exact BitVec.sub_add_cancel _ _
  have avoidsStack : (Stack.region entry 2264).Avoids InProgram :=
    fun a ha h ↦ pre.call.stackAvoid a ha (.inl h)
  have code : CodeIn (codeRange 0x10f2b1 setupBytes) s :=
    programText_slice (programLoaded_codeIn state.loaded) 0xf2b1 setupBytes
      (by decide +kernel) (by decide +kernel)
  have setupPre : SetupPre s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Nat.ne_of_gt pos, Nat.not_lt.mpr bound, or_self, ↓reduceIte] using state.pc
    · intro offset ho
      rw [address offset ho]
      exact CallFrame.stack_readable pre.call.stack state.allocated (by omega) (by omega)
    · intro offset ho ha
      rw [address offset ho]
      exact CallFrame.stack_writable8 pre.call.stack pre.call.stackAvoid state.allocated
        (by omega) (by omega)
    · intro offset ho delta len hh
      have hlen : setupBytes.length = 97 := by decide
      rw [hlen] at hh
      rw [address offset ho]
      change RangeApart _ 8 (Extracted.textAddress + BitVec.ofNat 64 0xf2b1 + BitVec.ofNat 64 delta) len
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact CallFrame.stack_codeApart pre.call.stack avoidsStack (by omega) (by omega) (by omega)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := setup_run boundary pre.call.outerBoundary s
    (supportedMachine_readyToStep state.machine) code setupPre
  have writes : WritesWithin (setupEffect s).components
      #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264] := by
    intro c member a covers
    obtain ⟨offset, written, covered⟩ := setup_store_covers member covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at written
    rw [address offset (by omega)] at covered
    exact ⟨Stack.region entry 2264, by simp, stackRegion_contains_sub pre.call.stack.2.2.1
      (by omega) (by omega) covered⟩
  have avoids : ∀ r ∈ #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264],
      r.Avoids InProgram := by
    simp only [writtenLength, bound, ↓reduceIte]
    intro r hr a ha h
    exact ((pre.separation pos bound).2 r hr).2 a ha (.inl h)
  have running := state.toSavedFrame.toRunning.of_agrees run ready effect.agrees writes avoids
    (by simp [setupEffect, Effect.components])
  have sp : t.regValue .rsp = s.regValue .rsp :=
    effect.agrees.read (r := 4) (n := 64) (by simp [setupEffect, Effect.components])
  have keep (offset : Nat) (apart : offset + 8 ≤ 256) :
      slot t (BitVec.ofNat 64 offset) = slot s (BitVec.ofNat 64 offset) := by
    unfold slot
    rw [sp]
    apply CallFrame.agrees_memLoad
    exact setup_agrees effect (by omega) (by
      intro other member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      exact .inl (by omega))
  have saved := state.toSavedFrame.of_agreement running sp
    (setup_agrees (start := 488) (size := 56) effect (by decide) (by decide))
    (keep 224 (by decide))
    (effect.agrees.mxcsr (by simp [setupEffect, Effect.components]))
    (effect.agrees.fcw (by simp [setupEffect, Effect.components]))
  obtain ⟨out, inner, _, table, outer, flag, memcpy, remaining, counter⟩ := effect.writes
  change (Operand.mem (s.regValue .rsp + 424) : Operand 64).read t = slot s 240 + 64 at inner
  change (Operand.mem (s.regValue .rsp + 416) : Operand 64).read t = slot s 240 + 104 at outer
  change (Operand.mem (s.regValue .rsp + 440) : Operand 64).read t =
    (slot s 248 <<< 4) + slot s 232 at table
  change t.regValue .rbp = slot s 224 at remaining
  have next : t.RIP = 0x10f586 := effect.rip
  have count : slot s 248 = 1 := state.count.trans pre.count
  refine ⟨t, {
    toSavedFrame := saved
    contextPtr := (keep 240 (by decide)).trans state.contextPtr
    descriptors := (keep 232 (by decide)).trans state.descriptors
    count := (keep 248 (by decide)).trans count
    innerPtr := ?_
    outerPtr := ?_
    tableEnd := ?_
    memcpy := memcpy
    pc := ?_
    outputPtr := ?_
    remaining := ?_
    counter := ?_
    flag := ?_
    previous := ?_
    output := ?_ }⟩
  · unfold slot
    rw [sp, inner, state.contextPtr]
  · unfold slot
    rw [sp, outer, state.contextPtr]
  · unfold slot
    rw [sp, table, count, state.descriptors]
    exact BitVec.add_comm _ _
  · simpa only [Nat.mul_zero, pos, ↓reduceIte] using next
  · simp only [Nat.mul_zero, Nat.zero_min, BitVec.add_zero]
    exact out.trans state.outputPtr
  · simpa only [Nat.mul_zero, Nat.sub_zero, state.size] using remaining
  · unfold slot
    rw [sp]
    exact counter
  · change (t.regValue .rax).setWidth 8 = 0
    rw [show t.regValue .rax = 0 from flag]
    rfl
  · rw [blocks_zero]
    exact ⟨rfl, fun i ↦ Fin.elim0 i⟩
  · simp only [blocks_zero, Nat.mul_zero, Nat.zero_min]
    have emptySize : (ByteArray.empty.extract 0 length).size = 0 := by
      rw [ByteArray.size_extract, show ByteArray.empty.size = 0 by rfl, Nat.min_zero]
    exact ⟨emptySize, fun i ↦ False.elim (by have := i.isLt; omega)⟩

end Hkdf.Proofs.NewExpand.Expand
