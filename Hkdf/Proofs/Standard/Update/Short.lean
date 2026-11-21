import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Standard.Update
import Hkdf.Proofs.Standard.Update.State
import Hkdf.Proofs.Standard.Finalize.Prepare
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Wrapper.Absorb.Memory
import Hkdf.Proofs.Common.Instructions.AddByte.Effect
import Hkdf.Proofs.Common.Instructions.ByteStore.Legacy
import Hkdf.Proofs.Wrapper.Absorb.ByteAdd
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update.Short

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

private def setupBytes : List UInt8 :=
  [0x4a,0x8d,0x3c,0x3c,0x48,0x83,0xc7,0x78,0x4c,0x89,0xee,0x48,0x89,0xda]

private def setupEffect (s : RamState) : Effect :=
  { rip := 0x10162e
    writes := [⟨(.reg 7 : Operand 64), rspOf s + s.regValue .r15 + 120⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .rbx⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s + s.regValue .r15) 120).2) }

private theorem setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x101620)
      (codeRange 0x101620 setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x101620 0x4a (by simp [RexWPrefix]) 7
    (.sib 4 (some 15) 0 .none) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1624 (by decide))
  advance_then (add_r64_imm8_effect_step 0x101624 0x48 0xc7 120 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101620 setupBytes 4 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1628 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101628 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101620 setupBytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x162b (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10162b 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101620 setupBytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x162e (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [setupEffect, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [setupEffect, BitVec.add_zero, BitVec.shiftLeft_zero]
    exact ⟨rfl, rfl, rfl⟩
  · intro j; cases j <;> x86_norm [setupEffect, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals rfl
  · x86_norm [setupEffect, BitVec.add_zero, BitVec.shiftLeft_zero]

private def copyLayout (position count : Nat) (bound : position + count ≤ 64) :
    Hkdf.Proofs.Common.CallFrame.StackCallLayout 1792 0 count 0 :=
  ⟨528, 400, 400 - position, by decide, by decide, by decide, by omega,
    by decide, by omega, .inl (by omega)⟩

private theorem destination_address {initial : RamState} {position : Nat} (bound : position ≤ 400) :
    hmacBase initial + BitVec.ofNat 64 position =
      stackPtr initial - BitVec.ofNat 64 (400 - position) := by
  change stackPtr initial - 520 + 120 + BitVec.ofNat 64 position = _
  have sub : (400 : BitVec 64) - BitVec.ofNat 64 position =
      BitVec.ofNat 64 (400 - position) :=
    BitVec.ofNat_sub_ofNat_of_le 400 position (by omega) (by omega)
  rw [← sub]
  bv_omega


inductive CopySite where
  | short
  | fill
  | tail

def CopySite.offset : CopySite → Nat
  | .short => 0x162e
  | .fill => 0x168c
  | .tail => 0x1703

def CopySite.pc (site : CopySite) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 site.offset

theorem copy [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) (state : Preserved initial s)
    (site : CopySite) (i : Fin inputs.size) {sourceOffset position count : Nat}
    (sourceBound : sourceOffset + count ≤ inputs[i].bytes.size)
    (destinationBound : position + count ≤ 64)
    (rip : s.RIP = site.pc)
    (destination : s.regValue .rdi = hmacBase initial + BitVec.ofNat 64 position)
    (source : s.regValue .rsi = inputs[i].address + BitVec.ofNat 64 sourceOffset)
    (length : s.regValue .rdx = BitVec.ofNat 64 count)
    (copyRegister : s.regValue .r12 = 0x10dd60) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Preserved initial t ∧ t.RIP = (site.pc + (3 : BitVec 64)) ∧ Hkdf.Proofs.Program.PreservesABI s t ∧
      MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 (400 - position)).toNat, count⟩ : MemoryRegion),
        (⟨(stackPtr initial - 528).toNat, 8⟩ : MemoryRegion)] ∧
      (⟨(hmacBase initial + BitVec.ofNat 64 position).toNat, count⟩ : MemoryRegion).HasBytes
        t.external (inputs[i].bytes.extract sourceOffset (sourceOffset + count)) := by
  have bounds := Standard.stack_bounds ctx
  have avoid : (Stack.region initial hkdfSha256Extract.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (ctx.call.stackSeparation.2 (Stack.region initial hkdfSha256Extract.minStackBytes) (by simp)).2
  have outside := (returnBoundary_valid ctx).2.2
  have destination' := destination.trans (destination_address (by omega))
  have pushed : pushAddr s = stackPtr initial - 528 := by
    rw [pushAddr, show stackPtr s = frameBase initial from state.rsp, frameBase, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [pushed]
    exact CallFrame.stack_writable8 ctx.call.stack avoid state.allocated (by decide) (by decide)
  have apart : RangeApart (pushAddr s) 8 site.pc 3 := by
    rw [pushed]
    exact Standard.stack_codeApart ctx (offset := 528) (len := 8)
      (codeOffset := site.offset) (codeLen := 3) (by decide) (by decide)
      (by cases site <;> decide)
  have callStep := call_r64_rex_effect_step site.pc 0x41 0xd4
    (by simp [RexPrefix]) rfl rfl
  change StepEffect (CallPre site.pc 3 (fun s ↦ s.regValue .r12))
    (codeRange site.pc [0x41,0xff,0xd4])
    (callEffect (fun s ↦ s.regValue .r12) ((site.pc + (3 : BitVec 64)))) at callStep
  obtain ⟨c, callRun, readyC, call⟩ := callStep.advances
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.machine)
    (programText_slice (programLoaded_codeIn state.loaded) site.offset _
      (by cases site <;> decide) (by cases site <;> decide +kernel))
    ⟨⟨rip, writable, apart⟩, by change (s.regValue .r12).toNat < 2^32; rw [copyRegister]; decide⟩
    (by change s.regValue .r12 ≠ (returnBoundary initial).rip
        rw [copyRegister]; exact boundary_ne_program outside (inProgram_of_textOffset 0xdd60 (by decide)))
  have runningC := state.toRunning.of_agrees callRun readyC call.agrees
    (Standard.Finalize.call_stack_writes state.rsp ctx.call.stack)
    (by intro r hr b hb hp
        have eq : r = Stack.region initial hkdfSha256Extract.minStackBytes := by
          simpa only [Vector.mem_singleton] using hr
        subst r; exact avoid b hb (.inl hp))
    (by simp [callEffect, pushEffect_components])
  have rspC : stackPtr c = stackPtr initial - 528 := call.writes.1.trans pushed
  have returnC : returnBoundary c = ⟨(site.pc + (3 : BitVec 64)), frameBase initial⟩ := by
    have h := call_boundary call
    simpa only [show stackPtr s = frameBase initial from state.rsp] using h
  have destC : c.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (400 - position) :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans destination'
  have sourceC : c.regValue .rsi = inputs[i].address + BitVec.ofNat 64 sourceOffset :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans source
  have countC : c.regValue .rdx = BitVec.ofNat 64 count :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans length
  have slice := extract_input_slice ctx.call runningC.frame i (offset := sourceOffset) (count := count) sourceBound
  have regionC : registerRegion c .rsi count =
      (⟨(inputs[i].address + BitVec.ofNat 64 sourceOffset).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, sourceC]
  have allocated : (registerRegion c .rsi count).Allocated c.external := by
    rw [regionC]
    exact Hkdf.Proofs.Common.Machine.allocated_of_hasBytes slice.1.2
  have pre : CalleePre c (returnBoundary initial) 0x10dd60 count count 0 :=
    callee_pre_of_stack_output ctx.environment.stringStride ctx.call.stack avoid outside
      runningC.machine runningC.directionFlag runningC.loaded runningC.allocated
      (copyLayout position count destinationBound)
      (call.rip.trans copyRegister) rspC destC
      (by rw [returnC]
          change InProgram (Extracted.textAddress + BitVec.ofNat 64 site.offset + BitVec.ofNat 64 3)
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact inProgram_of_textOffset (site.offset + 3) (by cases site <;> decide))
      (regionC ▸ slice.1.1) allocated (regionC ▸ slice.2)
  have countBound := extract_input_bound ctx.call i
  obtain ⟨t, result, copied, _⟩ := Common.Memory.memcpy_correct pre countC (by omega)
  have complete := call_result pre call result state.directionFlag
  have fullFrame : MemoryWriteFrame s t #v[registerRegion c .rdi count, Stack.region c 0] := complete.1
  have observed (offset len : Nat) (low : offset ≤ 520) (high : len ≤ offset + 8)
      (apart : offset + count ≤ 400 - position ∨ 400 - position + len ≤ offset) :
      (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Agrees s t := by
    apply frame_agrees_of_disjoint fullFrame
    · rw [Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (by change offset ≤ 1792; omega)]
      omega
    · exact stack_layout_disjoint ctx.call.stack (copyLayout position count destinationBound)
        rspC destC apart (by change offset + 8 ≤ 528; omega)
  have saved := observed 48 56 (by decide) (by decide) (.inl (by omega))
  have persistent : ∀ offset ∈ ([8,96,104,112] : List Nat),
      (Component.mem (frameBase initial + BitVec.ofNat 64 offset) 8).Agrees s t := by
    intro offset member
    have bound : 8 ≤ offset ∧ offset ≤ 112 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have addr : frameBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
      have h := stack_address state.rsp (offset := offset) (by omega)
      simpa only [show rspOf s = frameBase initial from state.rsp] using h
    rw [addr]
    exact observed (520-offset) 8 (by omega) (by omega) (.inr (by omega))
  have runningT := runningC.of_callee result (by
    intro region member b hb
    exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
      stack_layout_within ctx.call.stack (copyLayout position count destinationBound) rspC destC
        region member b hb⟩)
  have rspT : t.regValue .rsp = frameBase initial := by
    exact result.rsp.trans (congrArg ReturnBoundary.rsp returnC)
  have preserved := state.of_observations runningT saved persistent rspT
  have outputRegion : registerRegion c .rdi count =
      (⟨(stackPtr initial - BitVec.ofNat 64 (400-position)).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, destC]
  have stackRegion : Stack.region c 0 =
      (⟨(stackPtr initial - 528).toNat, 8⟩ : MemoryRegion) := by
    simp only [Stack.region, Nat.sub_zero, Nat.add_sub_cancel_left]
    change (⟨(stackPtr c).toNat, 8⟩ : MemoryRegion) = _
    rw [rspC]
  obtain ⟨copyFuel, copyRun⟩ := result.execution
  refine ⟨1 + copyFuel, t, callRun.trans copyRun,
    Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep result.machine, preserved,
    by simpa only [returnC] using result.rip, complete.2,
    by simpa only [outputRegion, stackRegion] using fullFrame, ?_⟩
  refine ⟨by simp only [MemoryRegion.HasLength, ByteArray.size_extract]; omega, ?_⟩
  intro j
  have hj : j.val < count := by have h := j.isLt; simp only [ByteArray.size_extract] at h; omega
  have h := copied j.val hj
  rw [destC, sourceC] at h
  have addr := destination_address (initial := initial) (position := position) (by omega)
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [addr, h]
  have inputByte := extract_input_byte_unchanged ctx.call runningC.frame i
    ⟨sourceOffset+j.val, by omega⟩
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, ByteArray.getElem_extract] using inputByte

theorem copy_observation [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {position count offset len : Nat} (ctx : Context initial salt inputs)
    (frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 (400-position)).toNat, count⟩ : MemoryRegion),
      (⟨(stackPtr initial - 528).toNat, 8⟩ : MemoryRegion)])
    (bound : position + count ≤ 64) (low : offset ≤ 520) (high : len ≤ offset + 8)
    (apart : offset + count ≤ 400-position ∨ 400-position + len ≤ offset) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Agrees s t := by
  have bounds := Standard.stack_bounds ctx
  have query := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := offset) (by change offset ≤ 1792; omega)
  have dest := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 400-position) (by change 400-position ≤ 1792; omega)
  have slot := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 528) (by decide)
  apply frame_agrees_of_disjoint frame
  · rw [query]
    omega
  · intro r hr a ha hb
    change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + len at ha
    rw [query] at ha
    have cases : r = (⟨(stackPtr initial - BitVec.ofNat 64 (400-position)).toNat, count⟩ : MemoryRegion) ∨
        r = (⟨(stackPtr initial - 528).toNat, 8⟩ : MemoryRegion) := by simpa using hr
    rcases cases with rfl | rfl
    · change (stackPtr initial - BitVec.ofNat 64 (400-position)).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 (400-position)).toNat + count at hb
      rw [dest] at hb
      rcases apart with before | after <;> omega
    · change (stackPtr initial - 528).toNat ≤ a ∧ a < (stackPtr initial - 528).toNat + 8 at hb
      change (stackPtr initial - BitVec.ofNat 64 528).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 528).toNat + 8 at hb
      rw [slot] at hb
      omega

private theorem finish_observation {initial s t : RamState} {offset len : Nat}
    (frame : AgreesExcept [.reg 3, .flags, .mem (hmacBase initial + 63) 1, .rip] s t)
    (within : offset + len ≤ 144) (apart : offset + len ≤ 63 ∨ 64 ≤ offset) :
    ∀ i < len, t.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  by_cases zero : len = 0
  · subst len
    intro i hi
    omega
  have positive : 0 < len := by omega
  have sep : OffsetsApart (BitVec.ofNat 64 offset) len 63 1 := by
    unfold OffsetsApart
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64), BitVec.reduceToNat]
    rcases apart with h | h <;> omega
  intro i hi
  apply frame.memory
  intro c hc cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  obtain ⟨j, hj, he⟩ := cover
  exact OffsetsApart.ne sep (hmacBase initial) hi hj (by omega) he

private theorem finish [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) (state : Preserved initial s)
    (rip : s.RIP = 0x101631) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ ReadyToStep t ∧
      Preserved initial t ∧ t.RIP = 0x10163b ∧
      t.external[hmacBase initial + 63]? = some (UInt8.ofNat
        (((Operand.reg 3 : Operand 8).read s + (Operand.reg 15 : Operand 8).read s).toNat)) ∧
      AgreesExcept [.reg 3, .flags, .mem (hmacBase initial + 63) 1, .rip] s t := by
  have outside := (returnBoundary_valid ctx).2.2
  obtain ⟨a, runA, readyA, added⟩ :=
    (Hkdf.Proofs.Common.Instructions.AddByte.add_r8_r8_effect_step 0x101631 0x44 0xfb
      (by simp [RexPrefix]) rfl).advances
      (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) 0x1631 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1634 (by decide)))
  have frameA : AgreesExcept [.reg 3, .flags, .rip] s a := added.agrees
  have stateA := Preserved.of_noMem ctx state runA readyA frameA
    (by simp [Component.Covers]) (by simp) (by simp)
  have low : (Operand.reg 3 : Operand 8).read a =
      (Operand.reg 3 : Operand 8).read s + (Operand.reg 15 : Operand 8).read s := by
    have h := added.writes
    change a.regValue .rbx = mergeGPR 8
      ((Operand.reg 3 : Operand 8).read s + (Operand.reg 15 : Operand 8).read s)
      (s.regValue .rbx) at h
    change (a.regValue .rbx).setWidth 8 = _
    rw [h, Hkdf.Proofs.Wrapper.Absorb.mergeGPR8_low]
  have address : rspOf a + 183 = hmacBase initial + 63 := by
    change a.regValue .rsp + 183 = _
    rw [stateA.rsp, hmacBase, BitVec.add_assoc]
    rfl
  have stackAddress : hmacBase initial + 63 = stackPtr initial - 337 := by
    change stackPtr initial - 520 + 120 + 63 = _
    bv_omega
  have avoid : (Stack.region initial hkdfSha256Extract.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) := (ctx.call.stackSeparation.2 _ (by simp)).2
  have writable : MemWritable a (rspOf a + 183) 1 := by
    rw [address, stackAddress]
    exact CallFrame.stack_writable1 ctx.call.stack avoid stateA.allocated (by decide)
  have apart : RangeApart (rspOf a + 183) 1 0x101634 7 := by
    rw [address, stackAddress]
    exact Standard.stack_codeApart ctx (offset := 337) (len := 1)
      (codeOffset := 0x1634) (codeLen := 7) (by decide) (by decide) (by decide)
  obtain ⟨t, runT, readyT, stored⟩ :=
    (Hkdf.Proofs.Common.Instructions.mov_m8_r8_legacy_effect_step 0x101634 3 (by decide)
      (.sib 4 none 0 (.d32 183)) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0x1634 _
        (by decide) (by decide +kernel)) ⟨added.rip, writable, apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x163b (by decide)))
  have frameT : AgreesExcept [.mem (hmacBase initial + 63) 1, .rip] a t := by
    have h := stored.agrees
    simp only [storeEffect_components] at h
    change AgreesExcept [.mem (rspOf a + 183) 1, .rip] a t at h
    rwa [address] at h
  have combined : AgreesExcept [.reg 3, .flags, .mem (hmacBase initial + 63) 1, .rip] s t :=
    (frameA.trans frameT).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) | (rfl | rfl) <;> simp)
  have observed (offset len : Nat)
      (sep : OffsetsApart (-BitVec.ofNat 64 offset) len (-337) 1)
      (small : len + 1 < 2^64) :
      (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Agrees s t := by
    intro i hi
    apply combined.memory
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨j, hj, eq⟩ := cover
    apply OffsetsApart.ne sep (stackPtr initial) hi hj small
    simpa only [stackAddress, BitVec.sub_eq_add_neg] using eq
  have writes : WritesWithin [.reg 3, .flags, .mem (hmacBase initial + 63) 1, .rip]
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] := by
    intro c hc b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hb.elim
    rw [stackAddress] at hb
    exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
      Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.call.stack.2.2.1
        (by decide) (by decide) hb⟩
  have running := state.toRunning.of_agrees (runA.trans runT) readyT combined writes
    (by intro r hr b hb hp; have eq : r = Stack.region initial hkdfSha256Extract.minStackBytes := by simpa only [Vector.mem_singleton] using hr
        subst r; exact avoid b hb (.inl hp)) (by simp)
  have saved := observed 48 56 (by unfold OffsetsApart; decide +kernel) (by decide)
  have persistent : ∀ offset ∈ ([8,96,104,112] : List Nat),
      (Component.mem (frameBase initial + BitVec.ofNat 64 offset) 8).Agrees s t := by
    intro offset member
    have limits : 8 ≤ offset ∧ offset ≤ 112 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have addr := Standard.stack_address state.rsp (offset := offset) (by omega)
    rw [show rspOf s = frameBase initial from state.rsp] at addr
    rw [addr]
    have cases : offset = 8 ∨ offset = 96 ∨ offset = 104 ∨ offset = 112 := by simpa using member
    rcases cases with rfl | rfl | rfl | rfl
    all_goals exact observed _ _ (by unfold OffsetsApart; decide +kernel) (by decide)
  have preserved := state.of_observations running saved persistent
    ((combined.read (n := 64) (r := 4) (by simp)).trans state.rsp)
  have value : memLoad t.external (rspOf a + 183) 8 = (Operand.reg 3 : Operand 8).read a :=
    stored.writes
  have bytes := Bytes.of_memLoad (n := 8)
    (fun i hi ↦ stored.agrees.grow _ (writable.mem i hi)) 0 (by decide)
  rw [value, BitVec.add_zero, address] at bytes
  have tail : t.external[hmacBase initial + 63]? =
      some (UInt8.ofNat ((Operand.reg 3 : Operand 8).read a).toNat) := by
    simpa only [storedByte, Nat.mul_zero, Nat.shiftRight_zero] using bytes
  rw [low] at tail
  exact ⟨t, runA.trans runT, readyT, preserved, stored.rip, tail, combined⟩

theorem short_input [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat} (ctx : Context initial salt inputs)
    (ready : ReadyToStep s) (state : PreparedInput initial s salt inputs index true) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      InputDone initial t salt inputs index true := by
  let i : Fin inputs.size := ⟨index, state.remaining⟩
  let position := (prefixConcatenation inputs index).size % 64
  let bytes := inputs[i].bytes
  let prior := HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++ prefixConcatenation inputs index
  have small : position + bytes.size < 64 := by
    have h := state.branch
    change bytes.size < 64 - position at h
    omega
  have priorPosition : prior.size % 64 = position := by
    dsimp only [prior]
    rw [ByteArray.size_append, HMAC.xorPad_keyBlock_size]
    omega
  have short : bytes.size < 64 - prior.size % 64 := by rw [priorPosition]; omega
  have counts := Hkdf.Proofs.Wrapper.Absorb.append_short_counts prior bytes short
  obtain ⟨setupFuel, a, setupRun, readyA, _, setupPost⟩ := setup (returnBoundary initial)
    (returnBoundary_valid ctx).2.2 s ready
    (programText_slice (programLoaded_codeIn state.loaded) 0x1620 setupBytes
      (by decide +kernel) (by decide +kernel)) state.rip
  have frameA : AgreesExcept [.reg 7, .reg 6, .reg 2, .flags, .rip] s a := setupPost.agrees
  have bufferedA := buffered_of_noMem ctx state.toBuffered setupRun readyA frameA
    (by simp [Component.Covers]) (by simp) (by simp)
  have destination : a.regValue .rdi = hmacBase initial + BitVec.ofNat 64 position := by
    have h : a.regValue .rdi = rspOf s + s.regValue .r15 + 120 := setupPost.writes.1
    rw [h, state.tail]
    change s.regValue .rsp + BitVec.ofNat 64 position + 120 = _
    rw [state.rsp, hmacBase]
    bv_omega
  have source : a.regValue .rsi = inputs[i].address + BitVec.ofNat 64 0 := by
    exact (setupPost.writes.2.1.trans state.pointer).trans
      (BitVec.add_zero inputs[i].address).symm
  have length : a.regValue .rdx = BitVec.ofNat 64 bytes.size := setupPost.writes.2.2.trans state.length
  have copyRegister : a.regValue .r12 = 0x10dd60 :=
    (frameA.read (n := 64) (r := 12) (by simp)).trans state.copyRegister
  obtain ⟨copyFuel, c, copyRun, readyC, preservedC, ripC, abi, frameC, copied⟩ :=
    copy ctx bufferedA.toPreserved .short i (sourceOffset := 0) (position := position)
      (count := bytes.size) (by change 0 + bytes.size ≤ bytes.size; omega) (Nat.le_of_lt small)
      setupPost.rip destination source length copyRegister
  have copied' : (⟨(hmacBase initial + BitVec.ofNat 64 position).toNat, bytes.size⟩ : MemoryRegion).HasBytes
      c.external bytes := by
    change (⟨(hmacBase initial + BitVec.ofNat 64 position).toNat, bytes.size⟩ : MemoryRegion).HasBytes
      c.external (bytes.extract 0 (0 + bytes.size)) at copied
    simpa only [Nat.zero_add, ByteArray.extract_zero_size] using copied
  have copiedSame (offset len : Nat) (bound : offset + len ≤ 144)
      (apart : offset + len ≤ position ∨ position + bytes.size ≤ offset) :
      ∀ j < len, c.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? =
        a.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? := by
    have query := copy_observation ctx frameC (offset := 400-offset) (len := len)
      (by omega) (by omega) (by omega) (by rcases apart with h | h <;> omega)
    have address := destination_address (initial := initial) (position := offset) (by omega)
    rw [address]
    exact query
  have rbxC : c.regValue .rbx = BitVec.ofNat 64 bytes.size :=
    (abi.1 .rbx (by simp)).trans ((frameA.read (n := 64) (r := 3) (by simp)).trans state.length)
  have r15C : c.regValue .r15 = BitVec.ofNat 64 position :=
    (abi.1 .r15 (by simp)).trans ((frameA.read (n := 64) (r := 15) (by simp)).trans state.tail)
  obtain ⟨t, finishRun, readyT, preservedT, ripT, stored, frameT⟩ :=
    finish ctx preservedC (ripC.trans (by decide +kernel))
  have sum : (Operand.reg 3 : Operand 8).read c + (Operand.reg 15 : Operand 8).read c =
      BitVec.ofNat 8 (position + bytes.size) := by
    change (c.regValue .rbx).setWidth 8 + (c.regValue .r15).setWidth 8 = _
    rw [rbxC, r15C, BitVec.setWidth_ofNat_of_le (by decide),
      BitVec.setWidth_ofNat_of_le (by decide), ← BitVec.ofNat_add, Nat.add_comm]
  rw [sum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : position + bytes.size < 256)] at stored
  have unchanged (offset len : Nat) (bound : offset + len ≤ 144) (above : 64 ≤ offset) :
      ∀ j < len, t.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? =
        a.external[hmacBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? := by
    intro j hj
    exact (finish_observation frameT bound (.inr above) j hj).trans
      (copiedSame offset len bound (.inr (by omega)) j hj)
  have tailSize : (Hkdf.Proofs.Common.SHA256.remainderBytes prior ++ bytes).size =
      position + bytes.size := by
    rw [ByteArray.size_append, Hkdf.Proofs.Common.SHA256.remainderBytes_size, priorPosition]
  have front : (⟨(hmacBase initial).toNat,
      (Hkdf.Proofs.Common.SHA256.remainderBytes prior).size⟩ : MemoryRegion).HasBytes
        c.external (Hkdf.Proofs.Common.SHA256.remainderBytes prior) := by
    refine ⟨rfl, ?_⟩
    intro j
    have hj : j.val < position := by
      simpa only [Hkdf.Proofs.Common.SHA256.remainderBytes_size, priorPosition] using j.isLt
    have old := bufferedA.hmac.inner.tail.2 j
    have same := copiedSame 0 position (by omega) (.inl (by omega)) j.val hj
    simp only [BitVec.add_zero] at same
    change c.external[BitVec.ofNat 64 ((hmacBase initial).toNat + j.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [same]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, prior,
      Hkdf.Proofs.Common.SHA256.remainderBytes] using old
  have tailC := Hkdf.Proofs.Wrapper.Absorb.hasBytes_append front
    (by simpa only [Hkdf.Proofs.Common.SHA256.remainderBytes_size, priorPosition] using copied')
  have tailT : (⟨(hmacBase initial).toNat,
      (Hkdf.Proofs.Common.SHA256.remainderBytes prior ++ bytes).size⟩ : MemoryRegion).HasBytes
      t.external (Hkdf.Proofs.Common.SHA256.remainderBytes prior ++ bytes) := by
    refine ⟨rfl, ?_⟩
    intro j
    have hj : j.val < position + bytes.size := by simpa only [tailSize] using j.isLt
    have same := finish_observation frameT (offset := 0) (len := position + bytes.size)
      (by omega) (.inl (by omega)) j.val hj
    simp only [BitVec.add_zero] at same
    change t.external[BitVec.ofNat 64 ((hmacBase initial).toNat + j.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [same]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using tailC.2 j
  have inner : StreamAt t (hmacBase initial) (prior ++ bytes) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Hkdf.Proofs.Wrapper.Absorb.compressBlocks_append_short _ _ _ short]
      apply Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedA.hmac.inner.hashWords
      intro j hj
      simpa only [BitVec.ofNat_eq_ofNat] using unchanged 64 32 (by decide) (by decide) j hj
    · change (⟨(hmacBase initial).toNat, (prior ++ bytes).size % 64⟩ : MemoryRegion).HasBytes
        t.external (Hkdf.Proofs.Common.SHA256.remainderBytes (prior ++ bytes))
      rw [Hkdf.Proofs.Wrapper.Absorb.remainderBytes_append_short _ _ short, counts.2, priorPosition]
      simpa only [tailSize] using tailT
    · rw [counts.2, priorPosition]
      exact stored
    · rw [counts.1]
      change Machine.loadBytes t.external (hmacBase initial + BitVec.ofNat 64 96) 8 = _
      rw [Hkdf.Proofs.Common.Memory.loadBytes_congr
        (fun j hj ↦ unchanged 96 8 (by decide) (by decide) j hj)]
      exact bufferedA.hmac.inner.blocks
  have hmac : HmacAt t (hmacBase initial) (saltKey salt)
      (prefixConcatenation inputs index ++ bytes) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [prior, ByteArray.append_assoc] using inner
    · apply Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedA.hmac.outerHash
      intro j hj
      simpa only [BitVec.ofNat_eq_ofNat] using unchanged 104 32 (by decide) (by decide) j hj
    · change Machine.loadBytes t.external (hmacBase initial + BitVec.ofNat 64 136) 8 = _
      rw [Hkdf.Proofs.Common.Memory.loadBytes_congr
        (fun j hj ↦ unchanged 136 8 (by decide) (by decide) j hj)]
      exact bufferedA.hmac.outerBlocks
  refine ⟨setupFuel + copyFuel + 2, t, (setupRun.trans copyRun).trans finishRun, readyT, {
    toBuffered := ⟨preservedT, ?_⟩
    remaining := state.remaining
    rip := ripT
    indexRegister := (frameT.read (n := 64) (r := 14) (by simp)).trans
      ((abi.1 .r14 (by simp)).trans ((frameA.read (n := 64) (r := 14) (by simp)).trans state.indexRegister))
    copyRegister := (frameT.read (n := 64) (r := 12) (by simp)).trans
      ((abi.1 .r12 (by simp)).trans ((frameA.read (n := 64) (r := 12) (by simp)).trans state.copyRegister))
  }⟩
  rw [prefixConcatenation_succ inputs index state.remaining]
  exact hmac

end Hkdf.Proofs.Standard.Update.Short
