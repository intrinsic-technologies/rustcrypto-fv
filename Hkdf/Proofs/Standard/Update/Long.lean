import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Standard.Initialization.Inner
import Hkdf.Proofs.Standard.Update.Bulk
import Hkdf.Proofs.Standard.Update.Short
import Hkdf.Proofs.Standard.Update.Blocks
import Hkdf.Proofs.Standard.Update.State
import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.Streaming
import Hkdf.Proofs.Wrapper.Absorb.Mathematics
import Hkdf.Proofs.Wrapper.Absorb.Arithmetic
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import Hkdf.Proofs.Common.Instructions.MemoryAlu.Inc
import Hkdf.Proofs.Common.Instructions.ByteStore
import Hkdf.Proofs.Standard.Update
import Hkdf.Proofs.Common.Instructions.MemoryAlu.Add

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions.MemoryAlu
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Standard.Initialization
open Hkdf.Proofs.Common.SHA256

theorem tail_dispatch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x101674) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .r15 = 0 then 0x101716 else 0x10167d) ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, first, readyU, tested⟩ :=
    (test_r64_r64_effect_step 0x101674 0x4d 0xff (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice code 0x1674 _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1677 (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := tested.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) code
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .r15 == 0) := by
    have h := tested.flag .ZF
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((s.regValue .r15 &&& s.regValue .r15) == 0) at h
    simpa only [BitVec.and_self] using h
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step 0x101677 4 0x99 u readyU
    (programText_slice codeU 0x1677 _ (by decide) (by decide +kernel))
    ⟨tested.rip, fun _ ↦ by decide⟩
  have target : t.RIP =
      (if s.regValue .r15 = 0 then 0x101716 else 0x10167d) := by
    rw [jumped.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x101716 else 0x10167d) = _
    rw [zf]
    simp only [beq_iff_eq]
  have second : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1716 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x167d (by decide))
  refine ⟨t, first.trans second, readyT, target, ?_⟩
  exact (frame.trans jumped.agrees).mono (by simp [jccEffect, branchEffect_components])

def fillBytes : List UInt8 :=
  [0x4a,0x8d,0x1c,0x2a,0x4a,0x8d,0x3c,0x3c,0x48,0x83,0xc7,0x78,0x4c,0x89,0xee]

def fillEffect (s : RamState) : Effect :=
  { rip := 0x10168c
    writes := [⟨(.reg 3 : Operand 64),
        (Operand.reg 2 : Operand 64).read s + (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + ((Operand.reg 15 : Operand 64).read s) + 120⟩,
      ⟨(.reg 6 : Operand 64), ((Operand.reg 13 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags
      (addSpec (rspOf s + (Operand.reg 15 : Operand 64).read s) 120).2) }

theorem fill_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10167d fillBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x167d fillBytes
    (by decide +kernel) (by decide +kernel)

theorem fill_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10167d)
      (codeRange 0x10167d fillBytes) (Effect.post fillEffect) := by
  advance_begin (lea_r64_effect_step 0x10167d 0x4a (by simp [RexWPrefix]) 3
    (.sib 2 (some 13) 0 .none) (by decide +kernel) rfl rfl)
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1681 (by decide))
  advance_then (lea_r64_effect_step 0x101681 0x4a (by simp [RexWPrefix]) 7
    (.sib 4 (some 15) 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10167d fillBytes 4 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1685 (by decide))⟩
  advance_then (add_r64_imm8_effect_step 0x101685 0x48 0xc7 120 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10167d fillBytes 8 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1689 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101689 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10167d fillBytes 12 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x168c (by decide))⟩
  advance_finish [fillEffect, BitVec.add_zero, BitVec.shiftLeft_zero]

def fillCountBytes : List UInt8 :=
  [0x48,0xff,0x84,0x24,0xd8,0,0,0,0xba,1,0,0,0,
    0x48,0x8d,0xbc,0x24,0xb8,0,0,0,0x48,0x8d,0x74,0x24,0x78]

def fillCountEffect (s : RamState) : Effect :=
  { rip := 0x1016a9
    writes := [⟨(.mem (rspOf s + 216) : Operand 64), memLoad s.external (rspOf s+216) 64+1⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 184⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 120⟩]
    flags := some (.ofStatusFlags
      (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) (memLoad s.external (rspOf s+216) 64)).2) }

theorem fill_count_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10168f ∧
      MemWritable s (rspOf s + 216) 8 ∧ RangeApart (rspOf s + 216) 8 0x10168f 26)
      (codeRange 0x10168f fillCountBytes) (Effect.post fillCountEffect) := by
  advance_begin (inc_m64_effect_step 0x10168f 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i hi j hj
    exact h.2.2 i hi j (by simp [AddrMode.tail, Disp.bytes] at hj; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [incM64Effect]
    exact h.2.2
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1697 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x101697 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10168f fillCountBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x169c (by decide))⟩
  advance_then (lea_r64_effect_step 0x10169c 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10168f fillCountBytes 13 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16a4 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1016a4 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10168f fillCountBytes 21 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16a9 (by decide))⟩
  advance_finish [fillCountEffect, incM64Effect, incSpec]

def filledBytes : List UInt8 := [0xc6,0x84,0x24,0xb7,0,0,0,0,0x49,0x89,0xdd]

def filledEffect (s : RamState) : Effect :=
  { rip := 0x1016b9
    writes := [⟨(.mem (rspOf s + 183) : Operand 8), 0⟩,
      ⟨(.reg 13 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

theorem filled_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x1016ae ∧
      MemWritable s (rspOf s + 183) 1 ∧ RangeApart (rspOf s + 183) 1 0x1016ae 11)
      (codeRange 0x1016ae filledBytes) (Effect.post filledEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x1016ae (.sib 4 none 0 (.d32 183))
    (by decide) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i hi j hj
    exact h.2.2 i hi j (by simp [AddrMode.tail, Disp.bytes] at hj; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.2.2
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x16b6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1016b6 0x49 0xdd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1016ae filledBytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16b9 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [filledEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [filledEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [filledEffect]
  · x86_norm [filledEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

theorem compress_buffer [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {hash : Array UInt32} {block : ByteArray}
    (ctx : Context initial salt inputs) (state : Preserved initial s)
    (ready : ReadyToStep s) (rip : s.RIP = 0x1016a9)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 336)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400)
    (count : s.regValue .rdx = BitVec.ofNat 64 1)
    (words : HashStateAt s (stackPtr initial - BitVec.ofNat 64 336) hash)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 400).toNat, 64⟩ : MemoryRegion).HasBytes
      s.external block) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Preserved initial t ∧ t.RIP = 0x1016ae ∧
      HashStateAt t (stackPtr initial - BitVec.ofNat 64 336) (compressBlocks hash block) ∧
      Hkdf.Proofs.Program.PreservesABI s t ∧
      MemoryWriteFrame s t (innerWriteRegions initial 32 336) := by
  obtain ⟨u, callRun, readyU, runningU, callEffect, callFrame, rspU, retU⟩ :=
    hash_call ctx state ready rip (call_rel32_effect_step 0x1016a9 0x7f12 (by decide))
      (programText_slice (programLoaded_codeIn state.loaded) 0x16a9 _
        (by decide) (by decide +kernel))
      (stack_codeApart ctx (codeOffset := 0x16a9) (by decide) (by decide) (by decide))
  have outputU : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 336 :=
    (callEffect.agrees.read (n := 64) (r := 7)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans output
  have sourceU : u.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400 :=
    (callEffect.agrees.read (n := 64) (r := 6)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans source
  have countU : u.regValue .rdx = BitVec.ofNat 64 1 :=
    (callEffect.agrees.read (n := 64) (r := 2)
      (by simp [X86Proofs.callEffect, pushEffect_components])).trans count
  have wordsU := Hkdf.Proofs.Wrapper.hashState_of_bytes words
    (inner_frame_agrees ctx callFrame (offset := 336) (len := 32)
      (by decide) (by decide) (by decide) (by decide))
  have bytesU := inner_hasBytes_of_frame ctx callFrame (offset := 400) (len := 64)
    (by decide) (by decide) (by decide) (by decide) bytes
  have pre := hash_compression_pre ctx (by decide) (by decide) runningU callEffect.rip
    rspU outputU sourceU (by rw [retU]; exact inProgram_of_textOffset 0x16ae (by decide))
    countU bytesU wordsU
  obtain ⟨t, result⟩ := Common.SHA256.compression_correct pre
  have resultFrame := hash_compression_frame ctx (by decide) rspU outputU result.frame
  have frame := memoryWriteFrame_trans (hash_zero_frame callFrame) resultFrame
  have runningT := runningU.of_callee result.toCalleeResult
    (by intro region member a contains
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
          stack_layout_within ctx.call.stack (hashCallLayout 336 (by decide))
            rspU outputU region member a contains⟩)
  have rspT : t.regValue .rsp = frameBase initial := by rw [result.rsp, retU]
  have preserved := inner_preserved_of_frame ctx state runningT frame rspT
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨1+fuel, t, callRun.trans execution, supportedMachine_readyToStep result.machine,
    preserved, ?_, ?_, (CallFrame.call_result pre.toCalleePre callEffect
      result.toCalleeResult state.directionFlag).2, frame⟩
  · rw [result.rip, retU]
    rfl
  · simpa only [outputU] using result.hashWords

set_option maxHeartbeats 1200000 in
theorem long_to_bulk [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : PreparedInput initial s salt inputs index false) :
    ∃ fuel t consumed direct, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      BulkInput initial t salt inputs ⟨index, state.remaining⟩ consumed direct := by
  let i : Fin inputs.size := ⟨index, state.remaining⟩
  let previous := prefixConcatenation inputs index
  let bytes := inputs[i].bytes
  let prior := HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++ previous
  let position := previous.size % 64
  let capacity := 64-position
  have priorPosition : prior.size % 64 = position := by
    dsimp only [prior]
    rw [ByteArray.size_append, HMAC.xorPad_keyBlock_size]
    omega
  have positionBound : position < 64 := Nat.mod_lt _ (by decide)
  have enough : capacity ≤ bytes.size := state.branch
  have counts := Hkdf.Proofs.Wrapper.Absorb.filled_prefix_counts prior bytes
    (by simpa only [priorPosition] using enough)
  have extent : position+capacity ≤ 64 := by dsimp only [capacity]; omega
  have address (offset : Nat) (bound : offset ≤ 520) :
      frameBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520-offset) := by
    have addr := stack_address state.rsp (offset := offset) bound
    rw [show rspOf s = frameBase initial from state.rsp] at addr
    exact addr
  have hmacAddress : hmacBase initial = stackPtr initial - BitVec.ofNat 64 400 :=
    address 120 (by decide)
  obtain ⟨d, dispatchRun, readyD, target, dispatchFrame⟩ := tail_dispatch ready state.loaded
    (returnBoundary_valid ctx).2.2 state.rip
  have bufferedD := buffered_of_noMem ctx state.toBuffered dispatchRun readyD dispatchFrame
    (by simp [Component.Covers]) (by simp) (by simp)
  have sameD (r : BitVec 5) : (Operand.reg r : Operand 64).read d =
      (Operand.reg r : Operand 64).read s := dispatchFrame.read (by simp)
  by_cases zero : position = 0
  · have zeroRegister : s.regValue .r15 = 0 := by rw [state.tail]; exact congrArg _ zero
    have ripD : d.RIP = 0x101716 := by simpa only [zeroRegister, ↓reduceIte] using target
    obtain ⟨t, movedRun, readyT, moved⟩ :=
      (mov_r64_r64_effect_step 0x101716 0x48 0xdd (by simp [RexWPrefix]) rfl).advances readyD
        (programText_slice (programLoaded_codeIn bufferedD.loaded) 0x1716 _
          (by decide) (by decide +kernel)) ripD
        (boundary_ne_program (returnBoundary_valid ctx).2.2
          (inProgram_of_textOffset 0x1719 (by decide)))
    have movedFrame : AgreesExcept [.reg 5, .rip] d t := moved.agrees
    have bufferedT := buffered_of_noMem ctx bufferedD movedRun readyT movedFrame
      (by simp [Component.Covers]) (by simp) (by simp)
    refine ⟨3, t, 0, true, dispatchRun.trans movedRun, readyT, ?_⟩
    refine ⟨?_, Nat.zero_le _, ?_, moved.rip, ?_, ?_, ?_, ?_⟩
    · simpa only [ByteArray.extract_same, ByteArray.append_empty] using bufferedT
    · simpa only [ByteArray.extract_same, ByteArray.append_empty] using zero
    · exact ((movedFrame.read (n := 64) (r := 13) (by simp)).trans
        ((sameD 13).trans state.pointer)).trans (BitVec.add_zero inputs[i].address).symm
    · have word : t.regValue .rbp = d.regValue .rbx := moved.writes
      simpa only [Nat.sub_zero, i, Fin.getElem_fin] using word.trans ((sameD 3).trans state.length)
    · exact (movedFrame.read (n := 64) (r := 14) (by simp)).trans
        ((sameD 14).trans state.indexRegister)
    · exact (movedFrame.read (n := 64) (r := 12) (by simp)).trans
        ((sameD 12).trans state.copyRegister)
  · have nonzeroRegister : s.regValue .r15 ≠ 0 := by
      intro h
      have hn := congrArg BitVec.toNat (state.tail.symm.trans h)
      change position % 2^64 = 0 at hn
      rw [Nat.mod_eq_of_lt (by omega : position < 2^64)] at hn
      exact zero hn
    have ripD : d.RIP = 0x10167d := by simpa only [nonzeroRegister, ↓reduceIte] using target
    obtain ⟨setupFuel, a, setupRun, readyA, _, setup⟩ := fill_setup (returnBoundary initial)
      (returnBoundary_valid ctx).2.2 d readyD (fill_code bufferedD.loaded) ripD
    have setupFrame : AgreesExcept [.reg 3, .reg 7, .reg 6, .flags, .rip] d a := setup.agrees
    have bufferedA := buffered_of_noMem ctx bufferedD setupRun readyA setupFrame
      (by simp [Component.Covers]) (by simp) (by simp)
    have destination : a.regValue .rdi = hmacBase initial + BitVec.ofNat 64 position := by
      have word : a.regValue .rdi = rspOf d + d.regValue .r15 + 120 := setup.writes.2.1
      have tailD : d.regValue .r15 = BitVec.ofNat 64 position :=
        (sameD 15).trans state.tail
      rw [word, tailD]
      change d.regValue .rsp + BitVec.ofNat 64 position + 120 = _
      rw [bufferedD.rsp, hmacBase]
      bv_omega
    have source : a.regValue .rsi = inputs[i].address + BitVec.ofNat 64 0 :=
      (setup.writes.2.2.trans ((sameD 13).trans state.pointer)).trans
        (BitVec.add_zero inputs[i].address).symm
    have length : a.regValue .rdx = BitVec.ofNat 64 capacity :=
      (setupFrame.read (n := 64) (r := 2) (by simp)).trans ((sameD 2).trans state.capacity)
    have copyRegister : a.regValue .r12 = 0x10dd60 :=
      (setupFrame.read (n := 64) (r := 12) (by simp)).trans ((sameD 12).trans state.copyRegister)
    obtain ⟨copyFuel, c, copyRun, readyC, preservedC, ripC, abiC, frameC, copied⟩ :=
      Short.copy ctx bufferedA.toPreserved .fill i (sourceOffset := 0) (position := position)
        (count := capacity) (by simpa only [Nat.zero_add, bytes] using enough) extent
        setup.rip destination source length copyRegister
    have copiedSame (offset len : Nat) (bound : offset+len ≤ 144)
        (apart : offset+len ≤ position ∨ position+capacity ≤ offset) :
        (Component.mem (hmacBase initial + BitVec.ofNat 64 offset) len).Agrees a c := by
      have query := Short.copy_observation ctx frameC (offset := 400-offset) (len := len)
        extent (by omega) (by omega) (by rcases apart with h | h <;> omega)
      have addr : hmacBase initial + BitVec.ofNat 64 offset =
          stackPtr initial - BitVec.ofNat 64 (400-offset) := by
        change frameBase initial + BitVec.ofNat 64 120 + BitVec.ofNat 64 offset = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, address (120+offset) (by omega)]
        congr 2
        omega
      rw [addr]
      exact query
    have front : (⟨(hmacBase initial).toNat, (remainderBytes prior).size⟩ : MemoryRegion).HasBytes
        c.external (remainderBytes prior) := by
      refine ⟨rfl, ?_⟩
      intro j
      have hj : j.val < position := by simpa only [remainderBytes_size, priorPosition] using j.isLt
      have old := bufferedA.hmac.inner.tail.2 j
      have same := copiedSame 0 position (by omega) (.inl (by omega)) j.val hj
      simp only [BitVec.add_zero] at same
      change c.external[BitVec.ofNat 64 ((hmacBase initial).toNat + j.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, same]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, prior, remainderBytes]
        using old
    have back : (⟨(hmacBase initial + BitVec.ofNat 64 (remainderBytes prior).size).toNat,
        (bytes.extract 0 capacity).size⟩ : MemoryRegion).HasBytes c.external
        (bytes.extract 0 capacity) := by
      have sized : (bytes.extract 0 capacity).size = capacity := by
        rw [ByteArray.size_extract]; omega
      simpa only [remainderBytes_size, priorPosition, sized, Nat.zero_add, bytes] using copied
    have fullBytes := Hkdf.Proofs.Wrapper.Absorb.hasBytes_append front back
    have fullSize := Hkdf.Proofs.Wrapper.Absorb.filledBlock_size prior bytes
      (by simpa only [priorPosition] using enough)
    have blockC : (⟨(stackPtr initial - BitVec.ofNat 64 400).toNat, 64⟩ : MemoryRegion).HasBytes
        c.external (Hkdf.Proofs.Wrapper.Absorb.filledBlock prior bytes) := by
      change (⟨(hmacBase initial).toNat, _⟩ : MemoryRegion).HasBytes _ _ at fullBytes
      have sized : (remainderBytes prior ++ bytes.extract 0 capacity).size = 64 := by
        simpa only [Hkdf.Proofs.Wrapper.Absorb.filledBlock, priorPosition] using fullSize
      simpa only [Hkdf.Proofs.Wrapper.Absorb.filledBlock, priorPosition, hmacAddress, sized]
        using fullBytes
    have hashC := Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedA.hmac.inner.hashWords
      (copiedSame 64 32 (by decide) (.inr (by omega)))
    have blocksC : X86.Machine.loadBytes c.external (hmacBase initial+96) 8 =
        .ok (BitVec.ofNat 64 (prior.size/64)) :=
      (CallFrame.agrees_loadBytes (copiedSame 96 8 (by decide) (.inr (by omega)))).trans
        bufferedA.hmac.inner.blocks
    have outerHashC := Hkdf.Proofs.Wrapper.hashState_of_bytes bufferedA.hmac.outerHash
      (copiedSame 104 32 (by decide) (.inr (by omega)))
    have outerBlocksC : X86.Machine.loadBytes c.external (hmacBase initial+136) 8 = .ok 1 :=
      (CallFrame.agrees_loadBytes (copiedSame 136 8 (by decide) (.inr (by omega)))).trans
        bufferedA.hmac.outerBlocks
    have rbxC : c.regValue .rbx = inputs[i].address + BitVec.ofNat 64 capacity := by
      have word : a.regValue .rbx = d.regValue .rdx + d.regValue .r13 := setup.writes.1
      have capD : d.regValue .rdx = BitVec.ofNat 64 capacity := (sameD 2).trans state.capacity
      have ptrD : d.regValue .r13 = inputs[i].address := (sameD 13).trans state.pointer
      rw [abiC.1 .rbx (by simp), word, capD, ptrD, BitVec.add_comm]
    have rbpC : c.regValue .rbp = BitVec.ofNat 64 (bytes.size-capacity) := by
      have word := (abiC.1 .rbp (by simp)).trans
        ((setupFrame.read (n := 64) (r := 5) (by simp)).trans ((sameD 5).trans state.rest))
      exact word.trans (BitVec.ofNat_sub_ofNat_of_le _ _ (by
        have := extract_input_bound ctx.call i; omega) enough)
    have indexC : c.regValue .r14 = BitVec.ofNat 64 index :=
      (abiC.1 .r14 (by simp)).trans
        ((setupFrame.read (n := 64) (r := 14) (by simp)).trans
          ((sameD 14).trans state.indexRegister))
    have copyC : c.regValue .r12 = 0x10dd60 := (abiC.1 .r12 (by simp)).trans copyRegister
    have preCount : c.RIP = 0x10168f ∧ MemWritable c (rspOf c+216) 8 ∧
        RangeApart (rspOf c+216) 8 0x10168f 26 := by
      refine ⟨ripC.trans (by decide +kernel), ?_, ?_⟩
      · change MemWritable c (rspOf c + BitVec.ofNat 64 216) 8
        rw [stack_address preservedC.rsp (offset := 216) (by decide)]
        exact CallFrame.stack_writable8 ctx.call.stack
          (ctx.call.stackSeparation.2 _ (by simp)).2 preservedC.allocated (by decide) (by decide)
      · change RangeApart (rspOf c + BitVec.ofNat 64 216) 8 0x10168f 26
        rw [stack_address preservedC.rsp (offset := 216) (by decide)]
        exact stack_codeApart ctx (codeOffset := 0x168f) (by decide) (by decide) (by decide)
    obtain ⟨countFuel, e, countRun, readyE, _, countEffect⟩ :=
      fill_count_setup (returnBoundary initial) (returnBoundary_valid ctx).2.2 c readyC
        (programText_slice (programLoaded_codeIn preservedC.loaded) 0x168f fillCountBytes
          (by decide) (by decide +kernel)) preCount
    have countWrites : WritesWithin (fillCountEffect c).components
        (innerWriteRegions initial 8 304) := by
      intro component member a cover
      simp only [fillCountEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
        Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_assoc] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 304).toNat, 8⟩,
        by simp [innerWriteRegions],
        hash_output_memory ctx preservedC (by decide) (by decide) (by decide) cover⟩
    obtain ⟨preservedE, countFrame⟩ := effect_preserved ctx preservedC countRun readyE countEffect
      countWrites (by decide)
      (by simp [fillCountEffect, Effect.components, Write.component, Operand.component])
      (by simp [fillCountEffect, Effect.components, Write.component, Operand.component])
    have storesE := countEffect.writes
    simp only [fillCountEffect, Write.AllHold] at storesE
    have outputE : e.regValue .rdi = stackPtr initial - BitVec.ofNat 64 336 := by
      have value : e.regValue .rdi = rspOf c + BitVec.ofNat 64 184 := storesE.2.2.1
      rw [stack_address preservedC.rsp (offset := 184) (by decide)] at value
      exact value
    have sourceE : e.regValue .rsi = stackPtr initial - BitVec.ofNat 64 400 := by
      have value : e.regValue .rsi = rspOf c + BitVec.ofNat 64 120 := storesE.2.2.2
      rw [stack_address preservedC.rsp (offset := 120) (by decide)] at value
      exact value
    have countE : e.regValue .rdx = BitVec.ofNat 64 1 := storesE.2.1
    have blockE := inner_hasBytes_of_frame ctx countFrame (offset := 400) (len := 64)
      (by decide) (by decide) (by decide) (by decide) blockC
    have hashAddress : hmacBase initial + BitVec.ofNat 64 64 =
        stackPtr initial - BitVec.ofNat 64 336 := by
      change frameBase initial + BitVec.ofNat 64 120 + BitVec.ofNat 64 64 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, address 184 (by decide)]
    have countAddress : hmacBase initial + BitVec.ofNat 64 96 =
        stackPtr initial - BitVec.ofNat 64 304 := by
      change frameBase initial + BitVec.ofNat 64 120 + BitVec.ofNat 64 96 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, address 216 (by decide)]
    rw [hashAddress] at hashC
    have hashE := Hkdf.Proofs.Wrapper.hashState_of_bytes hashC
      (inner_frame_agrees ctx countFrame (offset := 336) (len := 32)
        (by decide) (by decide) (by decide) (by decide))
    have wordC : memLoad c.external (stackPtr initial - BitVec.ofNat 64 304) 64 =
        BitVec.ofNat 64 (prior.size/64) := by
      change X86.Machine.loadBytes c.external
        (hmacBase initial + BitVec.ofNat 64 96) 8 = _ at blocksC
      rw [countAddress] at blocksC
      exact Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64 blocksC
    have wordE : memLoad e.external (stackPtr initial - BitVec.ofNat 64 304) 64 =
        BitVec.ofNat 64 (prior.size/64+1) := by
      have value := storesE.1
      change memLoad e.external (rspOf c+BitVec.ofNat 64 216) 64 =
        memLoad c.external (rspOf c+BitVec.ofNat 64 216) 64+1 at value
      rw [stack_address preservedC.rsp (offset := 216) (by decide), wordC] at value
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using value
    have blocksE : X86.Machine.loadBytes e.external (hmacBase initial+BitVec.ofNat 64 96) 8 =
        .ok (BitVec.ofNat 64 (prior.size/64+1)) := by
      have data := Bytes.of_memLoad (n := 64)
        (stack_readable ctx preservedE.toState (offset := 304) (len := 8)
          (by decide) (by decide)).mem
      rw [wordE] at data
      change X86.Machine.loadBytes e.external (hmacBase initial + BitVec.ofNat 64 96) 8 = _
      rw [countAddress]
      exact data.loadBytes64
    obtain ⟨compressFuel, f, compressRun, readyF, preservedF, ripF, hashF, abiF, frameF⟩ :=
      compress_buffer ctx preservedE readyE countEffect.rip outputE sourceE countE hashE blockE
    have blocksF := (CallFrame.agrees_loadBytes
      (inner_frame_agrees ctx frameF (offset := 304) (len := 8)
        (by decide) (by decide) (by decide) (by decide))).trans
          (by simpa only [countAddress] using blocksE)
    have writableFinish : MemWritable f (rspOf f+183) 1 := by
      change MemWritable f (rspOf f+BitVec.ofNat 64 183) 1
      rw [stack_address preservedF.rsp (offset := 183) (by decide)]
      exact CallFrame.stack_writable1 ctx.call.stack
        (ctx.call.stackSeparation.2 _ (by simp)).2 preservedF.allocated (by decide)
    have apartFinish : RangeApart (rspOf f+183) 1 0x1016ae 11 := by
      change RangeApart (rspOf f+BitVec.ofNat 64 183) 1 0x1016ae 11
      rw [stack_address preservedF.rsp (offset := 183) (by decide)]
      exact stack_codeApart ctx (codeOffset := 0x16ae) (by decide) (by decide) (by decide)
    obtain ⟨finishFuel, g, finishRun, readyG, _, finishEffect⟩ := filled_setup
      (returnBoundary initial) (returnBoundary_valid ctx).2.2 f readyF
        (programText_slice (programLoaded_codeIn preservedF.loaded) 0x16ae filledBytes
          (by decide) (by decide +kernel)) ⟨ripF, writableFinish, apartFinish⟩
    have finishWrites : WritesWithin (filledEffect f).components
        (innerWriteRegions initial 1 337) := by
      intro component member a cover
      simp only [filledEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
        Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_assoc] at member
      rcases member with rfl | rfl | rfl
      all_goals try exact cover.elim
      exact ⟨⟨(stackPtr initial - BitVec.ofNat 64 337).toNat, 1⟩,
        by simp [innerWriteRegions],
        hash_output_memory ctx preservedF (by decide) (by decide) (by decide) cover⟩
    obtain ⟨preservedG, frameG⟩ := effect_preserved ctx preservedF finishRun readyG finishEffect
      finishWrites (by decide)
      (by simp [filledEffect, Effect.components, Write.component, Operand.component])
      (by simp [filledEffect, Effect.components, Write.component, Operand.component])
    have hashG := Hkdf.Proofs.Wrapper.hashState_of_bytes hashF
      (inner_frame_agrees ctx frameG (offset := 336) (len := 32)
        (by decide) (by decide) (by decide) (by decide))
    have blocksG := (CallFrame.agrees_loadBytes
      (inner_frame_agrees ctx frameG (offset := 304) (len := 8)
        (by decide) (by decide) (by decide) (by decide))).trans blocksF
    have outerSame (offset len : Nat) (low : 264 ≤ offset ∧ offset ≤ 296) (high : offset+32 ≤ 336)
        (size : len ≤ 40) :
        (Component.mem (stackPtr initial-BitVec.ofNat 64 offset) len).Agrees c g := by
      intro j hj
      exact (inner_frame_agrees ctx frameG (offset := offset) (len := len)
        (by omega) (by omega) (by omega) (by omega) (by omega) j hj).trans
        ((inner_frame_agrees ctx frameF (offset := offset) (len := len)
          (by omega) (by omega) (by omega) (by omega) (by omega) j hj).trans
          (inner_frame_agrees ctx countFrame (offset := offset) (len := len)
            (by omega) (by omega) (by omega) (by omega) (by omega) j hj))
    have outerHashG := Hkdf.Proofs.Wrapper.hashState_of_bytes outerHashC
      (by change (Component.mem (hmacBase initial+BitVec.ofNat 64 104) 32).Agrees c g
          change (Component.mem (frameBase initial+BitVec.ofNat 64 120+
            BitVec.ofNat 64 104) 32).Agrees c g
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, address 224 (by decide)]
          exact outerSame 296 32 (by decide) (by decide) (by decide))
    have outerBlocksG : X86.Machine.loadBytes g.external (hmacBase initial+136) 8 = .ok 1 := by
      apply Eq.trans _ outerBlocksC
      apply CallFrame.agrees_loadBytes
      change (Component.mem (frameBase initial+BitVec.ofNat 64 120+
        BitVec.ofNat 64 136) 8).Agrees c g
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, address 256 (by decide)]
      exact outerSame 264 8 (by decide) (by decide) (by decide)
    have lengthG : g.external[hmacBase initial+63]? = some 0 := by
      have value := finishEffect.writes.1
      change memLoad g.external (rspOf f+BitVec.ofNat 64 183) 8 = 0 at value
      rw [stack_address preservedF.rsp (offset := 183) (by decide)] at value
      have data := Bytes.of_memLoad (n := 8)
        (stack_readable ctx preservedG.toState (offset := 337) (len := 1)
          (by decide) (by decide)).mem
      rw [value] at data
      have byte := data 0 (by decide)
      change g.external[frameBase initial+120+63]? = some 0
      change g.external[frameBase initial+BitVec.ofNat 64 120+BitVec.ofNat 64 63]? = some 0
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, address 183 (by decide)]
      rw [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] at byte
      exact byte
    have whole : prior ++ bytes.extract 0 capacity =
        HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++
          (previous ++ bytes.extract 0 capacity) := ByteArray.append_assoc
    have aligned : (previous ++ bytes.extract 0 capacity).size % 64 = 0 := by
      rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left enough, Nat.sub_zero]
      dsimp only [capacity, position]
      omega
    have bufferedG : Buffered initial g salt (previous ++ bytes.extract 0 capacity) := by
      refine ⟨preservedG, ?_, outerHashG, outerBlocksG⟩
      rw [← whole]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have computed := Hkdf.Proofs.Wrapper.Absorb.compressBlocks_filled_prefix
          Hkdf.Proofs.NIST.SHA256.initialHash prior bytes
            (by simpa only [priorPosition] using enough)
        rw [priorPosition] at computed
        change HashStateAt g (hmacBase initial+BitVec.ofNat 64 64) _
        rw [hashAddress, computed]
        simpa only [compressBlocks_single _ _ fullSize] using hashG
      · have zeroTail : (prior ++ bytes.extract 0 capacity).size % 64 = 0 := by
          simpa only [priorPosition] using counts.1
        have tailEmpty : ((prior ++ bytes.extract 0 capacity).extract
            (64*((prior ++ bytes.extract 0 capacity).size/64))
              (prior ++ bytes.extract 0 capacity).size) = ByteArray.empty := by
          have div : 64*((prior ++ bytes.extract 0 capacity).size/64) =
              (prior ++ bytes.extract 0 capacity).size := by omega
          rw [div, ByteArray.extract_same]
        rw [zeroTail, tailEmpty]
        exact ⟨rfl, fun j ↦ Fin.elim0 j⟩
      · have zeroTail : (prior ++ bytes.extract 0 capacity).size % 64 = 0 := by
          simpa only [priorPosition] using counts.1
        rw [zeroTail]
        exact lengthG
      · have blockCount : (prior ++ bytes.extract 0 capacity).size / 64 = prior.size/64+1 := by
          simpa only [priorPosition] using counts.2
        change X86.Machine.loadBytes g.external (hmacBase initial+BitVec.ofNat 64 96) 8 = _
        rw [countAddress, blockCount]
        exact blocksG
    have keptCount (r : BitVec 5) (member : r ∈ ([3,5,12,14] : List (BitVec 5))) :
        (Operand.reg r : Operand 64).read e = (Operand.reg r : Operand 64).read c := by
      apply countEffect.agrees.read
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [fillCountEffect, Effect.components, Write.component, Operand.component]
    have keptFinish (r : BitVec 5) (member : r ∈ ([5,12,14] : List (BitVec 5))) :
        (Operand.reg r : Operand 64).read g = (Operand.reg r : Operand 64).read f := by
      apply finishEffect.agrees.read
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;>
        simp [filledEffect, Effect.components, Write.component, Operand.component]
    refine ⟨2+setupFuel+copyFuel+countFuel+compressFuel+finishFuel, g, capacity, false,
      ((((dispatchRun.trans setupRun).trans copyRun).trans countRun).trans compressRun).trans
        finishRun,
        readyG, ?_⟩
    refine ⟨bufferedG, enough, aligned, finishEffect.rip, ?_, ?_, ?_, ?_⟩
    · have value : g.regValue .r13 = f.regValue .rbx := finishEffect.writes.2
      exact value.trans ((abiF.1 .rbx (by simp)).trans ((keptCount 3 (by simp)).trans rbxC))
    · exact (keptFinish 5 (by simp)).trans
        ((abiF.1 .rbp (by simp)).trans ((keptCount 5 (by simp)).trans rbpC))
    · exact (keptFinish 14 (by simp)).trans
        ((abiF.1 .r14 (by simp)).trans ((keptCount 14 (by simp)).trans indexC))
    · exact (keptFinish 12 (by simp)).trans
        ((abiF.1 .r12 (by simp)).trans ((keptCount 12 (by simp)).trans copyC))

theorem long_input [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : PreparedInput initial s salt inputs index false) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      InputDone initial t salt inputs index false := by
  obtain ⟨firstFuel, u, consumed, direct, first, readyU, inputU⟩ := long_to_bulk ctx ready state
  obtain ⟨secondFuel, t, second, readyT, done⟩ := bulk_input ctx readyU inputU
  exact ⟨firstFuel+secondFuel, t, first.trans second, readyT, done⟩

end Hkdf.Proofs.Standard.Update
