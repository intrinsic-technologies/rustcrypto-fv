import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Frame
import Md5.Proofs.Block.Bytes
import Md5.Proofs.MemoryRoutines.Ranges
import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Rounds.Store.Compose
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Md5.Proofs.NewEntries.UpdateFinalize.Epilogue

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

structure RestorePre (s : RamState) : Prop where
  rip : s.RIP = 0x101b81
  read : MemReadable s (stackPtr s + 280) 56

def restoreBytes : List UInt8 :=
  [0x48, 0x81, 0xc4, 0x18, 1, 0, 0,
    0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]

def restoreEffect (s : RamState) : Effect :=
  { rip := 0x101b81 + 17
    writes := [
      ⟨.reg 3, (Operand.mem (stackPtr s + BitVec.ofNat 64 280) : Operand 64).read s⟩,
      ⟨.reg 12, (Operand.mem (stackPtr s + BitVec.ofNat 64 (280 + 8)) : Operand 64).read s⟩,
      ⟨.reg 13, (Operand.mem (stackPtr s + BitVec.ofNat 64 (280 + 16)) : Operand 64).read s⟩,
      ⟨.reg 14, (Operand.mem (stackPtr s + BitVec.ofNat 64 (280 + 24)) : Operand 64).read s⟩,
      ⟨.reg 15, (Operand.mem (stackPtr s + BitVec.ofNat 64 (280 + 32)) : Operand 64).read s⟩,
      ⟨.reg 5, (Operand.mem (stackPtr s + BitVec.ofNat 64 (280 + 40)) : Operand 64).read s⟩,
      ⟨.reg 4, stackPtr s + BitVec.ofNat 64 (280 + 48)⟩]
    flags := some (.ofStatusFlags (addSpec (stackPtr s) (BitVec.ofNat 64 280)).2) }

private theorem pop_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (popR64Effect p len dst) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro t t' h
    have hsp : stackPtr t = stackPtr t' := congrArg (fun g ↦ g[gprIndex 4]) h.gpr
    simp only [popR64Effect, hsp, h.read_mem]
  · intro t t' _ i hi
    exact congrArg some hi
  · intro t
    simp [popR64Effect, Write.Full, Operand.Full]

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_local] pop_local
attribute [local x86_compose] popR64Effect addR64Imm32Effect stackPtr_read

private theorem pop_pre {s t : RamState} {e : Effect} {p : BitVec 64}
    (h : e.Holds s t) (ho : Obs (e.after s true) t) (hp : e.rip = p)
    (hr : MemReadable s (stackPtr (e.after s true)) 8) : PopPre p t := by
  refine ⟨h.rip_of hp, ?_⟩
  have hsp : stackPtr (e.after s true) = stackPtr t := ho.read (.reg 4 : Operand 64) trivial
  rw [← hsp]
  exact hr.of_holds h

set_option maxHeartbeats 600000 in
theorem restore [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary RestorePre
      (codeRange 0x101b81 restoreBytes) restoreEffect := by
  change AdvancesBlock boundary RestorePre
    (codeRange 0x101b81 [0x48, 0x81, 0xc4, 0x18, 0x01, 0x00, 0x00,
      0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) _
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x101b81)
      (codeRange 0x101b81 [0x48, 0x81, 0xc4, 0x18, 1, 0, 0])
      (addR64Imm32Effect 0x101b81 4 280) :=
    add_r64_imm32_effect_step 0x101b81 0x48 0xc4 280
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x101b81 + 7)) (codeRange (0x101b81 + 7) [0x5b])
      (popR64Effect (0x101b81 + 7) 1 3) :=
    pop_r64_effect_step (0x101b81 + 7) 0x5b (by decide) (by decide)
  have hPop1 : StepEffect (PopPre (0x101b81 + 8)) (codeRange (0x101b81 + 8) [0x41, 0x5c])
      (popR64Effect (0x101b81 + 8) 2 12) :=
    pop_r64_rex_effect_step (0x101b81 + 8) 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop2 : StepEffect (PopPre (0x101b81 + 10)) (codeRange (0x101b81 + 10) [0x41, 0x5d])
      (popR64Effect (0x101b81 + 10) 2 13) :=
    pop_r64_rex_effect_step (0x101b81 + 10) 0x41 0x5d
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop3 : StepEffect (PopPre (0x101b81 + 12)) (codeRange (0x101b81 + 12) [0x41, 0x5e])
      (popR64Effect (0x101b81 + 12) 2 14) :=
    pop_r64_rex_effect_step (0x101b81 + 12) 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop4 : StepEffect (PopPre (0x101b81 + 14)) (codeRange (0x101b81 + 14) [0x41, 0x5f])
      (popR64Effect (0x101b81 + 14) 2 15) :=
    pop_r64_rex_effect_step (0x101b81 + 14) 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre (0x101b81 + 16)) (codeRange (0x101b81 + 16) [0x5d])
      (popR64Effect (0x101b81 + 16) 1 5) :=
    pop_r64_effect_step (0x101b81 + 16) 0x5d (by decide) (by decide)
  md5_run_begin hAdd
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b88 (by decide +kernel)
  md5_run_then hPop0
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b89 (by decide +kernel)
  md5_run_then hPop1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b8b (by decide +kernel)
  md5_run_then hPop2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b8d (by decide +kernel)
  md5_run_then hPop3
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b8f (by decide +kernel)
  md5_run_then hPop4
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b91 (by decide +kernel)
  md5_run_then hPop5
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1b92 (by decide +kernel)
  md5_run_finish [restoreEffect]
  all_goals
    intro s t hP hH hO
    refine ⟨pop_pre hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
    x86_norm
    first
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd] using
          MemoryRoutines.memReadable_slice hP.read 0 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd] using
          MemoryRoutines.memReadable_slice hP.read 8 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd] using
          MemoryRoutines.memReadable_slice hP.read 16 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd] using
          MemoryRoutines.memReadable_slice hP.read 24 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd] using
          MemoryRoutines.memReadable_slice hP.read 32 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd] using
          MemoryRoutines.memReadable_slice hP.read 40 8 (by decide +kernel)


structure PreparePre (s : RamState) : Prop where
  rip : s.RIP = 0x101b69
  read : MemReadable s (stackPtr s) 336

def prepareBytes : List UInt8 :=
  [0x48,0x8b,0x04,0x24,0x48,0x8b,0x4c,0x24,0x08,
    0x48,0x8b,0x94,0x24,0xa8,0,0,0]

def prepareEffect (s : RamState) : Effect where
  rip := 0x101b7a
  writes := [
    ⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s) : Operand 64).read s⟩,
    ⟨(.reg 1 : Operand 64), (Operand.mem (stackPtr s + 8) : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), (Operand.mem (stackPtr s + 168) : Operand 64).read s⟩]

set_option maxHeartbeats 800000 in
theorem prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary PreparePre (codeRange 0x101b69 prepareBytes)
      prepareEffect := by
  unfold prepareBytes
  have h0 : StepEffect
      (LoadPre 0x101b69 (storeAddrAt 0x101b69 (.sib 4 none 0 .none) 4) 8)
      (codeRange 0x101b69 [ 0x48, 0x8b, 0x4, 0x24 ])
      (movR64M64Effect 0x101b69 0 (.sib 4 none 0 .none)) :=
    mov_r64_m64_effect_step 0x101b69 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 .none) (by decide) (by decide) (by decide)
  have h1 : StepEffect
      (LoadPre (0x101b69 + 4) (storeAddrAt (0x101b69 + 4) (.sib 4 none 0 (.d8 8)) 5) 8)
      (codeRange (0x101b69 + 4) [ 0x48, 0x8b, 0x4c, 0x24, 0x8 ])
      (movR64M64Effect (0x101b69 + 4) 1 (.sib 4 none 0 (.d8 8))) :=
    mov_r64_m64_effect_step (0x101b69 + 4) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  have h4 : StepEffect
      (LoadPre (0x101b69 + 9) (storeAddrAt (0x101b69 + 9) (.sib 4 none 0 (.d32 168)) 8) 8)
      (codeRange (0x101b69 + 9) [ 0x48, 0x8b, 0x94, 0x24, 0xa8, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x101b69 + 9) 2 (.sib 4 none 0 (.d32 168))) :=
    mov_r64_m64_effect_step (0x101b69 + 9) 0x48 (by unfold RexWPrefix; decide) 2
      (.sib 4 none 0 (.d32 168)) (by decide) (by decide) (by decide)
  md5_run_begin h0
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using
      MemoryRoutines.memReadable_slice h.read 0 8 (by decide)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1b6d (by decide +kernel)
  md5_run_then h1
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr] using
        MemoryRoutines.memReadable_slice h.read 8 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1b72 (by decide +kernel)
  md5_run_then h4
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr] using
        MemoryRoutines.memReadable_slice h.read 168 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1b7a (by decide +kernel)
  md5_run_finish [prepareEffect, BitVec.add_zero]

private theorem writableRange_write {s : RamState} {a : BitVec 64} {n : Nat}
    (h : MemoryRoutines.WritableRange s a n) : Memory.MemWritable s a n :=
  ⟨h.readable.low, h.readable.mem, h.tables⟩

private theorem writableRange_textApart {s : RamState} {a : BitVec 64} {n : Nat}
    (h : MemoryRoutines.WritableRange s a n) (offset count : Nat)
    (hbound : offset + count ≤ Extracted.textBytes.size) :
    RangeApart a n (Extracted.textAddress + BitVec.ofNat 64 offset) count := by
  intro i hi j hj he
  apply h.code i hi
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (offset + j) (by omega)

def epilogueOutput (s : RamState) : BitVec 64 := (Operand.reg 2 : Operand 64).read s

structure OutputPre (s : RamState) : Prop where
  rip : s.RIP = 0x101b7a
  write : MemoryRoutines.WritableRange s (epilogueOutput s) 16

def outputEffect (s : RamState) : Effect where
  rip := 0x101b81
  writes := [
    ⟨(.mem (epilogueOutput s + 8) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
    ⟨(.mem (epilogueOutput s) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩]

def outputBytes : List UInt8 := [0x48, 0x89, 0x4a, 0x8, 0x48, 0x89, 0x2]

set_option maxHeartbeats 400000 in
theorem output [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary OutputPre (codeRange 0x101b7a outputBytes)
      outputEffect := by
  unfold outputBytes
  have h0 : StepEffect (Memory.StorePre 0x101b7a 4
      (storeAddrAt 0x101b7a (.base 2 (.d8 8)) 4) 8)
      (codeRange 0x101b7a [0x48, 0x89, 0x4a, 0x8])
      (movM64R64Effect 0x101b7a 1 (.base 2 (.d8 8))) :=
    Buffered.Stores.mov_m64_r64_effect_step 0x101b7a 0x48 (by unfold RexWPrefix; decide) 1
      (.base 2 (.d8 8)) (by decide) (by decide) (by decide)
  have h1 : StepEffect (Memory.StorePre (0x101b7a + 4) 3
      (storeAddrAt (0x101b7a + 4) (.base 2 .none) 3) 8)
      (codeRange (0x101b7a + 4) [0x48, 0x89, 0x2])
      (movM64R64Effect (0x101b7a + 4) 0 (.base 2 .none)) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x101b7a + 4) 0x48 (by unfold RexWPrefix; decide) 0
      (.base 2 .none) (by decide) (by decide) (by decide)
  refine AdvancesBlock.block_first ?k h0 (by x86_sub) ?pre ?av ?boundary
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        BitVec.add_assoc] using
        writableRange_write (h.write.slice 8 8 (by decide))
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 8 8 (by decide)) 0x1b7a 4
          (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [epilogueOutput, BitVec.add_assoc, Extracted.textAddress] using
      writableRange_textApart (h.write.slice 8 8 (by decide)) 0x1b7a 7
        (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1b7e (by decide +kernel)
  refine AdvancesBlock.block_then ?copyEnd h1 (by x86_local) (by x86_sub)
    (by x86_full) ?mid ?boundary2
  case' copyEnd => x86_norm
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [epilogueOutput] using
          writableRange_write (h.write.slice 0 8 (by decide))
      · x86_norm
        simpa [epilogueOutput, Extracted.textAddress] using
          writableRange_textApart (h.write.slice 0 8 (by decide)) 0x1b7e 3
            (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [epilogueOutput, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 0 8 (by decide)) 0x1b7a 7
          (by decide +kernel)
  case boundary2 =>
    intro _ _
    exact text_address_ne_return hOutside 0x1b81 (by decide +kernel)
  md5_run_finish [outputEffect, epilogueOutput,
    BitVec.add_zero]

end Md5.Proofs.NewEntries.UpdateFinalize.Epilogue
