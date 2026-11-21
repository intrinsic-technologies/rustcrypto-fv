import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Push
import X86Proofs.Instructions.MovStore.Triple

namespace Hkdf.Proofs.NewExpand.Expand.Prologue

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

def effect (s : RamState) : Effect where
  rip := 0x10f281
  writes :=
    [⟨(.reg 4 : Operand 64), s.regValue .rsp - 536⟩,
     ⟨(.mem (s.regValue .rsp - 8) : Operand 64), s.regValue .rbp⟩,
     ⟨(.mem (s.regValue .rsp - 16) : Operand 64), s.regValue .r15⟩,
     ⟨(.mem (s.regValue .rsp - 24) : Operand 64), s.regValue .r14⟩,
     ⟨(.mem (s.regValue .rsp - 32) : Operand 64), s.regValue .r13⟩,
     ⟨(.mem (s.regValue .rsp - 40) : Operand 64), s.regValue .r12⟩,
     ⟨(.mem (s.regValue .rsp - 48) : Operand 64), s.regValue .rbx⟩,
     ⟨(.mem (s.regValue .rsp - 288) : Operand 64), s.regValue .rdx⟩,
     ⟨(.mem (s.regValue .rsp - 304) : Operand 64), s.regValue .rsi⟩,
     ⟨(.mem (s.regValue .rsp - 296) : Operand 64), s.regValue .rdi⟩,
     ⟨(.mem (s.regValue .rsp - 312) : Operand 64), s.regValue .r8⟩]
  flags := some (.ofStatusFlags (subSpec (s.regValue .rsp - 48) 488).2)

private theorem spill [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {reserve : Nat}
    (stack : Stack.Valid entry reserve)
    (avoid : (Stack.region entry reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (entry.external[a]?).isSome → (s.external[a]?).isSome)
    (pc offset : Nat) (rex : UInt8) (reg : BitVec 3) (disp : BitVec 32)
    (ip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (sp : stackPtr s = stackPtr entry - 536)
    (rel : -536 + disp.signExtend 64 = -BitVec.ofNat 64 offset)
    (below : 8 ≤ offset) (within : offset ≤ reserve) (align : offset % 8 = 0)
    (bound : pc + 8 < 115149) (prefixW : RexWPrefix rex.toBitVec)
    (rx : rexX rex.toBitVec = 0) (rb : rexB rex.toBitVec = 0)
    (bytes : let am := AddrMode.sib 4 none 0 (.d32 disp)
      Extracted.textBytes.toListFrom pc 8 = rex :: 0x89 :: am.modrm reg :: am.tail) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + 8) ∧
      AgreesExcept [.mem (stackPtr entry - BitVec.ofNat 64 offset) 8, .rip] s t ∧
      t.external = memStore s.external (stackPtr entry - BitVec.ofNat 64 offset)
        ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read s) := by
  let am := AddrMode.sib 4 none 0 (.d32 disp)
  have addr : am.addrAt s 8 = stackPtr entry - BitVec.ofNat 64 offset := by
    change stackPtr s + disp.signExtend 64 = _
    rw [sp, BitVec.sub_eq_add_neg, BitVec.add_assoc, rel, BitVec.sub_eq_add_neg]
  have writable : MemWritable s (am.addrAt s 8) 8 := by
    rw [addr]
    exact stack_writable8 stack avoid grow within align
  have code := programText_slice (programLoaded_codeIn loaded) pc
    (rex :: 0x89 :: am.modrm reg :: am.tail) (by change pc + 8 ≤ 115149; omega) bytes
  have step := mov_m64_r64_step s ready rex prefixW reg am (by simp [am, AddrMode.Valid]) rx rb
    (ip ▸ code.bytesAt) (by rw [ip]; exact code.low_len (len := 8) rfl (by decide) (by decide)) writable
  let value := (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read s
  let t := afterStep s 8 fun u ↦ writeResult (dataAccess u "store")
    (.mem (am.addrAt s 8) : Operand 64) value (BitVec.add s.RIP 8)
  have next : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + 8) := by
    rw [show t.RIP = BitVec.add s.RIP 8 from afterStep_store_rip ready _ _ _ _, ip]
    change (Extracted.textAddress + BitVec.ofNat 64 pc) + 8 = _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
    rfl
  have frame : AgreesExcept [.mem (am.addrAt s 8) 8, .rip] s t :=
    AgreesExcept.afterStep_store s 8 (am.addrAt s 8) value (BitVec.add s.RIP 8)
  rw [addr] at frame
  have writes : WritesWithin [.mem (stackPtr entry - BitVec.ofNat 64 offset) 8, .rip]
      #v[Stack.region entry reserve] := by
    apply CallFrame.stack_slot_within stack within below
    intro c hc a ha
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · rcases List.mem_singleton.mp hc with rfl
      exact ha.elim
  refine ⟨t, Advances.of_step step (.inl (next ▸ boundary_ne_program outside
    (inProgram_of_textOffset (pc + 8) bound))), ready.afterStep_store _ _ _ _ writable.low writable.tables,
    programLoaded_of_memoryWriteFrame (frame.memoryWriteFrame writes) loaded
      (CallFrame.stack_avoids avoid), next, frame, ?_⟩
  rw [← addr]
  rfl

private def spilledMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (memStore (Encoding.Serialize.saveMemory s)
    (stackPtr s - 288) (s.regValue .rdx))
    (stackPtr s - 304) (s.regValue .rsi))
    (stackPtr s - 296) (s.regValue .rdi))
    (stackPtr s - 312) (s.regValue .r8)

private theorem spill_writes {s t : RamState} (sp : stackPtr t = stackPtr s - 536)
    (memory : t.external = spilledMemory s) : Write.AllHold t (effect s).writes := by
  refine ⟨sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    change memLoad t.external (stackPtr s - _) 64 = _
    rw [memory]
    simp only [spilledMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  all_goals simp only [← BitVec.sub_eq_add_neg]
  · exact Encoding.Serialize.saveMemory_saved s (.rbp, 8) (by decide)
  · exact Encoding.Serialize.saveMemory_saved s (.r15, 16) (by decide)
  · exact Encoding.Serialize.saveMemory_saved s (.r14, 24) (by decide)
  · exact Encoding.Serialize.saveMemory_saved s (.r13, 32) (by decide)
  · exact Encoding.Serialize.saveMemory_saved s (.r12, 40) (by decide)
  · exact Encoding.Serialize.saveMemory_saved s (.rbx, 48) (by decide)
  all_goals exact memLoad_memStore _ _ (n := 64) (by decide) (by decide) _

theorem run [Bindings] {entry : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) :
    ∃ fuel s, Advances boundary fuel entry s ∧ ReadyToStep s ∧ (effect entry).Holds entry s := by
  have saveCode : Encoding.Serialize.SaveCode 0xf250 := by constructor <;> decide +kernel
  obtain ⟨saved, saveRun, ready, loaded, pc, savedSP, savedMem, savedFrame⟩ :=
    Encoding.Serialize.save_registers_of_push (codeOffset := 0xf250)
      (CallFrame.push_steps pre.call.stack (by decide) pre.call.stackAvoid pre.call.outerBoundary)
      (supportedMachine_readyToStep pre.call.machine) pre.call.loaded pre.call.rip saveCode
  obtain ⟨s, alloc, readyS, sub⟩ :=
    (sub_r64_imm32_effect_step 0x10f25a 0x48 0xec 488
      (by constructor <;> decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xf25a
        [0x48, 0x81, 0xec, 0xe8, 1, 0, 0] (by decide) (by decide +kernel)) pc
      (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xf261 (by decide)))
  have allocatedFrame : AgreesExcept (Encoding.Serialize.saveFrame entry ++ [.reg 4, .flags, .rip]) entry s :=
    savedFrame.trans sub.agrees
  have memS := sub.agrees.external (by simp [Component.Covers])
  have loadedS : ProgramLoaded s := fun a b hb ↦ memS ▸ loaded a b hb
  have spS : stackPtr s = stackPtr entry - 536 := by
    rw [show stackPtr s = stackPtr saved - 488 from sub.writes, savedSP, BitVec.sub_sub]
    rfl
  obtain ⟨s1, a1, r1, l1, pc1, f1, m1⟩ :=
    spill pre.call.stack pre.call.stackAvoid pre.call.outerBoundary readyS loadedS allocatedFrame.grow
      0xf261 288 0x48 2 248 sub.rip spS rfl (by decide) (by decide) (by decide) (by decide)
      (by simp [RexWPrefix]) rfl rfl (by decide +kernel)
  have f01 := allocatedFrame.trans f1
  have sp1 := (f1.read (r := 4) (n := 64) (by simp)).trans spS
  obtain ⟨s2, a2, r2, l2, pc2, f2, m2⟩ :=
    spill pre.call.stack pre.call.stackAvoid pre.call.outerBoundary r1 l1 f01.grow
      0xf269 304 0x48 6 232 pc1 sp1 rfl (by decide) (by decide) (by decide) (by decide)
      (by simp [RexWPrefix]) rfl rfl (by decide +kernel)
  have f02 := f01.trans f2
  have sp2 := (f2.read (r := 4) (n := 64) (by simp)).trans sp1
  obtain ⟨s3, a3, r3, l3, pc3, f3, m3⟩ :=
    spill pre.call.stack pre.call.stackAvoid pre.call.outerBoundary r2 l2 f02.grow
      0xf271 296 0x48 7 240 pc2 sp2 rfl (by decide) (by decide) (by decide) (by decide)
      (by simp [RexWPrefix]) rfl rfl (by decide +kernel)
  have f03 := f02.trans f3
  have sp3 := (f3.read (r := 4) (n := 64) (by simp)).trans sp2
  obtain ⟨t, a4, rt, _, pct, f4, m4⟩ :=
    spill pre.call.stack pre.call.stackAvoid pre.call.outerBoundary r3 l3 f03.grow
      0xf279 312 0x4c 0 224 pc3 sp3 rfl (by decide) (by decide) (by decide) (by decide)
      (by simp [RexWPrefix]) rfl rfl (by decide +kernel)
  refine ⟨11, t, (((((saveRun.trans alloc).trans a1).trans a2).trans a3).trans a4), rt, pct,
    spill_writes ((f4.read (r := 4) (n := 64) (by simp)).trans sp3) ?_, ?_, ?_⟩
  · have rd := allocatedFrame.read (r := 2) (n := 64) (by simp [Encoding.Serialize.saveFrame])
    have si := f01.read (r := 6) (n := 64) (by simp [Encoding.Serialize.saveFrame])
    have di := f02.read (r := 7) (n := 64) (by simp [Encoding.Serialize.saveFrame])
    have r8 := f03.read (r := 8) (n := 64) (by simp [Encoding.Serialize.saveFrame])
    rw [m4, m3, m2, m1, memS, savedMem]
    simp only [show gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2 = 2 from rfl,
      show gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 6 = 6 from rfl,
      show gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 7 = 7 from rfl,
      show gprNumber 0 (rexR (0x4c : UInt8).toBitVec) 0 = 8 from rfl, rd, si, di, r8]
    rfl
  · change (StatusFlagsOutcome.ofStatusFlags (subSpec (stackPtr entry - 48) 488).2).Allows _
    rw [(((f1.trans f2).trans f3).trans f4).statusFlags (by simp), ← savedSP]
    exact sub.flags
  · apply (f03.trans f4).mono
    simp only [Encoding.Serialize.saveFrame, effect, Effect.components, List.map_cons,
      Write.component_reg, Write.component_mem, Nat.reduceDiv, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    simp only [show entry.regValue .rsp = stackPtr entry from rfl]
    grind only

end Hkdf.Proofs.NewExpand.Expand.Prologue
