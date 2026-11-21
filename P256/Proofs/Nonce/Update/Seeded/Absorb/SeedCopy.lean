import P256.Proofs.Nonce.Update.Absorb.SeedCallPre
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Nonce.Update.Absorb.Seeded.Zero.Correct
import P256.Proofs.Program.Copy
import P256.Proofs.Nonce.Update.Absorb.SeedCopy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb

theorem copy_seed [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original : State} {address : BitVec 64}
    {sourceOffset count outputOffset : Nat}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (frame : FrameState initial s)
    (access : count = 0 ∨ ∃ inputBytes : ByteArray, UpdateSeedAt initial address inputBytes ∧
      sourceOffset + count ≤ inputBytes.size)
    (outputAbove : outputOffset ≤ 680) (outputEnd : count + 48 ≤ outputOffset)
    (small : count < 2^32)
    (offset : Nat) (size : offset + 3 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 3 = [0x41,0xff,0xd5])
    (pointer : s.regValue .r13 = 0x11c930)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (source : s.regValue .rsi = address + BitVec.ofNat 64 sourceOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (countRegister : s.regValue .rdx = BitVec.ofNat 64 count) :
    ∃ t, SeedCopyResult initial s t boundary count outputOffset
      (Extracted.textAddress + BitVec.ofNat 64 offset + 3) (address + BitVec.ofNat 64 sourceOffset) := by
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [ScalarFrame.scalar_call_address frame]
    exact P256.Proofs.Program.writable_of_grow
      (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) frame.allocated
  have apart : RangeApart (pushAddr s) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) 3 := by
    rw [ScalarFrame.scalar_call_address frame]
    intro i hi j hj he
    apply pre.avoids (Stack.region initial 1856) (by simp)
      (stackPtr initial - 688 + BitVec.ofNat 64 i)
    · exact ScalarFrame.stack_contains pre.callee (offset := 688) (len := 8)
        (by decide) (by decide) ⟨i, hi, rfl⟩
    · left
      change stackPtr initial - 688 + BitVec.ofNat 64 i = _ at he
      rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset (offset + j) (by omega)
  obtain ⟨call, step, ready, originalEffect⟩ :=
    call_r64_rex_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset) 0x41 0xd5
      (by simp [RexPrefix]) rfl rfl s (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) offset _ (by change offset + 3 ≤ 118431; omega) bytes)
      ⟨⟨rip, writable, apart⟩, by change (s.regValue .r13).toNat < 2^32; rw [pointer]; decide⟩
  have effect : (callEffect (fun _ => 0x11c930)
      (Extracted.textAddress + BitVec.ofNat 64 offset + 3) s).Holds s call := by
    change (callEffect (fun u => u.regValue .r13)
      (Extracted.textAddress + BitVec.ofNat 64 offset + 3) s).Holds s call at originalEffect
    simpa only [callEffect, pushEffect, pointer] using originalEffect
  have entry : call.RIP = 0x11c930 := effect.rip
  have run : Advances boundary 1 s call := Advances.of_step step (.inl (by
    rw [entry]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have callFrame := frame.after_call pre.callee (by decide) (by decide) ready effect
  have callMemory : MemoryWriteFrame s call #v[ScalarFrame.workRegion initial 1856] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨ScalarFrame.workRegion initial 1856, by simp, ?_⟩
      rw [ScalarFrame.scalar_call_address frame] at ha
      exact ScalarFrame.work_contains pre.callee (by decide) (by decide) ha
    · exact ha.elim
  have sourceCall : call.regValue .rsi = address + BitVec.ofNat 64 sourceOffset :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationCall : call.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have countCall : call.regValue .rdx = BitVec.ofNat 64 count :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans countRegister
  have retIn : InProgram (returnBoundary call).rip := by
    change InProgram (stackTop call)
    rw [(callEffect_stack effect).1]
    change InProgram (Extracted.textAddress + BitVec.ofNat 64 offset + 3)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      inProgram_of_textOffset (offset + 3) size
  obtain ⟨t, result, copied⟩ : ∃ t, CalleeResult call t boundary count 0 ∧
      ∀ i < count, t.external[call.regValue .rdi + BitVec.ofNat 64 i]? =
        call.external[call.regValue .rsi + BitVec.ofNat 64 i]? := by
    rcases access with zero | ⟨inputBytes, seed, span⟩
    · have stackReadable : MemReadable call (stackPtr call) 8 := by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          ScalarFrame.stack_readable pre.callee callFrame (offset := 0) (len := 8) (by decide) (by decide)
      obtain ⟨t, result, _, _⟩ := Update.Absorb.Seeded.Zero.memcpy_zero_correct
        (reserve := 0) callFrame.bindingsSupported callFrame.machine callFrame.loaded callFrame.directionFlag entry
        (by change call.regValue .rdx = 0#64; simpa only [zero] using countCall) stackReadable (by
          change (stackTop call).toNat < 2^32
          rw [(callEffect_stack effect).1]
          simp only [Extracted.textAddress]
          bv_omega) pre.outerBoundary (boundary_ne_program pre.outerBoundary retIn)
      exact ⟨t, by simpa only [zero] using result, by intro i hi; omega⟩
    · have callPre : CalleePre call boundary 0x11c930 count count 0 :=
        seed_callee_pre pre callFrame seed span outputAbove outputEnd sourceCall destinationCall entry retIn
      obtain ⟨t, result, copied, _⟩ := P256.Proofs.Program.memcpy_correct callPre countCall small
      exact ⟨t, result, copied⟩
  have copyMemory := result.stack_frame (savedBytes := 48) pre.stack callFrame.rsp
    destinationCall (by decide) (by decide) (by omega) outputEnd
  have frameT : ScalarFrame.FrameState initial t 64 1856 680 :=
    Update.frame_after_result pre.callee (by decide) callFrame result (by
      intro a ha
      apply copyMemory a
      intro region member inside
      have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
      subst region
      exact ha _ (by simp) inside)
      (result.rsp.trans ((callEffect_stack effect).2.trans frame.rsp))
  have calleeSaved : CalleeSavedRegistersUnchanged s t := by
    intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have bounds := stack_bounds pre.stack
  have stackNat : (stackPtr call).toNat = (stackPtr initial).toNat - 688 := by
    rw [callFrame.rsp]
    exact stack_sub_toNat pre.stack (offset := 688) (by decide)
  have stackRegion : Stack.region call 0 =
      MemoryRegion.mk ((stackPtr initial).toNat - 688) 8 := by
    change MemoryRegion.mk (stackPtr call).toNat
      ((stackPtr call).toNat + 8 - (stackPtr call).toNat) = _
    rw [Nat.add_sub_cancel_left, stackNat]
  have copyWrites : MemoryWriteFrame s t #v[
      MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat count,
      MemoryRegion.mk ((stackPtr initial).toNat - 688) 8] := by
    apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame ?_) ?_
    · intro c member a covered
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact covered.elim
      · obtain ⟨i, hi, rfl⟩ := covered
        refine ⟨MemoryRegion.mk ((stackPtr initial).toNat - 688) 8, by simp, ?_⟩
        rw [ScalarFrame.scalar_call_address frame]
        have base := stack_sub_toNat pre.stack (show 688 ≤ 1856 by omega)
        rw [toNat_add_ofNat _ _ (by rw [base]; omega), base]
        change (stackPtr initial).toNat - 688 ≤ _ ∧
          _ < (stackPtr initial).toNat - 688 + 8
        constructor <;> omega
      · exact covered.elim
    · simpa only [stackRegion, registerRegion, destinationCall] using result.frame
  obtain ⟨fuel, copyRun⟩ := result.execution
  refine ⟨t, frameT, ⟨1 + fuel, run.trans copyRun⟩,
    result.rip.trans (callEffect_stack effect).1, calleeSaved,
    memoryWriteFrame_trans callMemory copyMemory, copyWrites, ?_⟩
  intro i hi
  have byte := copied i hi
  rw [destinationCall, sourceCall] at byte
  rcases access with zero | ⟨inputBytes, seed, span⟩
  · omega
  · have callByte := seed_bytes callFrame seed (sourceOffset + i) (by omega)
    have oldByte := seed_bytes frame seed (sourceOffset + i) (by omega)
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at byte ⊢
    exact byte.trans (callByte.trans oldByte.symm)

end P256.Proofs.Nonce.Update.Seeded.Absorb
