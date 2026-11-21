import Hkdf.Proofs.Key.Hash.Prepare
import Hkdf.Proofs.Key.Hash.Compress
import Hkdf.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

set_option maxHeartbeats 800000 in
theorem compress_full_blocks [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (state : InitialBlocks initial boundary key s) :
    ∃ t, Working initial boundary t ∧ t.RIP = 0x116413 ∧
      HashStateAt t (blockAddress initial + 296)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash key) ∧
      t.regValue .r14 = s.regValue .r14 ∧ t.regValue .r15 = s.regValue .r15 ∧
      memLoad t.external (blockAddress initial + 328) 64 =
        BitVec.ofNat 64 (key.size / 64) := by
  have output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 80 := by
    rw [state.hashPointer]
    simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have words : HashStateAt s (s.regValue .rdi) Hkdf.Proofs.NIST.SHA256.initialHash := by
    rw [state.hashPointer]
    exact state.hashWords
  obtain ⟨t, working, rip, hashWords, abi, frame⟩ := compression_call ctx state.toWorking
    (input := fullBlocks key) 0x1640e 0xffff31ad 80
    (by decide) (by decide) (by decide +kernel) state.rip output
    (by decide) (by decide) (by decide) words state.countRegister (by
      intro u runningU call ret
      have push : pushAddr s = stackPtr initial - 384 := by
        change stackPtr s - 8 = _
        rw [state.rsp]
        simp only [blockAddress, BitVec.sub_sub]
        rfl
      have rspU : stackPtr u = stackPtr initial - 384 := call.writes.1.trans push
      have outputU : u.regValue .rdi = stackPtr initial - 80 := by
        have kept : u.regValue .rdi = s.regValue .rdi :=
          call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])
        rw [kept, state.hashPointer]
        simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd]
      have inputU : u.regValue .rsi = initial.regValue .rsi :=
        (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans state.inputPointer
      let layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 720 0 32 336 :=
        ⟨384, 0, 80, by decide, by decide, by decide, by decide, by decide, by decide,
          .inr (by decide)⟩
      have inputWithin (a : Nat) (h : (registerRegion u .rsi (64 * (key.size / 64))).Contains a) :
          (registerRegion initial .rsi key.size).Contains a := by
        change (u.regValue .rsi).toNat ≤ a ∧ a < (u.regValue .rsi).toNat + 64 * (key.size / 64) at h
        change (initial.regValue .rsi).toNat ≤ a ∧ a < (initial.regValue .rsi).toNat + key.size
        rw [inputU] at h
        constructor <;> omega
      have pre := callee_pre_of_stack_output ctx.stride ctx.stack
        (ctx.avoids (Stack.region initial stackBytes) (by simp)) ctx.outerBoundary
        runningU.machine runningU.directionFlag runningU.loaded runningU.allocated layout
        call.rip rspU outputU
        (by rw [ret]; exact inProgram_of_textOffset 0x16413 (by decide))
        (by
          change (u.regValue .rsi).toNat + 64 * (key.size / 64) < 2^32
          rw [inputU]
          have h := ctx.inputBounded
          change (initial.regValue .rsi).toNat + key.size < 2^32 at h
          omega)
        (by
          intro a ha
          exact Option.isSome_iff_exists.mp (runningU.allocated a
            (Option.isSome_iff_exists.mpr (ctx.inputAllocated a (inputWithin a.toNat ha)))))
        (by
          intro a ha hb
          exact ctx.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) a (inputWithin a ha) hb)
      have originalBytes : (registerRegion initial .rsi key.size).HasBytes u.external key := by
        apply frame_hasBytes runningU.frame ?_ (by have := ctx.inputBounded; change _ < 2^32 at this; omega) ctx.bytes
        intro region member
        have cases : region = registerRegion initial .rdi 64 ∨ region = Stack.region initial stackBytes := by
          simpa [writeRegions] using member
        rcases cases with rfl | rfl
        · exact ctx.separation ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
        · exact ctx.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
      have inputBytes : (registerRegion u .rsi (64 * (key.size / 64))).HasBytes u.external (fullBlocks key) := by
        rw [registerRegion, inputU]
        exact Hkdf.Proofs.Common.Memory.hasBytes_prefix originalBytes (by change 64 * (key.size / 64) ≤ key.size; omega)
      exact ⟨pre, inputBytes⟩)
  refine ⟨t, working, rip, ?_, abi.1 .r14 (by simp), abi.1 .r15 (by simp), ?_⟩
  · rw [state.hashPointer, compressBlocks_fullBlocks] at hashWords
    exact hashWords
  · have bounds := stack_bounds ctx.toCalleePre
    change 720 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at bounds
    have countNat : (stackPtr initial - BitVec.ofNat 64 48).toNat =
        (stackPtr initial).toNat - 48 := stack_sub_toNat ctx.toCalleePre (by decide)
    have outputNat : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 80 := by
      rw [output]
      exact stack_sub_toNat ctx.toCalleePre (by decide)
    have stackNat : (stackPtr initial - BitVec.ofNat 64 720).toNat =
        (stackPtr initial).toNat - 720 := stack_sub_toNat ctx.toCalleePre (by decide)
    have same := frame_agrees_of_disjoint frame
      (address := stackPtr initial - BitVec.ofNat 64 48) (size := 8)
      (by rw [countNat]; omega) (by
        intro region member
        have cases : region = registerRegion s .rdi 32 ∨
            region = (⟨(stackPtr initial - 720).toNat, 344⟩ : MemoryRegion) := by
          simpa using member
        rcases cases with rfl | rfl
        · intro a left right
          change (stackPtr initial - BitVec.ofNat 64 48).toNat ≤ a ∧
            a < (stackPtr initial - BitVec.ofNat 64 48).toNat + 8 at left
          change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 32 at right
          rw [countNat] at left
          rw [outputNat] at right
          omega
        · intro a left right
          change (stackPtr initial - BitVec.ofNat 64 48).toNat ≤ a ∧
            a < (stackPtr initial - BitVec.ofNat 64 48).toNat + 8 at left
          change (stackPtr initial - BitVec.ofNat 64 720).toNat ≤ a ∧
            a < (stackPtr initial - BitVec.ofNat 64 720).toNat + 344 at right
          rw [countNat] at left
          rw [stackNat] at right
          omega)
    have original : memLoad s.external (stackPtr initial - BitVec.ofNat 64 48) 64 =
        BitVec.ofNat 64 (key.size / 64) := by
      simpa only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using state.blocks
    have count := (agrees_memLoad (width := 64) same).trans original
    simpa only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using count

end Hkdf.Proofs.Key.Hash
