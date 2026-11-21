import AesGcm.Proofs.Machine.GHASHUpdate.BatchExec
import AesGcm.Proofs.Machine.GHASHUpdate.LoopMemory

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 1600000 in
theorem driver_batch_loop (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) (n : Nat) (hn : 0 < n)
    (args : Values Value Reg.count) (mem : Ram) (sp src ptr dst low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[6].get 64 = src)
    (hptr : args[12].get 64 = ptr) (hcount : args[5].get 64 = BitVec.ofNat 64 (64*n))
    (hdst : memLoad mem ptr 64 = dst) (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 312) 312)
    (hroom : low.toNat + 312 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem src (64*n)) (hp : Readable mem ptr 8)
    (hsrcsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span src (64*n)))
    (hptrsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span ptr 8))
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32))
    (hinput : (span dst 32).Disjoint (span src (64*n)))
    (hptrState : (span dst 32).Disjoint (span ptr 8)) :
    ∃ outArgs : Values Value Reg.count, ∃ outMem : Ram,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨.l1099c0, args, mem⟩, []⟩ ⟨⟨.l1099d5, outArgs, outMem⟩, []⟩ ∧
      outArgs[4] = ⟨64, sp⟩ ∧ outArgs[6] = ⟨64, src + BitVec.ofNat 64 (64*n)⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 12, 13, 14, 22, 39, 50, 51] → outArgs[r] = args[r]) ∧
      GPRsTyped outArgs ∧
      RamWriteFrame mem outMem [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := updateBlocks mem src (4*n)
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
          (memLoad mem (dst + 16) 64, memLoad mem (dst + 24) 64)
       memLoad outMem (dst + 16) 64 = result.1 ∧ memLoad outMem (dst + 24) 64 = result.2) := by
  induction n generalizing args mem src with
  | zero => omega
  | succ n ih =>
    have hlow := hr.low
    have hsrc64 : (src + 64).toNat = src.toNat + 64 := by
      simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    have firstRead : Readable mem src 64 := hr.sub (Nat.le_refl _) (by omega)
    have firstSep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span src 64) := by
      intro x hx hy
      apply hsrcsep x hx
      simp only [MemoryRegion.Contains, span] at hy ⊢
      omega
    obtain ⟨o, callReach, osp, o15, keep, otypes, frame, post⟩ :=
      driver_batch_exec code hcode hmultiply args mem sp src ptr dst low
        hsp hsrc hptr hdst htypes h39 h50 h51 hdf hstack hroom halign firstRead hp
        firstSep hptrsep hw hsep
    have o5 : o.values[5].get 64 = BitVec.ofNat 64 (64*(n+1)) := by
      have e : o.values[5] = args[5] := keep 5 (by decide); rw [e]; exact hcount
    obtain ⟨a, branch, a5, a6, akeep, atypes⟩ :=
      driver_batch_return_runBlock code o.values o.store (BitVec.ofNat 64 (64*(n+1)))
        (src + 64) o5 (by rw [o15]; rfl) otypes
    have subCount : BitVec.ofNat 64 (64*(n+1)) - 64 = BitVec.ofNat 64 (64*n) := by
      rw [Nat.mul_add, BitVec.ofNat_add]
      simp only [Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_sub_cancel]
    rw [subCount] at branch a5
    have a4 : a[4] = ⟨64, sp⟩ := (akeep 4 (by decide)).trans osp
    have preserved (r : Fin 53) (hr : r.val ∈ [3, 12, 13, 14, 22, 39, 50, 51]) : a[r] = args[r] := by
      apply (akeep r ?_).trans (keep r ?_)
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    by_cases hz : n = 0
    · subst n
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, ↓reduceIte] at branch
      have step : LIR.program.step (dialect code) ⟨⟨.l1099cc, o.values, o.store⟩, []⟩ =
          .next ⟨⟨.l1099d5, a, o.store⟩, []⟩ := by rw [Program.step, branch]; rfl
      exact ⟨a, o.store, callReach.trans (.single step), a4,
        by simpa only [Nat.zero_add, Nat.mul_one, BitVec.ofNat_eq_ofNat] using a6,
        preserved, atypes, frame, post⟩
    · have hn' : 0 < n := by omega
      have countNe : BitVec.ofNat 64 (64*n) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        change (64*n) % 2^64 = 0 at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [ite_eq_right countNe] at branch
      have step : LIR.program.step (dialect code) ⟨⟨.l1099cc, o.values, o.store⟩, []⟩ =
          .next ⟨⟨.l1099c0, a, o.store⟩, []⟩ := by rw [Program.step, branch]; rfl
      have hkeyOutside := stateKey_outside ⟨low.toNat, sp.toNat - low.toNat⟩ dst
        (by change 0 < sp.toNat - low.toNat; omega) hw.readable.low hsep
      have hptrOutside := input_outside ⟨low.toNat, sp.toNat - low.toNat⟩ dst ptr 8
        (by change 0 < sp.toNat - low.toNat; omega) (by decide) hw.readable.low hp.low hptrsep hptrState
      have hsourceOutside := input_outside ⟨low.toNat, sp.toNat - low.toNat⟩ dst src (64*(n+1))
        (by change 0 < sp.toNat - low.toNat; omega) (by omega) hw.readable.low hr.low hsrcsep hinput
      have key0 : memLoad o.store dst 64 = memLoad mem dst 64 := by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          (frame.memLoad_eq (outside_add_offset hkeyOutside (off := 0) (n := 8) (by decide) (by decide)) :
            memLoad o.store (dst + BitVec.ofNat 64 0) 64 = memLoad mem (dst + BitVec.ofNat 64 0) 64)
      have key8 : memLoad o.store (dst + 8) 64 = memLoad mem (dst + 8) 64 :=
        frame.memLoad_eq (outside_add_offset hkeyOutside (off := 8) (by decide) (by decide))
      have ptrLoad : memLoad o.store ptr 64 = dst := (frame.memLoad_eq hptrOutside).trans hdst
      have nextRead : Readable o.store (src + 64) (64*n) := by
        apply (hr.of_frame frame).sub <;> rw [hsrc64] <;> omega
      have nextSep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span (src + 64) (64*n)) := by
        intro x hx hy
        apply hsrcsep x hx
        simp only [MemoryRegion.Contains, span, hsrc64] at hy ⊢
        omega
      have nextInput : (span dst 32).Disjoint (span (src + 64) (64*n)) := by
        intro x hx hy
        apply hinput x hx
        simp only [MemoryRegion.Contains, span, hsrc64] at hy ⊢
        omega
      obtain ⟨b, out, reach, b4, b6, bkeep, btypes, frame', post'⟩ :=
        ih hn' a o.store (src + 64)
          (by rw [a4]; rfl) (by rw [a6]; rfl)
          (by have e : a[12] = args[12] := preserved 12 (by decide); rw [e]; exact hptr) (by rw [a5]; rfl)
          ptrLoad atypes
          (by have e : a[39] = args[39] := preserved 39 (by decide); rw [e]; exact h39)
          (by have e : a[50] = args[50] := preserved 50 (by decide); rw [e]; exact h50)
          (by have e : a[51] = args[51] := preserved 51 (by decide); rw [e]; exact h51)
          ((preserved 22 (by decide)).trans hdf)
          (hstack.of_frame frame) nextRead (hp.of_frame frame) nextSep (hw.of_frame frame) nextInput
      refine ⟨b, out, (callReach.trans (.single step)).trans reach, b4, ?_, ?_, btypes,
        frame.trans frame' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩), ?_⟩
      · rw [b6]
        congr 1
        rw [Nat.mul_add, BitVec.ofNat_add]
        simp only [Nat.mul_one, BitVec.ofNat_eq_ofNat]
        ac_rfl
      · intro r hr
        exact (bkeep r hr).trans (preserved r hr)
      · have remainingOutside : Outside [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16]
            (src + 64) (16*(4*n)) := by
          simpa only [BitVec.ofNat_eq_ofNat] using
            outside_add_offset hsourceOutside (off := 64) (n := 16*(4*n)) (by omega) (by omega)
        dsimp only at post post' ⊢
        rw [key0, key8, post.1, post.2] at post'
        rw [updateBlocks_of_frame frame (src + 64) (4*n) remainingOutside] at post'
        rw [show 4*(n+1) = 4+4*n by omega, updateBlocks_append]
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using post'

end AesGcm.Proofs.Machine.GHASHUpdate
