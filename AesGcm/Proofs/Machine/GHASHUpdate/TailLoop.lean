import AesGcm.Proofs.Machine.GHASHUpdate.TailExec
import AesGcm.Proofs.Machine.GHASHUpdate.Loop
import AesGcm.Proofs.Machine.GHASHUpdate.LoopMemory

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 1600000 in
theorem driver_tail_loop (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) (n : Nat) (hn : 0 < n)
    (args : Values Value Reg.count) (mem : Ram) (sp src offset dst low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[3].get 64 = src)
    (hoff : args[12].get 64 = offset) (hdst : args[14].get 64 = dst)
    (hscratch : args[15].get 64 = sp + 8)
    (hcount : args[13].get 64 = offset + BitVec.ofNat 64 (16*n))
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 136) 160)
    (hroom : low.toNat + 136 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem (src + offset) (16*n))
    (hsrcsep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint (span (src + offset) (16*n)))
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32))
    (hinput : (span dst 32).Disjoint (span (src + offset) (16*n))) :
    ∃ outArgs : Values Value Reg.count, ∃ outMem : Ram,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨.l109a00, args, mem⟩, []⟩ ⟨⟨.l109aaa, outArgs, outMem⟩, []⟩ ∧
      outArgs[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 13, 14, 15, 22, 39, 50, 51] → outArgs[r] = args[r]) ∧
      GPRsTyped outArgs ∧
      RamWriteFrame mem outMem [⟨low.toNat, sp.toNat + 24 - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := updateBlocks mem (src + offset) n
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
          (memLoad mem (dst + 16) 64, memLoad mem (dst + 24) 64)
       memLoad outMem (dst + 16) 64 = result.1 ∧ memLoad outMem (dst + 24) 64 = result.2) := by
  induction n generalizing args mem offset with
  | zero => omega
  | succ n ih =>
    have hlow := hr.low
    have hnext : src + (offset + 16) = src + offset + 16 := by bv_omega
    have hnextNat : (src + (offset + 16)).toNat = (src + offset).toNat + 16 := by
      rw [hnext]
      rw [BitVec.toNat_add]
      change ((src + offset).toNat + 16) % 2^64 = (src + offset).toNat + 16
      exact Nat.mod_eq_of_lt (by omega)
    have firstRead : Readable mem (src + offset) 16 := hr.sub (Nat.le_refl _) (by omega)
    obtain ⟨o, callReach, osp, keep, otypes, frame, post⟩ :=
      driver_tail_exec code hcode hmultiply args mem sp src offset dst low
        hsp hsrc hoff hdst hscratch htypes h39 h50 h51 hdf hstack hroom halign firstRead hw hsep
    obtain ⟨a, branch, a12, akeep, atypes⟩ :=
      driver_tail_return_runBlock code o.values o.store offset (offset + BitVec.ofNat 64 (16*(n+1)))
        (by have e : o.values[12] = args[12] := keep 12 (by decide); rw [e]; exact hoff)
        (by have e : o.values[13] = args[13] := keep 13 (by decide); rw [e]; exact hcount) otypes
    have subCount : offset + BitVec.ofNat 64 (16*(n+1)) - (offset + 16) = BitVec.ofNat 64 (16*n) := by
      rw [Nat.mul_add, BitVec.ofNat_add]
      simp only [Nat.mul_one, BitVec.ofNat_eq_ofNat]
      bv_omega
    rw [subCount] at branch
    have a4 : a[4] = ⟨64, sp⟩ := (akeep 4 (by decide)).trans osp
    have preserved (r : Fin 53) (hr : r.val ∈ [3, 5, 13, 14, 15, 22, 39, 50, 51]) : a[r] = args[r] := by
      apply (akeep r ?_).trans (keep r ?_)
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    by_cases hz : n = 0
    · subst n
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, ↓reduceIte] at branch
      have step : LIR.program.step (dialect code) ⟨⟨.l109a9d, o.values, o.store⟩, []⟩ =
          .next ⟨⟨.l109aaa, a, o.store⟩, []⟩ := by rw [Program.step, branch]; rfl
      exact ⟨a, o.store, callReach.trans (.single step), a4, preserved, atypes, frame, post⟩
    · have hn' : 0 < n := by omega
      have countNe : BitVec.ofNat 64 (16*n) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        change (16*n) % 2^64 = 0 at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [ite_eq_right countNe] at branch
      have step : LIR.program.step (dialect code) ⟨⟨.l109a9d, o.values, o.store⟩, []⟩ =
          .next ⟨⟨.l109a00, a, o.store⟩, []⟩ := by rw [Program.step, branch]; rfl
      have hkeyOutside := stateKey_outside ⟨low.toNat, sp.toNat + 24 - low.toNat⟩ dst
        (by change 0 < sp.toNat + 24 - low.toNat; omega) hw.readable.low hsep
      have hsourceOutside := input_outside ⟨low.toNat, sp.toNat + 24 - low.toNat⟩ dst (src + offset) (16*(n+1))
        (by change 0 < sp.toNat + 24 - low.toNat; omega) (by omega) hw.readable.low hr.low hsrcsep hinput
      have key0 : memLoad o.store dst 64 = memLoad mem dst 64 := by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          (frame.memLoad_eq (outside_add_offset hkeyOutside (off := 0) (n := 8) (by decide) (by decide)) :
            memLoad o.store (dst + BitVec.ofNat 64 0) 64 = memLoad mem (dst + BitVec.ofNat 64 0) 64)
      have key8 : memLoad o.store (dst + 8) 64 = memLoad mem (dst + 8) 64 :=
        frame.memLoad_eq (outside_add_offset hkeyOutside (off := 8) (by decide) (by decide))
      have nextRead : Readable o.store (src + (offset + 16)) (16*n) := by
        apply (hr.of_frame frame).sub <;> rw [hnextNat] <;> omega
      have nextSep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint
          (span (src + (offset + 16)) (16*n)) := by
        intro x hx hy
        apply hsrcsep x hx
        simp only [MemoryRegion.Contains, span, hnextNat] at hy ⊢
        omega
      have nextInput : (span dst 32).Disjoint (span (src + (offset + 16)) (16*n)) := by
        intro x hx hy
        apply hinput x hx
        simp only [MemoryRegion.Contains, span, hnextNat] at hy ⊢
        omega
      have countNext : a[13].get 64 = (offset + 16) + BitVec.ofNat 64 (16*n) := by
        have e : a[13] = args[13] := preserved 13 (by decide)
        rw [e, hcount, Nat.mul_add, BitVec.ofNat_add]
        simp only [Nat.mul_one, BitVec.ofNat_eq_ofNat]
        ac_rfl
      obtain ⟨b, out, reach, b4, bkeep, btypes, frame', post'⟩ :=
        ih hn' a o.store (offset + 16)
          (by rw [a4]; rfl) (by have e : a[3] = args[3] := preserved 3 (by decide); rw [e]; exact hsrc)
          (by rw [a12]; rfl) (by have e : a[14] = args[14] := preserved 14 (by decide); rw [e]; exact hdst)
          (by have e : a[15] = args[15] := preserved 15 (by decide); rw [e]; exact hscratch) countNext atypes
          (by have e : a[39] = args[39] := preserved 39 (by decide); rw [e]; exact h39)
          (by have e : a[50] = args[50] := preserved 50 (by decide); rw [e]; exact h50)
          (by have e : a[51] = args[51] := preserved 51 (by decide); rw [e]; exact h51)
          ((preserved 22 (by decide)).trans hdf)
          (hstack.of_frame frame) nextRead nextSep (hw.of_frame frame) nextInput
      refine ⟨b, out, (callReach.trans (.single step)).trans reach, b4, ?_, btypes,
        frame.trans frame' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩), ?_⟩
      · intro r hr
        exact (bkeep r hr).trans (preserved r hr)
      · have remainingOutside : Outside [⟨low.toNat, sp.toNat + 24 - low.toNat⟩, span (dst + 16) 16]
            (src + (offset + 16)) (16*n) := by
          simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
            outside_add_offset hsourceOutside (off := 16) (n := 16*n) (by omega) (by omega)
        dsimp only at post post' ⊢
        rw [key0, key8, post.1, post.2] at post'
        rw [updateBlocks_of_frame frame (src + (offset + 16)) n remainingOutside] at post'
        rw [show n+1 = 1+n by omega, updateBlocks_append]
        simpa only [Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using post'

end AesGcm.Proofs.Machine.GHASHUpdate
