import AesGcm.Proofs.Machine.GHASHUpdate.BatchLoop

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 800000 in
theorem driver_batches (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) (n : Nat)
    (args : Values Value Reg.count) (mem : Ram) (sp src dst low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[3].get 64 = src)
    (hcount : args[5].get 64 = BitVec.ofNat 64 (64*n))
    (hdst : memLoad mem (sp + 32) 64 = dst) (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 312) 312)
    (hroom : low.toNat + 312 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem src (64*n)) (hp : Readable mem (sp + 32) 8)
    (hsrcsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span src (64*n)))
    (hptrsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span (sp + 32) 8))
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32))
    (hinput : (span dst 32).Disjoint (span src (64*n)))
    (hptrState : (span dst 32).Disjoint (span (sp + 32) 8)) :
    ∃ outArgs : Values Value Reg.count, ∃ outMem : Ram,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if n = 0 then .l1099d5 else .l1099b4, args, mem⟩, []⟩
        ⟨⟨.l1099d5, outArgs, outMem⟩, []⟩ ∧
      outArgs[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 13, 14, 22, 39, 50, 51] → outArgs[r] = args[r]) ∧
      GPRsTyped outArgs ∧
      RamWriteFrame mem outMem [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := updateBlocks mem src (4*n)
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
          (memLoad mem (dst + 16) 64, memLoad mem (dst + 24) 64)
       memLoad outMem (dst + 16) 64 = result.1 ∧ memLoad outMem (dst + 24) 64 = result.2) := by
  by_cases hz : n = 0
  · subst n
    refine ⟨args, mem, ?_, ?_, fun _ _ => rfl, htypes, .refl _ _, ?_⟩
    · exact .refl _
    · rw [← hsp]
      exact htypes.value ⟨4, by decide⟩
    · simp only [Nat.mul_zero, updateBlocks_zero, and_self]
  · rw [ite_eq_right hz]
    obtain ⟨a, prepare, a12, a6, keep, atypes⟩ :=
      driver_batch_prepare_runBlock code args mem sp src hsp hsrc htypes
    have a4 : a[4] = args[4] := keep 4 (by decide)
    have a5 : a[5] = args[5] := keep 5 (by decide)
    have a39 : a[39] = args[39] := keep 39 (by decide)
    have a50 : a[50] = args[50] := keep 50 (by decide)
    have a51 : a[51] = args[51] := keep 51 (by decide)
    obtain ⟨out, outMem, reach, out4, -, outKeep, outTypes, frame, post⟩ :=
      driver_batch_loop code hcode hmultiply n (by omega) a mem sp src (sp + 32) dst low
        (by rw [a4]; exact hsp) (by rw [a6]; rfl) (by rw [a12]; rfl)
        (by rw [a5]; exact hcount) hdst atypes
        (by rw [a39]; exact h39) (by rw [a50]; exact h50) (by rw [a51]; exact h51)
        ((keep 22 (by decide)).trans hdf) hstack hroom halign hr hp hsrcsep hptrsep hw hsep hinput hptrState
    have step : LIR.program.step (dialect code) ⟨⟨.l1099b4, args, mem⟩, []⟩ =
        .next ⟨⟨.l1099c0, a, mem⟩, []⟩ := by rw [Program.step, prepare]; rfl
    refine ⟨out, outMem, (Semantics.Reaches.single step).trans reach, out4, ?_, outTypes, frame, post⟩
    intro r hr
    apply (outKeep r ?_).trans (keep r ?_)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega

end AesGcm.Proofs.Machine.GHASHUpdate
