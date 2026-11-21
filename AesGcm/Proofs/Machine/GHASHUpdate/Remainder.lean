import AesGcm.Proofs.Machine.GHASHUpdate.TailLoop
import AesGcm.Proofs.Machine.GHASHUpdate.Counts

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 1000000 in
theorem driver_remainder (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) (args : Values Value Reg.count) (mem : Ram)
    (sp src dst low count : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[3].get 64 = src)
    (hdst : args[14].get 64 = dst) (hcount : args[13].get 64 = count <<< 4)
    (hreadCount : Readable mem (sp + 24) 8) (hloadCount : memLoad mem (sp + 24) 64 = count)
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 136) 160)
    (hroom : low.toNat + 136 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem src (16*count.toNat))
    (hsrcsep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint (span src (16*count.toNat)))
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32))
    (hinput : (span dst 32).Disjoint (span src (16*count.toNat))) :
    ∃ outArgs : Values Value Reg.count, ∃ outMem : Ram,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨.l1099d5, args, mem⟩, []⟩ ⟨⟨.l109aaa, outArgs, outMem⟩, []⟩ ∧
      outArgs[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [14, 22, 39, 50, 51] → outArgs[r] = args[r]) ∧
      GPRsTyped outArgs ∧
      RamWriteFrame mem outMem [⟨low.toNat, sp.toNat + 24 - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := updateBlocks mem (src + BitVec.ofNat 64 (64*(count.toNat/4))) (count.toNat%4)
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
          (memLoad mem (dst + 16) 64, memLoad mem (dst + 24) 64)
       memLoad outMem (dst + 16) 64 = result.1 ∧ memLoad outMem (dst + 24) 64 = result.2) := by
  have hlow := hr.low
  have countBound : 16*count.toNat ≤ 2^32 := by omega
  have mask : (count <<< 4) &&& 0x30 = BitVec.ofNat 64 (16*(count.toNat%4)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat]
    rw [tail_count_mask count countBound, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have offsetEq : (count &&& 0x7fffffffffffffc) <<< 4 = BitVec.ofNat 64 (64*(count.toNat/4)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat]
    rw [tail_count_offset count countBound, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  obtain ⟨a, dispatch, a13, akeep, atypes⟩ :=
    driver_tail_dispatch_runBlock code args mem (count <<< 4) hcount htypes
  rw [mask] at dispatch a13
  have a4 : a[4] = args[4] := akeep 4 (by decide)
  have a3 : a[3] = args[3] := akeep 3 (by decide)
  by_cases hz : count.toNat%4 = 0
  · simp only [hz, Nat.mul_zero, BitVec.ofNat_eq_ofNat, ↓reduceIte] at dispatch
    have step : LIR.program.step (dialect code) ⟨⟨.l1099d5, args, mem⟩, []⟩ =
        .next ⟨⟨.l109aaa, a, mem⟩, []⟩ := by rw [Program.step, dispatch]; rfl
    refine ⟨a, mem, .single step, ?_, ?_, atypes, .refl _ _, ?_⟩
    · rw [a4, ← hsp]
      exact htypes.value ⟨4, by decide⟩
    · intro r hr
      apply akeep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    · simp only [hz, updateBlocks_zero, and_self]
  · have hn : 0 < count.toNat%4 := by omega
    have hmask : BitVec.ofNat 64 (16*(count.toNat%4)) ≠ 0 := by
      intro h
      have he := congrArg BitVec.toNat h
      change (16*(count.toNat%4)) % 2^64 = 0 at he
      rw [Nat.mod_eq_of_lt (by omega)] at he
      omega
    rw [ite_eq_right hmask] at dispatch
    have first : LIR.program.step (dialect code) ⟨⟨.l1099d5, args, mem⟩, []⟩ =
        .next ⟨⟨.l1099df, a, mem⟩, []⟩ := by rw [Program.step, dispatch]; rfl
    obtain ⟨b, prepare, b3, b12, b15, bkeep, btypes⟩ :=
      driver_tail_prepare_runBlock code a mem sp src
        (by rw [a4]; exact hsp) (by rw [a3]; exact hsrc) atypes hreadCount
    rw [hloadCount, offsetEq] at b3
    have second : LIR.program.step (dialect code) ⟨⟨.l1099df, a, mem⟩, []⟩ =
        .next ⟨⟨.l109a00, b, mem⟩, []⟩ := by rw [Program.step, prepare]; rfl
    have b4 : b[4] = args[4] := (bkeep 4 (by decide)).trans a4
    have b13 : b[13] = ⟨64, BitVec.ofNat 64 (16*(count.toNat%4))⟩ := (bkeep 13 (by decide)).trans a13
    have keep (r : Fin 53) (hr : r.val ∈ [14, 22, 39, 50, 51]) : b[r] = args[r] := by
      apply (bkeep r ?_).trans (akeep r ?_)
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    have tailNat : (src + BitVec.ofNat 64 (64*(count.toNat/4))).toNat =
        src.toNat + 64*(count.toNat/4) := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := 64*(count.toNat/4)) (by omega), Nat.mod_eq_of_lt (by omega)]
    have tailRead : Readable mem (src + BitVec.ofNat 64 (64*(count.toNat/4)) + 0) (16*(count.toNat%4)) := by
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      apply hr.sub <;> rw [tailNat] <;> omega
    have tailSep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint
        (span (src + BitVec.ofNat 64 (64*(count.toNat/4)) + 0) (16*(count.toNat%4))) := by
      intro x hx hy
      apply hsrcsep x hx
      simp only [MemoryRegion.Contains, span, BitVec.ofNat_eq_ofNat, BitVec.add_zero, tailNat] at hy ⊢
      omega
    have tailInput : (span dst 32).Disjoint
        (span (src + BitVec.ofNat 64 (64*(count.toNat/4)) + 0) (16*(count.toNat%4))) := by
      intro x hx hy
      apply hinput x hx
      simp only [MemoryRegion.Contains, span, BitVec.ofNat_eq_ofNat, BitVec.add_zero, tailNat] at hy ⊢
      omega
    obtain ⟨out, outMem, reach, out4, outKeep, outTypes, frame, post⟩ :=
      driver_tail_loop code hcode hmultiply (count.toNat%4) hn b mem sp
        (src + BitVec.ofNat 64 (64*(count.toNat/4))) 0 dst low
        (by rw [b4]; exact hsp) (by rw [b3]; rfl) (by rw [b12]; rfl)
        (by have e : b[14] = args[14] := keep 14 (by decide); rw [e]; exact hdst)
        (by rw [b15]; rfl) (by rw [b13]; simp only [Value.get, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, BitVec.zero_add]) btypes
        (by have e : b[39] = args[39] := keep 39 (by decide); rw [e]; exact h39)
        (by have e : b[50] = args[50] := keep 50 (by decide); rw [e]; exact h50)
        (by have e : b[51] = args[51] := keep 51 (by decide); rw [e]; exact h51)
        ((keep 22 (by decide)).trans hdf) hstack hroom halign tailRead tailSep hw hsep tailInput
    refine ⟨out, outMem, ((Semantics.Reaches.single first).trans (.single second)).trans reach,
      out4, ?_, outTypes, frame, ?_⟩
    · intro r hr
      apply (outKeep r ?_).trans (keep r hr)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using post

end AesGcm.Proofs.Machine.GHASHUpdate
