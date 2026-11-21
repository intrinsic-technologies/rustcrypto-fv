import AesGcm.Proofs.Machine.GHASHUpdate.Tail
import AesGcm.Proofs.Machine.GHASHUpdate.OneBlock
import AesGcm.Proofs.Machine.GHASHUpdate.Blocks
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 1000000 in
theorem driver_tail_exec (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) (args : Values Value Reg.count) (mem : Ram)
    (sp src offset dst low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[3].get 64 = src)
    (hoff : args[12].get 64 = offset) (hdst : args[14].get 64 = dst)
    (hscratch : args[15].get 64 = sp + 8) (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 136) 160)
    (hroom : low.toNat + 136 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem (src + offset) 16) (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat + 24 - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32)) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨.l109a00, args, mem⟩, []⟩ ⟨⟨.l109a9d, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values ∧
      RamWriteFrame mem o.store [⟨low.toNat, sp.toNat + 24 - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := updateBlocks mem (src + offset) 1
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
          (memLoad mem (dst + 16) 64, memLoad mem (dst + 24) 64)
       memLoad o.store (dst + 16) 64 = result.1 ∧ memLoad o.store (dst + 24) 64 = result.2) := by
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by
    have hle : (8 : BitVec 64) ≤ sp := by change 8 ≤ sp.toNat; omega
    simpa using BitVec.toNat_sub_of_le hle
  have hsub136 : (sp - 136).toNat = sp.toNat - 136 := by
    have hle : (136 : BitVec 64) ≤ sp := by change 136 ≤ sp.toNat; omega
    simpa using BitVec.toNat_sub_of_le hle
  have hspLow : sp.toNat + 24 ≤ 2^32 := by have := hstack.readable.low; rw [hsub136] at this; omega
  have hsadd : (sp + 8).toNat = sp.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  have dstBounds := disjoint_bounds low.toNat (sp.toNat + 24 - low.toNat)
    dst.toNat 32 (by omega) (by decide) hsep
  obtain ⟨a, prepared, hcall, asp, asrc, adst, keep, aTypes, frame, ret, words⟩ :=
    driver_tail_call_runBlock code hcode args mem sp src offset dst hsp hsrc hoff hdst hscratch
      htypes hr (hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) (by omega)
  have outside : Outside [span (sp - 8) 32] dst 32 := by
    refine ⟨by have := hw.readable.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hsub]
    omega
  have load (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad prepared (dst + BitVec.ofNat 64 off) 64 =
        memLoad mem (dst + BitVec.ofNat 64 off) 64 :=
    frame.memLoad_eq (outside_add_offset outside (by decide) ho)
  have l0 : memLoad prepared dst 64 = memLoad mem dst 64 := by simpa using load 0 (by decide)
  have l8 := load 8 (by decide)
  have l16 := load 16 (by decide)
  have l24 := load 24 (by decide)
  have aspGet : a[4].get 64 = sp - 8 := by rw [asp]; rfl
  have asrcGet : a[6].get 64 = sp + 8 := by rw [asrc]; rfl
  have adstGet : a[7].get 64 = dst := by rw [adst]; rfl
  have a39 : a[39] = args[39] := keep 39 (by decide)
  have a50 : a[50] = args[50] := keep 50 (by decide)
  have a51 : a[51] = args[51] := keep 51 (by decide)
  have a22 : a[22] = args[22] := keep 22 (by decide)
  have childSep : (⟨low.toNat, (sp - 8).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
      (span dst 32) := by
    intro x hx hy
    apply hsep x ?_ hy
    simp only [MemoryRegion.Contains, hsub] at hx ⊢
    omega
  obtain ⟨o, hexec, htag, hdone, outTypes, outFrame, post⟩ :=
    callContract_exec_values LIR.lifted code .l1034c0 LIR.Fn1034c0.frameInfo
      (fun fr => [span (fr.rdi + 16) 16]) _ _ (oneBlock_call code hmultiply)
      prepared a 0x109a9d low aTypes
      (by rw [a39]; exact h39) (by rw [a50]; exact h50) (by rw [a51]; exact h51)
      (a22.trans hdf)
      (by rw [aspGet]; exact (hstack.readable.of_frame frame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [aspGet]; exact ret) (by decide)
      (fun _ => by
        change Writable code prepared (a[4].get 64 - 128) 128
        rw [aspGet, show sp - 8 - 128 = sp - 136 by bv_omega]
        exact (hstack.of_frame frame).sub (Nat.le_refl _) (by omega))
      (by change low.toNat + 128 ≤ (a[4].get 64).toNat; rw [aspGet, hsub]; omega)
      (by rw [aspGet, hsub]; omega) (by trivial)
      (by
        change Readable prepared (a[6].get 64) 16 ∧ Writable code prepared (a[7].get 64) 32 ∧ _
        refine ⟨?_, ?_, ?_⟩
        · rw [asrcGet]
          exact (hstack.readable.of_frame frame).of_offsets rfl (addr_sub _ _) (by decide)
        · rw [adstGet]; exact hw.of_frame frame
        · simpa only [activationOfValues, callStack, aspGet, adstGet] using childSep)
  change o.values[4] = ⟨64, a[4].get 64 + 8⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
    o.values[3] = ⟨64, a[3].get 64⟩ ∧ o.values[5] = ⟨64, a[5].get 64⟩ ∧
    o.values[12] = ⟨64, a[12].get 64⟩ ∧ o.values[13] = ⟨64, a[13].get 64⟩ ∧
    o.values[14] = ⟨64, a[14].get 64⟩ ∧ o.values[15] = ⟨64, a[15].get 64⟩ ∧
    o.values[39] = ⟨32, a[39].get 32⟩ ∧ o.values[50] = ⟨16, a[50].get 16⟩ ∧
    o.values[51] = ⟨16, a[51].get 16⟩ ∧ True at hdone
  rcases hdone with ⟨o4, o22, o3, o5, o12, o13, o14, o15, o39, o50, o51, -⟩
  have accepted : driverTailFrame.Accepts (dialect code) o.tag = true := by rw [htag]; rfl
  have resume := CFGCall.exec_reaches_resume hexec driverTailFrame [] accepted
  have step : LIR.program.step (dialect code) ⟨⟨.l109a00, args, mem⟩, []⟩ =
      .next ⟨⟨.l1034c0, a, prepared⟩, [driverTailFrame]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨o, (Semantics.Reaches.single step).trans resume, ?_, ?_, outTypes, ?_, ?_⟩
  · simpa only [aspGet, BitVec.sub_add_cancel] using o4
  · rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (o3.trans (aTypes.value ⟨3, by decide⟩).symm).trans (keep 3 (by decide))
    · exact (o5.trans (aTypes.value ⟨5, by decide⟩).symm).trans (keep 5 (by decide))
    · exact (o12.trans (aTypes.value ⟨12, by decide⟩).symm).trans (keep 12 (by decide))
    · exact (o13.trans (aTypes.value ⟨13, by decide⟩).symm).trans (keep 13 (by decide))
    · exact (o14.trans (aTypes.value ⟨14, by decide⟩).symm).trans (keep 14 (by decide))
    · exact (o15.trans (aTypes.value ⟨15, by decide⟩).symm).trans (keep 15 (by decide))
    · exact o22.trans hdf.symm
    · exact (o39.trans (show ⟨32, a[39].get 32⟩ = args[39] by rw [a39]; exact h39.symm))
    · exact (o50.trans (show ⟨16, a[50].get 16⟩ = args[50] by rw [a50]; exact h50.symm))
    · exact (o51.trans (show ⟨16, a[51].get 16⟩ = args[51] by rw [a51]; exact h51.symm))
  · have nativeFrame : RamWriteFrame mem prepared
        [⟨low.toNat, sp.toNat + 24 - low.toNat⟩, span (dst + 16) 16] := by
      apply (RamWriteFrame.refl _ _).trans frame
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      refine ⟨⟨low.toNat, sp.toNat + 24 - low.toNat⟩, by simp, ?_, ?_⟩ <;>
        simp only [span, hsub] <;> omega
    change RamWriteFrame prepared o.store
      [⟨low.toNat, (a[4].get 64).toNat - low.toNat⟩, span (a[7].get 64 + 16) 16] at outFrame
    rw [aspGet, adstGet] at outFrame
    apply nativeFrame.trans outFrame
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨⟨low.toNat, sp.toNat + 24 - low.toNat⟩, by simp, Nat.le_refl _, ?_⟩
      simp only [hsub]
      omega
    · exact ⟨span (dst + 16) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  · simp only [activationOfValues, adstGet, asrcGet] at post
    simp only [BitVec.ofNat_eq_ofNat] at l8 l16 l24 words post
    rw [show sp + 8#64 + 8#64 = sp + 16#64 by bv_omega, words.1, words.2, l0, l8, l16, l24] at post
    simpa only [updateBlocks_succ, updateBlocks_zero, Nat.mul_zero, Nat.zero_add,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.xor_comm] using post

end AesGcm.Proofs.Machine.GHASHUpdate
