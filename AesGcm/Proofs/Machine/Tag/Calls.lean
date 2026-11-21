import AesGcm.Proofs.Machine.Tag.Execution.Calls
import AesGcm.Proofs.Machine.Tag.Execution.CallSupport
import AesGcm.Proofs.Machine.GHASHUpdate.Main

namespace AesGcm.Proofs.Machine.Tag
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 1600000 in
theorem ciphertext_update_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (hmultiply : MultiplyContract code)
    (args : Values Value Reg.count) (mem : Ram) (sp src len low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[14].get 64 = src)
    (hlen : args[15].get 64 = len) (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 408) 520)
    (hroom : low.toNat + 408 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem src len.toNat)
    (hsep : (⟨low.toNat, sp.toNat + 112 - low.toNat⟩ : MemoryRegion).Disjoint
      (span src len.toNat)) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l101d5e else .l10193e, args, mem⟩, []⟩
        ⟨⟨if use256 then .l101d72 else .l101952, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values ∧
      RamWriteFrame mem o.store [⟨low.toNat, sp.toNat - low.toNat⟩, span (sp + 96) 16] ∧
      (let result := updateBlocks mem src (len.toNat / 16)
          (memLoad mem (sp + 80) 64) (memLoad mem (sp + 88) 64)
          (memLoad mem (sp + 96) 64, memLoad mem (sp + 104) 64)
       memLoad o.store (sp + 96) 64 = result.1 ∧
       memLoad o.store (sp + 104) 64 = result.2) := by
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by
    exact BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have hsub408 : (sp - 408).toNat = sp.toNat - 408 := by
    exact BitVec.toNat_sub_of_le (by change 408 ≤ sp.toNat; omega)
  have hspLow : sp.toNat + 112 ≤ 2^32 := by
    have := hstack.readable.low
    rw [hsub408] at this
    omega
  have hadd (off : Nat) (ho : off ≤ 112) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h80 : (sp + 80).toNat = sp.toNat + 80 := hadd 80 (by decide)
  obtain ⟨callee, continuation, run, label, target, guard, memory, csp, cdst, csrc,
      ccount, keep, types⟩ := Execution.ciphertext_runBlock use256 code hcode args mem
        (by rw [hsp]; exact hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
  let ret : BitVec 64 := if use256 then 0x101d72 else 0x101952
  let prepared := memStore mem (sp - 8) ret
  have cmem : callee.store = prepared := by simpa only [hsp] using memory
  have cspGet : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [csp, hsp]; rfl
  have cdstGet : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 80 := by rw [cdst, hsp]; rfl
  have csrcGet : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = src := by rw [csrc, hsrc]; rfl
  have countGet : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = len.toNat / 16 := by
    rw [ccount, hlen]
    change (len >>> 4).toNat = _
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have frame : RamWriteFrame mem prepared [span (sp - 8) 8] := by
    apply (RamWriteFrame.refl mem _).memStore
    refine ⟨span (sp - 8) 8, by simp, ?_⟩
    simp only [InRegion, span, hsub]
    omega
  have stateOutside : Outside [span (sp - 8) 8] (sp + 80) 32 := by
    refine ⟨by rw [h80]; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hsub, h80]
    omega
  have stateLoad (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad prepared (sp + 80 + BitVec.ofNat 64 off) 64 =
        memLoad mem (sp + 80 + BitVec.ofNat 64 off) 64 :=
    frame.memLoad_eq (GHASHUpdate.outside_add_offset stateOutside (by decide) ho)
  have childSource : (⟨low.toNat, (sp - 8).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
      (span src (16 * (len.toNat / 16))) := by
    intro x hx hy
    apply hsep x ?_ ?_
    · simp only [MemoryRegion.Contains, hsub] at hx ⊢; omega
    · simp only [MemoryRegion.Contains, span] at hy ⊢; omega
  have stateSource : (span (sp + 80) 32).Disjoint (span src (16 * (len.toNat / 16))) := by
    intro x hx hy
    apply hsep x ?_ ?_
    · simp only [MemoryRegion.Contains, span, h80] at hx ⊢; omega
    · simp only [MemoryRegion.Contains, span] at hy ⊢; omega
  have stateSep : (⟨low.toNat, (sp - 8).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
      (span (sp + 80) 32) := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, hsub, h80] at hx hy
    omega
  have c39 : (callee.arguments[39]'(by change 39 < 53; decide)) = args[39] := keep 39 (by decide)
  have c50 : (callee.arguments[50]'(by change 50 < 53; decide)) = args[50] := keep 50 (by decide)
  have c51 : (callee.arguments[51]'(by change 51 < 53; decide)) = args[51] := keep 51 (by decide)
  have cdf := keep 22 (by decide)
  have ct := types htypes
  obtain ⟨o, exec, tag, doneAtoms, outTypes, outFrame, post⟩ :=
    callContract_exec_values LIR.lifted code .l109980 LIR.Fn109980.frameInfo
      (fun fr ↦ [span (fr.rdi + 16) 16]) _ _ (GHASHUpdate.update_call code hcode hmultiply)
      prepared callee.arguments ret low ct
      (by rw [c39]; exact h39) (by rw [c50]; exact h50) (by rw [c51]; exact h51)
      (cdf.trans hdf)
      (by rw [cspGet]; exact (hstack.readable.of_frame frame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [cspGet]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by dsimp only [ret]; split <;> decide)
      (fun _ ↦ by
        change Writable code prepared ((callee.arguments[4]'(by change 4 < 53; decide)).get 64 - 400) 400
        rw [cspGet, show sp - 8 - 400 = sp - 408 by bv_omega]
        exact (hstack.of_frame frame).sub (Nat.le_refl _) (by omega))
      (by change low.toNat + 400 ≤ ((callee.arguments[4]'(by change 4 < 53; decide)).get 64).toNat; rw [cspGet, hsub]; omega)
      (by rw [cspGet, hsub]; omega) (by trivial)
      (by
        simp only [activationOfValues, callStack, cspGet, cdstGet, csrcGet, countGet]
        refine ⟨(hstack.of_frame frame).of_offsets rfl (addr_sub _ _) (by decide),
          (hr.of_frame frame).sub (Nat.le_refl _) (by omega), stateSep, childSource, stateSource⟩)
  have preserved := Execution.preserved_of_doneAtoms code prepared callee.arguments ret low o ct
    (by rw [c39]; exact h39) (by rw [c50]; exact h50) (by rw [c51]; exact h51)
    (cdf.trans hdf) doneAtoms
  have actualExec : LIR.program.Exec (dialect code) ⟨callee, []⟩ o := by
    have hc : callee = ⟨.l109980, callee.arguments, prepared⟩ := by
      cases callee with
      | mk lab vals st =>
        dsimp only at label cmem
        subst lab st
        rfl
    rw [hc]
    exact exec
  have accepted : continuation.Accepts (dialect code) o.tag = true := by
    rw [tag]
    simp only [StackFrame.Accepts, guard]
    cases use256 <;> rfl
  have reaches := Execution.call_reaches code _ callee continuation o run actualExec accepted
  rw [target] at reaches
  refine ⟨o, reaches, ?_, ?_, outTypes, ?_, ?_⟩
  · simpa only [cspGet, BitVec.sub_add_cancel] using preserved.1
  · intro r hr
    exact (preserved.2 r hr).trans (keep r hr)
  · have prefixFrame : RamWriteFrame mem prepared
        [⟨low.toNat, sp.toNat - low.toNat⟩, span (sp + 96) 16] := by
      apply (RamWriteFrame.refl mem _).trans frame
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      refine ⟨⟨low.toNat, sp.toNat - low.toNat⟩, by simp, ?_, ?_⟩ <;>
        simp only [span, hsub] <;> omega
    change RamWriteFrame prepared o.store
      [⟨low.toNat, ((callee.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - low.toNat⟩,
        span ((callee.arguments[7]'(by change 7 < 53; decide)).get 64 + 16) 16] at outFrame
    rw [cspGet, cdstGet, show sp + 80 + 16 = sp + 96 by bv_omega] at outFrame
    apply prefixFrame.trans outFrame
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨⟨low.toNat, sp.toNat - low.toNat⟩, by simp, Nat.le_refl _, ?_⟩
      simp only [hsub]; omega
    · exact ⟨span (sp + 96) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  · have foldEq (y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) :
        updateBlocks prepared src (len.toNat / 16) y0 y1 initial =
          updateBlocks mem src (len.toNat / 16) y0 y1 initial := by
      by_cases hz : len.toNat / 16 = 0
      · simp only [hz, GHASHUpdate.updateBlocks_zero]
      · apply GHASHUpdate.updateBlocks_of_frame frame
        have hb := disjoint_bounds low.toNat (sp.toNat + 112 - low.toNat)
          src.toNat len.toNat (by omega) (by omega) hsep
        refine ⟨by have := hr.low; omega, ?_⟩
        intro r hin
        obtain rfl := List.mem_singleton.mp hin
        simp only [span, hsub]
        omega
    simp only [activationOfValues, cdstGet, csrcGet, countGet] at post
    have h0 := stateLoad 0 (by decide)
    have h8 := stateLoad 8 (by decide)
    have h16 := stateLoad 16 (by decide)
    have h24 := stateLoad 24 (by decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h8 h16 h24
    simp only [BitVec.ofNat_eq_ofNat] at post ⊢
    rw [h0, h8, h16, h24, foldEq] at post
    simpa only [show sp + 80#64 + 8#64 = sp + 88#64 by bv_omega,
      show sp + 80#64 + 16#64 = sp + 96#64 by bv_omega,
      show sp + 80#64 + 24#64 = sp + 104#64 by bv_omega] using post

end AesGcm.Proofs.Machine.Tag
