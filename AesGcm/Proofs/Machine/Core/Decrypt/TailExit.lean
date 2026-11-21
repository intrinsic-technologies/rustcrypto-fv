import AesGcm.Proofs.Machine.Core.Decrypt.Tail
import AesGcm.Proofs.Machine.Core.Decrypt.Branches
import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem tail_exit (u : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant u).keyBytes) (crypt : CTR.CryptCall u code key)
    (input : ByteArray) (positive : 0 < input.size) (bound : input.size ≤ 16)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (src dst : BitVec 64)
    (frame : Atom.All code args mem
      (if u then LIR.Fn102720.frameAt .l1028e4 fr else LIR.Fn1022c0.frameAt .l102484 fr))
    (typed : GPRsTyped args) (source : args[13].get 64 = src) (length : (args[14].get 64).toNat = input.size)
    (counter : args[15].get 64 = fr.rsp - 120)
    (schedule : AES16.ScheduleIn (AES16.variant u) key (fr.rdi + 32) mem)
    (scheduleRead : Readable mem (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1)))
    (keyPtr : memLoad mem (fr.rsp - 128) 64 = fr.rdi + 32)
    (srcRead : Readable mem src input.size) (bytes : (span src input.size).HasBytes mem input)
    (descRead : Readable mem fr.r8 24) (dest : memLoad mem (fr.r8 + 8) 64 = dst)
    (write : Writable code mem dst input.size)
    (sep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1)), span src input.size,
      span dst input.size, span fr.r8 24], (callStack fr).Disjoint r)
    (descSep : (span fr.r8 24).Disjoint (span dst input.size)) :
    ∃ last : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if u then .l1028e4 else .l102484), args, mem⟩, []⟩ ⟨last, []⟩ ∧
      last.label = (if u then .l102961 else .l102501) ∧
      Atom.All code last.arguments last.store
        (if u then LIR.Fn102720.frameAt .l102961 fr else LIR.Fn1022c0.frameAt .l102501 fr) ∧
      GPRsTyped last.arguments ∧ RamWriteFrame mem last.store [fr.region, span dst input.size] ∧
      (last.arguments[0]'(by change 0 < 53; decide)).get 8 = args[0].get 8 ∧
      (span dst input.size).HasBytes last.store (AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant u) key)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (fr.rsp - 120)))
          (AesGcm.Spec.GCM.bitsOfByteArray input))) ∧
      memLoad last.store (fr.r8 + 8) 64 = dst := by
  let window : Nat := if u then 2912 else 2384
  let childWindow : Nat := if u then 2688 else 2160
  let sp := fr.rsp - 216
  have windowEq : window = childWindow + 224 := by cases u <;> decide
  have fields : args[4] = ⟨64, sp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[5] = ⟨64, fr.rcx⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 152) 64 = fr.r8 ∧ memLoad mem (fr.rsp - 136) 64 = fr.rdx ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      (0x201238 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases u <;> exact frame
  obtain ⟨rsp, df, _, mxcsr, ftw, fcw, descriptor, _, rbx, r12, r13, r14, r15, rbp,
    retRead, ret, retLow, stackWrite, room, align, slot0Read, slot0, slot1Read, slot1,
    slot2Read, slot2, slot3Read, slot3, slotsApart, _⟩ := fields
  have subNat (offset : Nat) (h : offset ≤ window) :
      (fr.rsp - BitVec.ofNat 64 offset).toNat = fr.rsp.toNat - offset := by
    rw [BitVec.toNat_sub_of_le (by change offset % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]
  have spNat : sp.toNat = fr.rsp.toNat - 216 :=
    subNat 216 (by rw [windowEq]; omega)
  have lower : sp - BitVec.ofNat 64 (childWindow + 8) = fr.rsp - BitVec.ofNat 64 window := by
    change fr.rsp - BitVec.ofNat 64 216 - BitVec.ofNat 64 (childWindow + 8) = _
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, windowEq]
    rw [show 216 + (childWindow + 8) = childWindow + 224 by omega]
  have lowerNat := subNat window (Nat.le_refl _)
  have addr64 : sp + 64 = fr.rsp - 152 := by dsimp only [sp]; bv_omega
  have addr88 : sp + 88 = fr.rsp - 128 := by dsimp only [sp]; bv_omega
  have addr96 : sp + 96 = fr.rsp - 120 := by dsimp only [sp]; bv_omega
  have addr112 : sp + 112 = fr.rsp - 104 := by dsimp only [sp]; bv_omega
  have addr152 : sp + 152 = fr.rsp - 64 := by dsimp only [sp]; bv_omega
  have tailWrite : Writable code mem (sp - BitVec.ofNat 64 (childWindow + 8))
      (childWindow + 176) := by
    rw [lower]
    exact stackWrite.sub (Nat.le_refl _) (by omega)
  have tailSep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1)),
      span src input.size, span dst input.size, span fr.r8 24],
      (span (sp - BitVec.ofNat 64 (childWindow + 8)) (childWindow + 176)).Disjoint r := by
    intro r hr x hx hy
    apply sep r hr x ?_ hy
    rw [lower] at hx
    simp only [span, MemoryRegion.Contains, lowerNat] at hx
    simp only [callStack, MemoryRegion.Contains]
    omega
  obtain ⟨tail, tailRun, tailLabel, tailTyped, tailKeep, tailStatus, tailFrame, tailBytes⟩ :=
    tail_reaches u code hcode key crypt input bound positive args mem sp (fr.rdi + 32) src fr.r8 dst
      (by rw [rsp]; rfl) source length (by rw [addr96]; exact counter)
      (by change childWindow + 8 ≤ sp.toNat; rw [spNat]; omega)
      (by rw [spNat]; omega) tailWrite schedule scheduleRead
      (by rw [addr88]; exact keyPtr) srcRead bytes descRead
      (by rw [addr64]; exact descriptor) dest write tailSep
      ⟨slot0Read, slot0, slot1Read, slot1, slot3Read, slot3, slot2Read, slot2⟩
      (by
        change sp.toNat + 168 ≤ 0x201208 ∨ 0x201238 + childWindow + 8 ≤ sp.toNat
        rw [spNat]
        omega)
      typed df (by rw [mxcsr]; rfl) (by rw [ftw]; rfl) (by rw [fcw]; rfl)
  rcases tail with ⟨label, tailArgs, tailMem⟩
  dsimp only at tailRun tailLabel tailTyped tailKeep tailStatus tailFrame tailBytes
  subst label
  change Values Value Reg.count at tailArgs
  obtain ⟨last, lastRun, lastLabel, lastMem, lastRax, lastKeep, lastTyped⟩ :=
    tailDone_runBlock u code tailArgs tailMem
  have finalStep : LIR.program.step (dialect code)
      ⟨⟨(if u then .l10295f else .l1024ff), tailArgs, tailMem⟩, []⟩ = .next ⟨last, []⟩ := by
    rw [Program.step, lastRun]
    rfl
  let stackWrites := [span (sp - BitVec.ofNat 64 (childWindow + 8)) (childWindow + 64),
    span (sp + 112) 4, span (sp + 152) 16]
  have stackBounds (r : MemoryRegion) (hr : r ∈ stackWrites) :
      fr.low.toNat ≤ r.start ∧ r.start + r.size ≤ fr.rsp.toNat - 48 := by
    simp only [stackWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    have n104 : (fr.rsp - 104).toNat = fr.rsp.toNat - 104 :=
      subNat 104 (by rw [windowEq]; omega)
    have n64 : (fr.rsp - 64).toNat = fr.rsp.toNat - 64 :=
      subNat 64 (by rw [windowEq]; omega)
    rcases hr with rfl | rfl | rfl <;>
      simp only [span, lower, lowerNat, addr112, n104, addr152, n64] <;> omega
  have finalWrites : RamWriteFrame mem tailMem [fr.region, span dst input.size] := by
    apply (RamWriteFrame.refl _ _).trans tailFrame
    intro r hr
    change r ∈ stackWrites ++ [span dst input.size] at hr
    rw [List.mem_append, List.mem_singleton] at hr
    rcases hr with hstack | rfl
    · obtain ⟨start, stop⟩ := stackBounds r hstack
      refine ⟨fr.region, by simp, start, ?_⟩
      simp only [Activation.region]
      omega
    · exact ⟨span dst input.size, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have dstApart := disjoint_bounds _ _ _ _ (by
    change 0 < fr.rsp.toNat + 8 - fr.low.toNat
    omega) positive (sep (span dst input.size) (by simp))
  have savedOutside (offset : Nat) (h : offset ≤ 48) :
      Outside (stackWrites ++ [span dst input.size]) (fr.rsp - BitVec.ofNat 64 offset) 8 := by
    have addr := subNat offset (by omega)
    have retEnd := retRead.low
    refine ⟨by rw [addr]; omega, ?_⟩
    intro r hr
    rw [List.mem_append, List.mem_singleton] at hr
    rw [addr]
    rcases hr with hstack | rfl
    · have := (stackBounds r hstack).2
      omega
    · change fr.rsp.toNat - offset + 8 ≤ dst.toNat ∨
        dst.toNat + input.size ≤ fr.rsp.toNat - offset
      change fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ dst.toNat ∨
        dst.toNat + input.size ≤ fr.low.toNat at dstApart
      omega
  have exitFrame : Atom.All code args mem
      (if u then LIR.Fn102720.frameAt .l102961 fr else LIR.Fn1022c0.frameAt .l102501 fr) := by
    cases u <;>
      exact ⟨rsp, df, mxcsr, ftw, fcw, rbx, r12, r13, r14, r15, rbp,
        retRead, ret, retLow, stackWrite, room, align, trivial⟩
  have finalFrame : Atom.All code last.arguments last.store
      (if u then LIR.Fn102720.frameAt .l102961 fr else LIR.Fn1022c0.frameAt .l102501 fr) := by
    rw [lastMem]
    apply atomsAll_of_frame tailFrame ?_ exitFrame
    intro atom hr
    cases u <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2, LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG2,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (lastKeep _ (by decide)).trans (tailKeep _ (by decide))
      | trivial
      | exact savedOutside 48 (by decide)
      | exact savedOutside 40 (by decide)
      | exact savedOutside 32 (by decide)
      | exact savedOutside 24 (by decide)
      | exact savedOutside 16 (by decide)
      | exact savedOutside 8 (by decide)
      | change Outside (stackWrites ++ [span dst input.size]) fr.rsp 8
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using savedOutside 0 (by decide)
  have descOutside : Outside [fr.region, span dst input.size] fr.r8 24 := by
    have stackOutside := outside_activationRegion descRead (by decide) (by omega)
      (sep (span fr.r8 24) (by simp))
    refine ⟨stackOutside.1, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackOutside.2 _ (by simp)
    · exact disjoint_bounds _ _ _ _ (by decide : 0 < 24) positive descSep
  refine ⟨last, tailRun.trans (Semantics.Reaches.single finalStep), lastLabel, finalFrame,
    lastTyped tailTyped, ?_, ?_, ?_, ?_⟩
  · rw [lastMem]
    exact finalWrites
  · rw [lastRax]
    simpa only [Value.get, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] using tailStatus
  · rw [lastMem]
    rwa [addr96] at tailBytes
  · rw [lastMem]
    exact (finalWrites.memLoad_eq
      (outside_subregion descOutside (offset := 8) (count := 8) (by decide) (by decide))).trans dest

end AesGcm.Proofs.Machine.Core.Decrypt
