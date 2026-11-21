import AesGcm.Proofs.Machine.GHASHUpdate.Batches
import AesGcm.Proofs.Machine.GHASHUpdate.Remainder
import AesGcm.Proofs.Machine.GHASHUpdate.Driver
import AesGcm.Proofs.Machine.GHASHUpdate.Initialize
import AesGcm.Proofs.Machine.GHASHInterface
import AesGcm.Proofs.Machine.LIR.Fn109980.Frame
import AesGcm.Proofs.Machine.LIR.Fn109ac0.Frame
import AesGcm.Proofs.Machine.LIR.Fn1034c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn1034d0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102b80.Frame

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 2000000 in
theorem update_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) :
    CallContract LIR.lifted code .l109980 LIR.Fn109980.frameInfo
      (fun fr ↦ [span (fr.rdi + 16) 16])
      (fun fr mem ↦ Writable code mem fr.rdi 32 ∧
        Readable mem fr.rsi (16 * fr.rdx.toNat) ∧
        (callStack fr).Disjoint (span fr.rdi 32) ∧
        (callStack fr).Disjoint (span fr.rsi (16 * fr.rdx.toNat)) ∧
        (span fr.rdi 32).Disjoint (span fr.rsi (16 * fr.rdx.toNat)))
      (fun fr mem ↦
        let result := updateBlocks fr.original fr.rsi fr.rdx.toNat
          (memLoad fr.original fr.rdi 64) (memLoad fr.original (fr.rdi + 8) 64)
          (memLoad fr.original (fr.rdi + 16) 64, memLoad fr.original (fr.rdi + 24) 64)
        memLoad mem (fr.rdi + 16) 64 = result.1 ∧
        memLoad mem (fr.rdi + 24) 64 = result.2) := by
  intro fr loc hl hm hentry hTypes hpre
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm hentry hTypes hpre
  subst label mem
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 400) 400 ∧
    fr.low.toNat + 400 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, -, hcount, h3, h5, hsrc, hdst, -, -, h12, h13, h14, h15,
    h39, h50, h51, hreadret, hret, hretlow, hstack, hroom, halign, -⟩
  rcases hpre with ⟨hw, hr, hdstsep, hsrcsep, hdata⟩
  let sp := fr.rsp - 88
  have spNat : sp.toNat = fr.rsp.toNat - 88 := by
    have he : (88 : BitVec 64) ≤ fr.rsp := by change 88 ≤ fr.rsp.toNat; omega
    simpa only [sp, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat] using BitVec.toNat_sub_of_le he
  have spAddr (off : Nat) (ho : off ≤ 96) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    have := hreadret.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have sp24 : sp + 24 = fr.rsp - 64 := by dsimp only [sp]; bv_omega
  have sp32 : sp + 32 = fr.rsp - 56 := by dsimp only [sp]; bv_omega
  have sp88 : sp + 88 = fr.rsp := by dsimp only [sp]; bv_omega
  have hbatch : driverBatchBytes fr.rdx = BitVec.ofNat 64 (64*(fr.rdx.toNat/4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [batch_count_mask fr.rdx (by have := hr.low; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hr.low; omega)]
  have batchZero : driverBatchBytes fr.rdx = 0 ↔ fr.rdx.toNat/4 = 0 := by
    rw [hbatch]
    constructor
    · intro he
      have he := congrArg BitVec.toNat he
      change (64*(fr.rdx.toNat/4)) % 2^64 = 0 at he
      rw [Nat.mod_eq_of_lt (by have := hr.low; omega)] at he
      omega
    · intro he
      simp only [he, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
  obtain ⟨a, prepared, entry, a4, a3, a14, a13, a5, akeep, atypes, entryFrame,
      countSlot, dstSlot, saved3, saved12, saved13, saved14, saved15, saved5⟩ :=
    driver_entry_runBlock code hcode args fr.original fr.rsp fr.rsi fr.rdi fr.rdx
      (by rw [hsp]; rfl) (by rw [hsrc]; rfl) (by rw [hdst]; rfl) (by rw [hcount]; rfl)
      hTypes (hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) (by omega)
  change a[4] = ⟨64, sp⟩ at a4
  change RamWriteFrame fr.original prepared [span sp 88] at entryFrame
  have entryStep : LIR.program.step (dialect code) ⟨⟨.l109980, args, fr.original⟩, []⟩ =
      .next ⟨⟨if fr.rdx.toNat/4 = 0 then .l1099d5 else .l1099b4, a, prepared⟩, []⟩ := by
    rw [Program.step, entry]
    by_cases hz : fr.rdx.toNat/4 = 0
    · rw [ite_eq_left hz, ite_eq_left (batchZero.mpr hz)]
      rfl
    · have he : driverBatchBytes fr.rdx ≠ 0 := fun he => hz (batchZero.mp he)
      rw [ite_eq_right hz, ite_eq_right he]
      rfl
  have dstBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 32 (by omega) (by decide) hdstsep
  have entryState : Outside [span sp 88] fr.rdi 32 := by
    refine ⟨by have := hw.readable.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, spNat]
    omega
  have stateLoad (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad prepared (fr.rdi + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (fr.rdi + BitVec.ofNat 64 off) 64 :=
    entryFrame.memLoad_eq (outside_add_offset entryState (by decide) ho)
  have inputLoad (off : Nat) (ho : off + 8 ≤ 16*fr.rdx.toNat) :
      memLoad prepared (fr.rsi + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 off) 64 := by
    have hb := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      fr.rsi.toNat (16*fr.rdx.toNat) (by omega) (by omega) hsrcsep
    apply entryFrame.memLoad_eq
    apply outside_add_offset (off := off) (len := 16*fr.rdx.toNat) _ (by decide) ho
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, spNat]
    omega
  have regionSep (high : Nat) (hh : high ≤ fr.rsp.toNat + 8) :
      (⟨fr.low.toNat, high - fr.low.toNat⟩ : MemoryRegion).Disjoint (span fr.rdi 32) := by
    intro x hx hy
    apply hdstsep x ?_ hy
    simp only [MemoryRegion.Contains, callStack] at hx ⊢
    omega
  have sourceSep (high len : Nat) (hh : high ≤ fr.rsp.toNat + 8) (hn : len ≤ 16*fr.rdx.toNat) :
      (⟨fr.low.toNat, high - fr.low.toNat⟩ : MemoryRegion).Disjoint (span fr.rsi len) := by
    intro x hx hy
    apply hsrcsep x ?_ ?_
    · simp only [MemoryRegion.Contains, callStack] at hx ⊢; omega
    · simp only [MemoryRegion.Contains, span] at hy ⊢; omega
  have dataSep (len : Nat) (hn : len ≤ 16*fr.rdx.toNat) :
      (span fr.rdi 32).Disjoint (span fr.rsi len) := by
    intro x hx hy
    apply hdata x hx
    simp only [MemoryRegion.Contains, span] at hy ⊢
    omega
  have ptrSep : (⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩ : MemoryRegion).Disjoint (span (sp + 32) 8) := by
    intro x hx hy
    have ha : (sp + 32).toNat = sp.toNat + 32 := spAddr 32 (by decide)
    simp only [MemoryRegion.Contains, span, ha] at hx hy
    omega
  have ptrState : (span fr.rdi 32).Disjoint (span (sp + 32) 8) := by
    intro x hx hy
    apply hdstsep x ?_ hx
    have ha : (sp + 32).toNat = sp.toNat + 32 := spAddr 32 (by decide)
    simp only [MemoryRegion.Contains, span, callStack, ha] at hy ⊢
    omega
  have a39 : a[39] = args[39] := akeep 39 (by decide)
  have a50 : a[50] = args[50] := akeep 50 (by decide)
  have a51 : a[51] = args[51] := akeep 51 (by decide)
  obtain ⟨b, batchMem, batchesReach, b4, bkeep, btypes, batchFrame, batchPost⟩ :=
    driver_batches code hcode hmultiply (fr.rdx.toNat/4) a prepared sp fr.rsi fr.rdi fr.low
      (by rw [a4]; rfl) (by rw [a3]; rfl) (by rw [a5]; exact hbatch)
      (by rw [sp32]; exact dstSlot) atypes
      (by rw [a39, h39]; rfl) (by rw [a50, h50]; rfl) (by rw [a51, h51]; rfl)
      ((akeep 22 (by decide)).trans hdf)
      (by rw [show sp - 312 = fr.rsp - 400 by dsimp only [sp]; bv_omega]
          exact (hstack.of_frame entryFrame).sub (Nat.le_refl _) (by omega))
      (by rw [spNat]; omega) (by rw [spNat]; omega)
      ((hr.of_frame entryFrame).sub (Nat.le_refl _) (by omega))
      (by rw [sp32]; exact (hstack.readable.of_frame entryFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (sourceSep _ _ (by rw [spNat]; omega) (by omega)) ptrSep (hw.of_frame entryFrame)
      (regionSep _ (by rw [spNat]; omega)) (dataSep _ (by omega)) ptrState
  have batchSlot (off : Nat) (ho : 24 ≤ off) (ho' : off + 8 ≤ 96) :
      memLoad batchMem (sp + BitVec.ofNat 64 off) 64 = memLoad prepared (sp + BitVec.ofNat 64 off) 64 := by
    apply batchFrame.memLoad_eq
    have addr := spAddr off (by omega)
    have d16 : (fr.rdi + 16).toNat = fr.rdi.toNat + 16 := by
      have := hw.readable.low
      simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by have := hreadret.low; rw [addr]; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · rw [addr]; dsimp only; omega
    · simp only [span, addr, d16]; rw [spNat]; omega
  have b3 : b[3] = a[3] := bkeep 3 (by decide)
  have b13 : b[13] = a[13] := bkeep 13 (by decide)
  have b14 : b[14] = a[14] := bkeep 14 (by decide)
  have b39 : b[39] = a[39] := bkeep 39 (by decide)
  have b50 : b[50] = a[50] := bkeep 50 (by decide)
  have b51 : b[51] = a[51] := bkeep 51 (by decide)
  have countSlot' : memLoad batchMem (sp + 24) 64 = fr.rdx := by
    have he : memLoad batchMem (sp + 24) 64 = memLoad prepared (sp + 24) 64 := batchSlot 24 (by decide) (by decide)
    rw [he, sp24]
    exact countSlot
  obtain ⟨c, finalMem, remainderReach, c4, ckeep, ctypes, tailFrame, tailPost⟩ :=
    driver_remainder code hcode hmultiply b batchMem sp fr.rsi fr.rdi fr.low fr.rdx
      (by rw [b4]; rfl) (by rw [b3, a3]; rfl) (by rw [b14, a14]; rfl)
      (by rw [b13, a13]; rfl)
      (by rw [sp24]; exact ((hstack.readable.of_frame entryFrame).of_frame batchFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      countSlot' btypes
      (by rw [b39, a39, h39]; rfl) (by rw [b50, a50, h50]; rfl) (by rw [b51, a51, h51]; rfl)
      ((bkeep 22 (by decide)).trans ((akeep 22 (by decide)).trans hdf))
      (by rw [show sp - 136 = fr.rsp - 224 by dsimp only [sp]; bv_omega]
          exact ((hstack.of_frame entryFrame).of_frame batchFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [spNat]; omega) (by rw [spNat]; omega)
      ((hr.of_frame entryFrame).of_frame batchFrame)
      (sourceSep _ _ (by rw [spNat]; omega) (Nat.le_refl _))
      ((hw.of_frame entryFrame).of_frame batchFrame)
      (regionSep _ (by rw [spNat]; omega)) hdata
  have bodyFrame : RamWriteFrame prepared finalMem
      [⟨fr.low.toNat, sp.toNat + 24 - fr.low.toNat⟩, span (fr.rdi + 16) 16] := by
    have hf : RamWriteFrame prepared batchMem
        [⟨fr.low.toNat, sp.toNat + 24 - fr.low.toNat⟩, span (fr.rdi + 16) 16] := by
      apply (RamWriteFrame.refl _ _).trans batchFrame
      intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl
      · refine ⟨⟨fr.low.toNat, sp.toNat + 24 - fr.low.toNat⟩, by simp, Nat.le_refl _, ?_⟩
        dsimp only
        omega
      · exact ⟨span (fr.rdi + 16) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
    exact hf.trans tailFrame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have fullFrame : RamWriteFrame fr.original finalMem [fr.region, span (fr.rdi + 16) 16] := by
    have hf : RamWriteFrame fr.original prepared [fr.region, span (fr.rdi + 16) 16] := by
      apply (RamWriteFrame.refl _ _).trans entryFrame
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [Activation.region, span, spNat] <;> omega
    apply hf.trans bodyFrame
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨fr.region, by simp, Nat.le_refl _, ?_⟩
      simp only [Activation.region, spNat]
      omega
    · exact ⟨span (fr.rdi + 16) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have finalSlot (off : Nat) (ho : 24 ≤ off) (ho' : off + 8 ≤ 96) :
      memLoad finalMem (sp + BitVec.ofNat 64 off) 64 = memLoad prepared (sp + BitVec.ofNat 64 off) 64 := by
    apply bodyFrame.memLoad_eq
    have addr := spAddr off (by omega)
    have d16 : (fr.rdi + 16).toNat = fr.rdi.toNat + 16 := by
      have := hw.readable.low
      simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by have := hreadret.low; rw [addr]; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · rw [addr]; dsimp only; omega
    · simp only [span, addr, d16]; rw [spNat]; omega
  have retFinal : memLoad finalMem (sp + 88) 64 = fr.ret := by
    rw [sp88]
    apply Eq.trans (fullFrame.memLoad_eq ?_) hret
    refine ⟨by have := hreadret.low; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region]; omega
    · have d16 : (fr.rdi + 16).toNat = fr.rdi.toNat + 16 := by
        have := hw.readable.low
        simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [span, d16]
      omega
  have exitRead : Readable finalMem (sp + 40) 56 := by
    have pref : Readable fr.original (sp + 40) 48 := by
      rw [show sp + 40 = fr.rsp - 48 by dsimp only [sp]; bv_omega]
      exact hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    have last : Readable fr.original ((sp + 40) + BitVec.ofNat 64 48) 8 := by
      rw [show (sp + 40) + BitVec.ofNat 64 48 = fr.rsp by dsimp only [sp]; bv_omega]
      exact hreadret
    exact (readable_append pref last).of_frame fullFrame
  obtain ⟨o, exit, tag, outMem, out4, out3, out12, out13, out14, out15, out5, keep, outTypes⟩ :=
    driver_exit_runBlock code c finalMem sp (by rw [c4]; rfl) ctypes exitRead (by rw [retFinal]; exact hretlow)
  have finishExec : LIR.program.Exec (dialect code) ⟨⟨.l109aaa, c, finalMem⟩, []⟩ o := by
    apply Program.Exec.done
    rw [Program.step, exit]
    rfl
  have reach := ((Semantics.Reaches.single entryStep).trans batchesReach).trans remainderReach
  have exec : LIR.program.Exec (dialect code) ⟨⟨.l109980, args, fr.original⟩, []⟩ o :=
    .of_sem (reach.exec finishExec.sem)
  have loadSaved (off : Nat) (ho : 40 ≤ off) (ho' : off ≤ 80) :
      memLoad finalMem (sp + BitVec.ofNat 64 off) 64 =
        memLoad prepared (fr.rsp - BitVec.ofNat 64 (88-off)) 64 := by
    rw [finalSlot off (by omega) (by omega)]
    congr 1
    dsimp only [sp]
    have he : BitVec.ofNat 64 (88-off) = 88 - BitVec.ofNat 64 off :=
      (BitVec.ofNat_sub_ofNat_of_le 88 off (by omega) (by omega)).symm
    rw [he]
    bv_omega
  have s3 : memLoad finalMem (sp + 40) 64 = fr.rbx := by
    have he : memLoad finalMem (sp + 40) 64 = memLoad prepared (fr.rsp - 48) 64 :=
      loadSaved 40 (by decide) (by decide)
    rw [he]
    exact saved3.trans (show args[3].get 64 = _ by rw [h3]; rfl)
  have s12 : memLoad finalMem (sp + 48) 64 = fr.r12 := by
    have he : memLoad finalMem (sp + 48) 64 = memLoad prepared (fr.rsp - 40) 64 :=
      loadSaved 48 (by decide) (by decide)
    rw [he]
    exact saved12.trans (show args[12].get 64 = _ by rw [h12]; rfl)
  have s13 : memLoad finalMem (sp + 56) 64 = fr.r13 := by
    have he : memLoad finalMem (sp + 56) 64 = memLoad prepared (fr.rsp - 32) 64 :=
      loadSaved 56 (by decide) (by decide)
    rw [he]
    exact saved13.trans (show args[13].get 64 = _ by rw [h13]; rfl)
  have s14 : memLoad finalMem (sp + 64) 64 = fr.r14 := by
    have he : memLoad finalMem (sp + 64) 64 = memLoad prepared (fr.rsp - 24) 64 :=
      loadSaved 64 (by decide) (by decide)
    rw [he]
    exact saved14.trans (show args[14].get 64 = _ by rw [h14]; rfl)
  have s15 : memLoad finalMem (sp + 72) 64 = fr.r15 := by
    have he : memLoad finalMem (sp + 72) 64 = memLoad prepared (fr.rsp - 16) 64 :=
      loadSaved 72 (by decide) (by decide)
    rw [he]
    exact saved15.trans (show args[15].get 64 = _ by rw [h15]; rfl)
  have s5 : memLoad finalMem (sp + 80) 64 = fr.rbp := by
    have he : memLoad finalMem (sp + 80) 64 = memLoad prepared (fr.rsp - 8) 64 :=
      loadSaved 80 (by decide) (by decide)
    rw [he]
    exact saved5.trans (show args[5].get 64 = _ by rw [h5]; rfl)
  have unchanged (r : Fin 53) (hr : r.val ∈ [22,39,50,51]) : o.values[r] = args[r] := by
    apply (keep r ?_).trans ((ckeep r ?_).trans ((bkeep r ?_).trans (akeep r ?_)))
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
  refine ⟨o, exec, ?_, ?_, outTypes, ?_, ?_⟩
  · rw [tag, retFinal]
  · change o.values[4] = ⟨64, fr.rsp + 8⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      o.values[3] = ⟨64, fr.rbx⟩ ∧ o.values[5] = ⟨64, fr.rbp⟩ ∧
      o.values[12] = ⟨64, fr.r12⟩ ∧ o.values[13] = ⟨64, fr.r13⟩ ∧
      o.values[14] = ⟨64, fr.r14⟩ ∧ o.values[15] = ⟨64, fr.r15⟩ ∧
      o.values[39] = ⟨32, fr.mxcsr⟩ ∧ o.values[50] = ⟨16, fr.ftw⟩ ∧
      o.values[51] = ⟨16, fr.fcw⟩ ∧ True
    refine ⟨?_, (unchanged 22 (by decide)).trans hdf, ?_, ?_, ?_, ?_, ?_, ?_,
      (unchanged 39 (by decide)).trans h39, (unchanged 50 (by decide)).trans h50,
      (unchanged 51 (by decide)).trans h51, trivial⟩
    · rw [out4]; congr 1; dsimp only [sp]; bv_omega
    · simpa only [s3] using out3
    · simpa only [s5] using out5
    · simpa only [s12] using out12
    · simpa only [s13] using out13
    · simpa only [s14] using out14
    · simpa only [s15] using out15
  · rw [outMem]
    exact fullFrame
  · rw [outMem]
    have keyOutside := stateKey_outside ⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩ fr.rdi
      (by change 0 < sp.toNat - fr.low.toNat; rw [spNat]; omega) hw.readable.low
      (regionSep _ (by rw [spNat]; omega))
    have key0 : memLoad batchMem fr.rdi 64 = memLoad prepared fr.rdi 64 := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        (batchFrame.memLoad_eq (outside_add_offset keyOutside (off := 0) (n := 8) (by decide) (by decide)) :
          memLoad batchMem (fr.rdi + BitVec.ofNat 64 0) 64 = memLoad prepared (fr.rdi + BitVec.ofNat 64 0) 64)
    have key8 : memLoad batchMem (fr.rdi + 8) 64 = memLoad prepared (fr.rdi + 8) 64 :=
      batchFrame.memLoad_eq (outside_add_offset keyOutside (off := 8) (by decide) (by decide))
    have remainingFold (y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) :
        updateBlocks batchMem (fr.rsi + BitVec.ofNat 64 (64*(fr.rdx.toNat/4))) (fr.rdx.toNat%4) y0 y1 initial =
          updateBlocks prepared (fr.rsi + BitVec.ofNat 64 (64*(fr.rdx.toNat/4))) (fr.rdx.toNat%4) y0 y1 initial := by
      by_cases hz : fr.rdx.toNat%4 = 0
      · simp only [hz, updateBlocks_zero]
      · have outside := input_outside ⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩ fr.rdi fr.rsi (16*fr.rdx.toNat)
          (by change 0 < sp.toNat - fr.low.toNat; rw [spNat]; omega) (by omega)
          hw.readable.low hr.low (sourceSep _ _ (by rw [spNat]; omega) (Nat.le_refl _)) hdata
        apply updateBlocks_of_frame batchFrame
        exact outside_add_offset outside (by omega) (by omega)
    dsimp only at batchPost tailPost ⊢
    rw [key0, key8, batchPost.1, batchPost.2, remainingFold] at tailPost
    have append := updateBlocks_append prepared fr.rsi (memLoad prepared fr.rdi 64)
      (memLoad prepared (fr.rdi + 8) 64) (4*(fr.rdx.toNat/4)) (fr.rdx.toNat%4)
      (memLoad prepared (fr.rdi + 16) 64, memLoad prepared (fr.rdi + 24) 64)
    have total : 4*(fr.rdx.toNat/4) + fr.rdx.toNat%4 = fr.rdx.toNat := by omega
    rw [total, show 16*(4*(fr.rdx.toNat/4)) = 64*(fr.rdx.toNat/4) by omega] at append
    rw [← append] at tailPost
    have state0 : memLoad prepared fr.rdi 64 = memLoad fr.original fr.rdi 64 := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using stateLoad 0 (by decide)
    have state8 : memLoad prepared (fr.rdi + 8) 64 = memLoad fr.original (fr.rdi + 8) 64 := stateLoad 8 (by decide)
    have state16 : memLoad prepared (fr.rdi + 16) 64 = memLoad fr.original (fr.rdi + 16) 64 := stateLoad 16 (by decide)
    have state24 : memLoad prepared (fr.rdi + 24) 64 = memLoad fr.original (fr.rdi + 24) 64 := stateLoad 24 (by decide)
    rw [state0, state8, state16, state24] at tailPost
    have foldEq := updateBlocks_congr prepared fr.original fr.rsi fr.rsi
      (memLoad fr.original fr.rdi 64) (memLoad fr.original (fr.rdi + 8) 64) fr.rdx.toNat
      (memLoad fr.original (fr.rdi + 16) 64, memLoad fr.original (fr.rdi + 24) 64)
      (fun j hj => inputLoad (16*j) (by omega)) (fun j hj => inputLoad (16*j+8) (by omega))
    simpa only [foldEq] using tailPost

end AesGcm.Proofs.Machine.GHASHUpdate
