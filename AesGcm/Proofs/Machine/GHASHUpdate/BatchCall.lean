import AesGcm.Proofs.Machine.GHASHUpdate.Batch
import AesGcm.Proofs.Machine.GHASHUpdate.FourBlockCall

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface
open AesGcm.Proofs.Machine.GHASH

theorem batch_return_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (sp : BitVec 64) (hsp : args[4].get 64 = sp)
    (hTypes : GPRsTyped args) (hr : Readable mem (sp + 136) 8)
    (hret : (memLoad mem (sp + 136) 64).toNat < 2^32) :
    ∃ o : Output Value Ram Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l109d81, args, mem⟩ = .returned o ∧
      o.tag = some ⟨64, memLoad mem (sp + 136) 64⟩ ∧ o.store = mem ∧
      o.values[4] = ⟨64, sp + 144⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values := by
  have hlow := hr.low
  runtime_context [hsp]
  refine ⟨?out, ?execution, ?tag, ?store, ?sp, ?preserved, ?typed⟩
  case execution =>
    cfg_eval [hsp]
    runtime_guards returned
    rfl
  case tag => runtime_finish []
  case store => rfl
  case sp => runtime_finish []
  case preserved =>
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case typed => runtime_typed

set_option maxHeartbeats 2400000 in
theorem batch_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) :
    CallContract LIR.lifted code .l109ac0 LIR.Fn109ac0.frameInfo
      (fun fr => [span (memLoad fr.original fr.rdi 64 + 16) 16])
      (fun fr mem =>
        let dst := memLoad fr.original fr.rdi 64
        Readable mem fr.rdi 8 ∧ Readable mem fr.rsi 64 ∧ Writable code mem dst 32 ∧
          (callStack fr).Disjoint (span fr.rdi 8) ∧
          (callStack fr).Disjoint (span fr.rsi 64) ∧
          (callStack fr).Disjoint (span dst 32))
      (fun fr mem =>
        let dst := memLoad fr.original fr.rdi 64
        let result := updateBlocks fr.original fr.rsi 4
          (memLoad fr.original dst 64) (memLoad fr.original (dst + 8) 64)
          (memLoad fr.original (dst + 16) 64, memLoad fr.original (dst + 24) 64)
        memLoad mem (dst + 16) 64 = result.1 ∧ memLoad mem (dst + 24) 64 = result.2) := by
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
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 304) 304 ∧
    fr.low.toNat + 304 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, -, -, h3, h5, hsrc, hptr, -, -, h12, h13, h14, h15,
    h39, h50, h51, hreadret, hret, hretlow, hstack, hroom, halign, -⟩
  rcases hpre with ⟨hp, hr, hw, hptrsep, hsrcsep, hdstsep⟩
  let dst := memLoad fr.original fr.rdi 64
  change Writable code fr.original dst 32 at hw
  let sp := fr.rsp - 144
  let src := fr.rsp - 128
  let full := [fr.region, span (dst + 16) 16]
  have hsub : sp.toNat = fr.rsp.toNat - 144 := by
    have hle : (144 : BitVec 64) ≤ fr.rsp := by change 144 ≤ fr.rsp.toNat; omega
    simpa [sp] using BitVec.toNat_sub_of_le hle
  have hsrcNat : src.toNat = fr.rsp.toNat - 128 := by
    have hle : (128 : BitVec 64) ≤ fr.rsp := by change 128 ≤ fr.rsp.toNat; omega
    simpa [src] using BitVec.toNat_sub_of_le hle
  have ptrBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 8 (by omega) (by decide) hptrsep
  have srcBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat 64 (by omega) (by decide) hsrcsep
  have dstBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    dst.toNat 32 (by omega) (by decide) hdstsep
  have hnativeStack : Writable code fr.original (fr.rsp - 144) 144 :=
    hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨a, prepared, hcall, asp, asrc, adst, keep, preparedTypes, hframe, hreturn, words⟩ :=
    batch_runBlock code hcode args fr.original fr.rsp fr.rsi fr.rdi
      (by rw [hsp]; rfl) (by rw [hsrc]; rfl) (by rw [hptr]; rfl) hTypes hr hp hnativeStack
      (by omega) (by omega) (by omega)
  change RamWriteFrame fr.original prepared [span sp 144] at hframe
  have hnativeFull : RamWriteFrame fr.original prepared full := by
    apply (RamWriteFrame.refl _ _).trans hframe
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp [full], ?_, ?_⟩ <;>
      simp only [Activation.region, span, hsub] <;> omega
  have nativeStateOutside : Outside [span sp 144] dst 32 := by
    refine ⟨by have := hw.readable.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hsub]
    omega
  have stateLoad (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad prepared (dst + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (dst + BitVec.ofNat 64 off) 64 :=
    hframe.memLoad_eq (outside_add_offset nativeStateOutside (by decide) ho)
  have aspGet : a[4].get 64 = sp := by rw [asp]; rfl
  have asrcGet : a[6].get 64 = src := by rw [asrc]; rfl
  have adstGet : a[7].get 64 = dst := by rw [adst]; rfl
  have a39 : a[39] = args[39] := keep 39 (by decide)
  have a50 : a[50] = args[50] := keep 50 (by decide)
  have a51 : a[51] = args[51] := keep 51 (by decide)
  have a22 : a[22] = args[22] := keep 22 (by decide)
  have childRead : Readable prepared src 64 :=
    (hstack.readable.of_frame hframe).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have childRetRead : Readable prepared sp 8 :=
    (hstack.readable.of_frame hframe).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have childStack : Writable code prepared (sp - 160) 160 := by
    rw [show sp - 160 = fr.rsp - 304 by dsimp only [sp]; bv_omega]
    exact (hstack.of_frame hframe).sub (Nat.le_refl _) (by omega)
  have childSrcSep : (⟨fr.low.toNat, sp.toNat + 8 - fr.low.toNat⟩ : MemoryRegion).Disjoint
      (span src 64) := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, hsrcNat, hsub] at hx hy
    omega
  have childDstSep : (⟨fr.low.toNat, sp.toNat + 8 - fr.low.toNat⟩ : MemoryRegion).Disjoint
      (span dst 32) := by
    intro x hx hy
    apply hdstsep x ?_ hy
    simp only [MemoryRegion.Contains, callStack, hsub] at hx ⊢
    omega
  have childDataSep : (span dst 32).Disjoint (span src 64) := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, hsrcNat] at hx hy
    omega
  obtain ⟨calleeOut, calleeExec, calleeTag, calleeDone, calleeTypes, calleeFrame, calleePost⟩ :=
    callContract_exec_values LIR.lifted code .l1034d0 LIR.Fn1034d0.frameInfo
      (fun fr => [span (fr.rdi + 16) 16]) _ _ (fourBlock_call code hcode hmultiply)
      prepared a 0x109d81 fr.low preparedTypes
      (by rw [a39, h39]; rfl) (by rw [a50, h50]; rfl) (by rw [a51, h51]; rfl)
      (a22.trans hdf)
      (by simpa only [aspGet] using childRetRead)
      (by simpa only [aspGet] using hreturn) (by decide)
      (fun _ => by
        change Writable code prepared (a[4].get 64 - 160) 160
        rw [aspGet]
        exact childStack)
      (by change fr.low.toNat + 160 ≤ (a[4].get 64).toNat; rw [aspGet, hsub]; omega)
      (by rw [aspGet, hsub]; omega) (by trivial)
      (by simpa only [activationOfValues, callStack, aspGet, asrcGet, adstGet] using
        And.intro childRead (And.intro (hw.of_frame hframe)
          (And.intro childSrcSep (And.intro childDstSep childDataSep))))
  change calleeOut.values[4] = ⟨64, a[4].get 64 + 8⟩ ∧ calleeOut.values[22] = ⟨1, 0⟩ ∧
    calleeOut.values[3] = ⟨64, a[3].get 64⟩ ∧ calleeOut.values[5] = ⟨64, a[5].get 64⟩ ∧
    calleeOut.values[12] = ⟨64, a[12].get 64⟩ ∧ calleeOut.values[13] = ⟨64, a[13].get 64⟩ ∧
    calleeOut.values[14] = ⟨64, a[14].get 64⟩ ∧ calleeOut.values[15] = ⟨64, a[15].get 64⟩ ∧
    calleeOut.values[39] = ⟨32, a[39].get 32⟩ ∧ calleeOut.values[50] = ⟨16, a[50].get 16⟩ ∧
    calleeOut.values[51] = ⟨16, a[51].get 16⟩ ∧ True at calleeDone
  rcases calleeDone with ⟨csp, cdf, c3, c5, c12, c13, c14, c15, c39, c50, c51, -⟩
  have childWithin : RegionsWithin
      [⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩, span (dst + 16) 16] full := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨fr.region, by simp [full], Nat.le_refl _, ?_⟩
      simp only [Activation.region, hsub]
      omega
    · exact ⟨span (dst + 16) 16, by simp [full], Nat.le_refl _, Nat.le_refl _⟩
  have cf : RamWriteFrame prepared calleeOut.store
      [⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩, span (dst + 16) 16] := by
    simpa only [activationOfValues, Activation.region, aspGet, adstGet] using calleeFrame
  have hfull : RamWriteFrame fr.original calleeOut.store full := hnativeFull.trans cf childWithin
  have hd16 : (dst + 16).toNat = dst.toNat + 16 := by
    have := hw.readable.low
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  have retOutside : Outside full fr.rsp 8 := by
    refine ⟨by have := hreadret.low; omega, ?_⟩
    intro r hin
    simp only [full, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region]
      omega
    · simp only [span, hd16]
      omega
  have retAddr : sp + 8 + 136 = fr.rsp := by dsimp only [sp]; bv_omega
  have hretFinal : memLoad calleeOut.store (sp + 8 + 136) 64 = fr.ret := by
    rw [retAddr]
    exact (hfull.memLoad_eq retOutside).trans hret
  obtain ⟨o, hrunReturn, htag, hstore, hspOut, hkeepOut, hTypesOut⟩ :=
    batch_return_runBlock code calleeOut.values calleeOut.store (sp + 8)
      (by rw [csp, aspGet]; rfl) calleeTypes
      (by rw [retAddr]; exact hreadret.of_frame hfull)
      (by rw [hretFinal]; exact hretlow)
  have returnExec : LIR.program.Exec (dialect code)
      ⟨⟨.l109d81, calleeOut.values, calleeOut.store⟩, []⟩ o := by
    apply Program.Exec.done
    rw [Program.step, hrunReturn]
    rfl
  have hexec : LIR.program.Exec (dialect code)
      ⟨⟨.l109ac0, args, fr.original⟩, []⟩ o := by
    apply CFGCall.exec_call hcall calleeExec ?_ returnExec
    rw [calleeTag]
    rfl
  have calleeStable : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
      calleeOut.values[r] = args[r] := by
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c3.trans ((congrArg (fun v : Value => Value.mk 64 (v.get 64)) (keep 3 (by decide))).trans
        (hTypes.value ⟨3, by decide⟩).symm)
    · exact c5.trans ((congrArg (fun v : Value => Value.mk 64 (v.get 64)) (keep 5 (by decide))).trans
        (hTypes.value ⟨5, by decide⟩).symm)
    · exact c12.trans ((congrArg (fun v : Value => Value.mk 64 (v.get 64)) (keep 12 (by decide))).trans
        (hTypes.value ⟨12, by decide⟩).symm)
    · exact c13.trans ((congrArg (fun v : Value => Value.mk 64 (v.get 64)) (keep 13 (by decide))).trans
        (hTypes.value ⟨13, by decide⟩).symm)
    · exact c14.trans ((congrArg (fun v : Value => Value.mk 64 (v.get 64)) (keep 14 (by decide))).trans
        (hTypes.value ⟨14, by decide⟩).symm)
    · exact c15.trans ((congrArg (fun v : Value => Value.mk 64 (v.get 64)) (keep 15 (by decide))).trans
        (hTypes.value ⟨15, by decide⟩).symm)
    · exact cdf.trans hdf.symm
    · rw [a39, h39] at c39
      exact c39.trans h39.symm
    · rw [a50, h50] at c50
      exact c50.trans h50.symm
    · rw [a51, h51] at c51
      exact c51.trans h51.symm
  have stable : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
      o.values[r] = args[r] := fun r hr => (hkeepOut r hr).trans (calleeStable r hr)
  have hdone : Atom.All code o.values o.store (LIR.Fn109ac0.frameInfo.doneAtoms fr) := by
    change o.values[4] = ⟨64, fr.rsp + 8⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      o.values[3] = ⟨64, fr.rbx⟩ ∧ o.values[5] = ⟨64, fr.rbp⟩ ∧
      o.values[12] = ⟨64, fr.r12⟩ ∧ o.values[13] = ⟨64, fr.r13⟩ ∧
      o.values[14] = ⟨64, fr.r14⟩ ∧ o.values[15] = ⟨64, fr.r15⟩ ∧
      o.values[39] = ⟨32, fr.mxcsr⟩ ∧ o.values[50] = ⟨16, fr.ftw⟩ ∧
      o.values[51] = ⟨16, fr.fcw⟩ ∧ True
    refine ⟨?_, (stable 22 (by decide)).trans hdf, (stable 3 (by decide)).trans h3,
      (stable 5 (by decide)).trans h5, (stable 12 (by decide)).trans h12,
      (stable 13 (by decide)).trans h13, (stable 14 (by decide)).trans h14,
      (stable 15 (by decide)).trans h15, (stable 39 (by decide)).trans h39,
      (stable 50 (by decide)).trans h50, (stable 51 (by decide)).trans h51, trivial⟩
    simpa only [show sp + 8 + 144 = fr.rsp + 8 by dsimp only [sp]; bv_omega] using hspOut
  have p : memLoad calleeOut.store (dst + 16) 64 =
      (rawUpdateBlocks prepared src 4 (memLoad prepared dst 64) (memLoad prepared (dst + 8) 64)
        (memLoad prepared (dst + 16) 64, memLoad prepared (dst + 24) 64)).1 ∧
      memLoad calleeOut.store (dst + 24) 64 =
      (rawUpdateBlocks prepared src 4 (memLoad prepared dst 64) (memLoad prepared (dst + 8) 64)
        (memLoad prepared (dst + 16) 64, memLoad prepared (dst + 24) 64)).2 := by
    simpa only [activationOfValues, asrcGet, adstGet] using calleePost
  have s0 := stateLoad 0 (by decide)
  have s8 := stateLoad 8 (by decide)
  have s16 := stateLoad 16 (by decide)
  have s24 := stateLoad 24 (by decide)
  simp only [BitVec.add_zero] at s0
  simp only [BitVec.ofNat_eq_ofNat] at p
  simp only [s0, s8, s16, s24] at p
  have hraw (y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) :
      rawUpdateBlocks prepared src 4 y0 y1 initial = updateBlocks fr.original fr.rsi 4 y0 y1 initial :=
    rawUpdateBlocks_eq_updateBlocks prepared fr.original src fr.rsi y0 y1 4 initial
      (fun j hj => (words ⟨j,hj⟩).1) (fun j hj => (words ⟨j,hj⟩).2)
  rw [hraw] at p
  refine ⟨o, hexec, ?_, hdone, hTypesOut, ?_, ?_⟩
  · exact htag.trans (congrArg (fun v => some (Value.mk 64 v)) hretFinal)
  · simpa only [hstore] using hfull
  · simpa only [hstore, BitVec.ofNat_eq_ofNat] using p

end AesGcm.Proofs.Machine.GHASHUpdate
