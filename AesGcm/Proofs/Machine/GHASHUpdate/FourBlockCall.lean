import AesGcm.Proofs.Machine.GHASHUpdate.FourBlocks
import AesGcm.Proofs.Machine.GHASHUpdate.Blocks

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface
open AesGcm.Proofs.Machine.GHASH

set_option maxHeartbeats 3000000 in
theorem fourBlock_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) :
    CallContract LIR.lifted code .l1034d0 LIR.Fn1034d0.frameInfo
      (fun fr => [span (fr.rdi + 16) 16])
      (fun fr mem => Readable mem fr.rsi 64 ∧ Writable code mem fr.rdi 32 ∧
        (callStack fr).Disjoint (span fr.rsi 64) ∧
        (callStack fr).Disjoint (span fr.rdi 32) ∧
        (span fr.rdi 32).Disjoint (span fr.rsi 64))
      (fun fr mem =>
        let result := rawUpdateBlocks fr.original fr.rsi 4
          (memLoad fr.original fr.rdi 64) (memLoad fr.original (fr.rdi + 8) 64)
          (memLoad fr.original (fr.rdi + 16) 64, memLoad fr.original (fr.rdi + 24) 64)
        memLoad mem (fr.rdi + 16) 64 = result.1 ∧ memLoad mem (fr.rdi + 24) 64 = result.2) := by
  intro fr loc hl hm hentry htypes hpre
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm hentry htypes hpre
  subst label mem
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 160) 160 ∧
    fr.low.toNat + 160 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, -, -, h3, h5, hsrc, hdst, -, -, h12, h13, h14, h15,
    h39, h50, h51, hreadret, hret, hretlow, hstack, hroom, halign, -⟩
  rcases hpre with ⟨hr, hw, hsrcsep, hdstsep, hdatasep⟩
  let sp := fr.rsp - 24
  let saved := fourSavedMemory fr.original fr.rsp (args[14].get 64) (args[3].get 64) (args[0].get 64)
  let full := [fr.region, span (fr.rdi + 16) 16]
  let work := [⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩, span (fr.rdi + 16) 16]
  have hsub : sp.toNat = fr.rsp.toNat - 24 := by
    have hle : (24 : BitVec 64) ≤ fr.rsp := by change 24 ≤ fr.rsp.toNat; omega
    simpa [sp] using BitVec.toNat_sub_of_le hle
  have hstate16 : (fr.rdi + 16).toNat = fr.rdi.toNat + 16 := by
    have := hw.readable.low
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  have srcBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat 64 (by omega) (by decide) hsrcsep
  have dstBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 32 (by omega) (by decide) hdstsep
  have dataBounds := disjoint_bounds fr.rdi.toNat 32 fr.rsi.toNat 64
    (by decide) (by decide) hdatasep
  have srcOutside : Outside full fr.rsi 64 := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    simp only [full, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region]
      omega
    · simp only [span, hstate16]
      omega
  have keyOutside : Outside full fr.rdi 16 := by
    refine ⟨by have := hw.readable.low; omega, ?_⟩
    intro r hin
    simp only [full, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region]
      omega
    · simp only [span, hstate16]
      omega
  have workWithin : RegionsWithin work full := by
    intro r hin
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨fr.region, by simp [full], Nat.le_refl _, ?_⟩
      simp only [Activation.region, hsub]
      omega
    · exact ⟨span (fr.rdi + 16) 16, by simp [full], Nat.le_refl _, Nat.le_refl _⟩
  have hfSaved := fourSavedMemory_frame fr.original fr.rsp
    (args[14].get 64) (args[3].get 64) (args[0].get 64) (by omega)
  change RamWriteFrame fr.original saved [span sp 24] at hfSaved
  have hfSavedFull : RamWriteFrame fr.original saved full := by
    apply (RamWriteFrame.refl _ _).trans hfSaved
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp [full], ?_, ?_⟩ <;>
      simp only [Activation.region, span, hsub] <;> omega
  have savedStateOutside : Outside [span sp 24] fr.rdi 32 := by
    refine ⟨by have := hw.readable.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hsub]
    omega
  have sourceLoad (m : Ram) (hf : RamWriteFrame fr.original m full) (off : Nat)
      (ho : off + 8 ≤ 64) :
      memLoad m (fr.rsi + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 off) 64 :=
    hf.memLoad_eq (outside_add_offset srcOutside (by decide) ho)
  have keyLoad (m : Ram) (hf : RamWriteFrame fr.original m full) (off : Nat)
      (ho : off + 8 ≤ 16) :
      memLoad m (fr.rdi + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (fr.rdi + BitVec.ofNat 64 off) 64 :=
    hf.memLoad_eq (outside_add_offset keyOutside (by decide) ho)
  have savedLoad (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad saved (fr.rdi + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (fr.rdi + BitVec.ofNat 64 off) 64 :=
    hfSaved.memLoad_eq (outside_add_offset savedStateOutside (by decide) ho)
  have workStack : Writable code saved (sp - 136) 136 := by
    have he : sp - 136 = fr.rsp - 160 := by dsimp only [sp]; bv_omega
    rw [he]
    exact (hstack.of_frame hfSaved).sub (Nat.le_refl _) (by omega)
  have workRoom : fr.low.toNat + 136 ≤ sp.toNat := by rw [hsub]; omega
  have workAlign : sp.toNat % 16 = 0 := by rw [hsub]; omega
  have workSep : (⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩ : MemoryRegion).Disjoint
      (span fr.rdi 32) := by
    intro x hx hy
    apply hdstsep x ?_ hy
    simp only [MemoryRegion.Contains, callStack, hsub] at hx ⊢
    omega
  obtain ⟨a0, hcall0, h02, h06, h03, h014, h04, hkeep0, htypes0⟩ :=
    fourBlock_entry_runBlock code hcode args fr.original fr.rsi fr.rdi fr.rsp
      (by rw [hsrc]; rfl) (by rw [hdst]; rfl) (by rw [hsp]; rfl) hr hstack htypes
  have k039 : a0[39] = args[39] := hkeep0 39 (by decide)
  have k050 : a0[50] = args[50] := hkeep0 50 (by decide)
  have k051 : a0[51] = args[51] := hkeep0 51 (by decide)
  have k022 : a0[22] = args[22] := hkeep0 22 (by decide)
  have k07 : a0[7] = args[7] := hkeep0 7 (by decide)
  have fp39 : args[39] = ⟨32, args[39].get 32⟩ := by rw [h39]; rfl
  have fp50 : args[50] = ⟨16, args[50].get 16⟩ := by rw [h50]; rfl
  have fp51 : args[51] = ⟨16, args[51].get 16⟩ := by rw [h51]; rfl
  obtain ⟨o0, he0, tag0, sp0, pres0, types0, frame0, post0⟩ :=
    multiply_pushed code hmultiply saved a0 sp fr.rdi 0x1034e6 fr.low
      (by rw [h04]; change fr.rsp - 32 = (fr.rsp - 24) - 8; bv_omega)
      (by rw [k07, hdst]; rfl) htypes0
      (by rw [k039]; exact fp39) (by rw [k050]; exact fp50) (by rw [k051]; exact fp51)
      (k022.trans hdf) (by decide) workStack workRoom workAlign (hw.of_frame hfSaved) workSep
  have hf0 : RamWriteFrame fr.original o0.store full := hfSavedFull.trans frame0 workWithin
  have stable0 : ∀ r : Fin 53, r.val ∈ [5, 12, 13, 15, 22, 39, 50, 51] → o0.values[r] = args[r] := by
    intro r hr'
    exact (pres0 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; omega)).trans
      (hkeep0 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; omega))
  have bx0 : o0.values[3] = ⟨64, fr.rsi⟩ := (pres0 3 (by decide)).trans h03
  have r140 : o0.values[14] = ⟨64, fr.rdi⟩ := (pres0 14 (by decide)).trans h014
  obtain ⟨o1, reach1, sp1, pres1, types1, frame1, post1⟩ :=
    fourBlock_middle_exec false code hcode hmultiply o0.values o0.store fr.rsi fr.rdi sp fr.low
      (by rw [bx0]; rfl) (by rw [r140]; rfl) (by rw [sp0]; rfl) types0
      (by have h : o0.values[39] = args[39] := stable0 39 (by decide); rw [h]; exact fp39)
      (by have h : o0.values[50] = args[50] := stable0 50 (by decide); rw [h]; exact fp50)
      (by have h : o0.values[51] = args[51] := stable0 51 (by decide); rw [h]; exact fp51)
      ((stable0 22 (by decide)).trans hdf) (hr.of_frame hf0)
      (workStack.of_frame frame0)
      workRoom workAlign (hw.of_frame hf0) workSep
  have hf1 : RamWriteFrame fr.original o1.store full := hf0.trans frame1 workWithin
  have stable1 : ∀ r : Fin 53, r.val ∈ [5, 12, 13, 15, 22, 39, 50, 51] → o1.values[r] = args[r] := by
    intro r hr'
    exact (pres1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; omega)).trans
      (stable0 r hr')
  have bx1 : o1.values[3] = ⟨64, fr.rsi⟩ := (pres1 3 (by decide)).trans bx0
  have r141 : o1.values[14] = ⟨64, fr.rdi⟩ := (pres1 14 (by decide)).trans r140
  obtain ⟨o2, reach2, sp2, pres2, types2, frame2, post2⟩ :=
    fourBlock_middle_exec true code hcode hmultiply o1.values o1.store fr.rsi fr.rdi sp fr.low
      (by rw [bx1]; rfl) (by rw [r141]; rfl) (by rw [sp1]; rfl) types1
      (by have h : o1.values[39] = args[39] := stable1 39 (by decide); rw [h]; exact fp39)
      (by have h : o1.values[50] = args[50] := stable1 50 (by decide); rw [h]; exact fp50)
      (by have h : o1.values[51] = args[51] := stable1 51 (by decide); rw [h]; exact fp51)
      ((stable1 22 (by decide)).trans hdf) (hr.of_frame hf1)
      (workStack.of_frame (frame0.trans frame1 (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)))
      workRoom workAlign (hw.of_frame hf1) workSep
  have hf2 : RamWriteFrame fr.original o2.store full := hf1.trans frame2 workWithin
  have stable2 : ∀ r : Fin 53, r.val ∈ [5, 12, 13, 15, 22, 39, 50, 51] → o2.values[r] = args[r] := by
    intro r hr'
    exact (pres2 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; omega)).trans
      (stable1 r hr')
  have bx2 : o2.values[3] = ⟨64, fr.rsi⟩ := (pres2 3 (by decide)).trans bx1
  have r142 : o2.values[14] = ⟨64, fr.rdi⟩ := (pres2 14 (by decide)).trans r141
  have hfSaved2 : RamWriteFrame saved o2.store work :=
    (frame0.trans frame1 (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)).trans frame2
      (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have tailStack : Readable o2.store sp 24 := by
    apply (hstack.readable.of_frame hf2).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨a3, htail, h32, h36, h37, h34, h33, h314, keep3, types3⟩ :=
    fourBlock_tail_runBlock code o2.values o2.store fr.rsi fr.rdi sp
      (by rw [bx2]; rfl) (by rw [r142]; rfl) (by rw [sp2]; rfl)
      (hr.of_frame hf2) tailStack types2
  have savedOutside : Outside work sp 24 := by
    refine ⟨by have := fr.rsp.isLt; omega, ?_⟩
    intro r hin
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · dsimp only
      omega
    · simp only [span, hstate16]
      omega
  have saved3 : memLoad o2.store (sp + 8) 64 = fr.rbx := by
    have heq : memLoad o2.store (sp + 8) 64 = memLoad saved (sp + 8) 64 := hfSaved2.memLoad_eq (outside_add_offset (off := 8) (n := 8) savedOutside (by decide) (by decide))
    rw [heq]
    have hh := (fourSavedMemory_load fr.original fr.rsp
      (args[14].get 64) (args[3].get 64) (args[0].get 64)).1
    change memLoad saved (fr.rsp - 16) 64 = args[3].get 64 at hh
    rw [show sp + 8 = fr.rsp - 16 by dsimp only [sp]; bv_omega, hh, h3]
    rfl
  have saved14 : memLoad o2.store (sp + 16) 64 = fr.r14 := by
    have heq : memLoad o2.store (sp + 16) 64 = memLoad saved (sp + 16) 64 := hfSaved2.memLoad_eq (outside_add_offset (off := 16) (n := 8) savedOutside (by decide) (by decide))
    rw [heq]
    have hh := (fourSavedMemory_load fr.original fr.rsp
      (args[14].get 64) (args[3].get 64) (args[0].get 64)).2
    change memLoad saved (fr.rsp - 8) 64 = args[14].get 64 at hh
    rw [show sp + 16 = fr.rsp - 8 by dsimp only [sp]; bv_omega, hh, h14]
    rfl
  have retOutside : Outside full fr.rsp 8 := by
    refine ⟨by have := hreadret.low; omega, ?_⟩
    intro r hin
    simp only [full, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region]
      omega
    · simp only [span, hstate16]
      omega
  have stable3 : ∀ r : Fin 53, r.val ∈ [5, 12, 13, 15, 22, 39, 50, 51] → a3[r] = args[r] := by
    intro r hr'
    exact (keep3 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; omega)).trans
      (stable2 r hr')
  obtain ⟨o3, he3, tag3, sp3, pres3, typesOut, frame3, post3⟩ :=
    multiply_values code hmultiply o2.store a3 fr.rsp fr.rdi fr.ret fr.low
      (by rw [h34]; change sp + 24 = fr.rsp; dsimp only [sp]; bv_omega)
      (by rw [h37]; rfl) types3
      (by have h : a3[39] = args[39] := stable3 39 (by decide); rw [h]; exact fp39)
      (by have h : a3[50] = args[50] := stable3 50 (by decide); rw [h]; exact fp50)
      (by have h : a3[51] = args[51] := stable3 51 (by decide); rw [h]; exact fp51)
      ((stable3 22 (by decide)).trans hdf) (hreadret.of_frame hf2)
      ((hf2.memLoad_eq retOutside).trans hret) hretlow
      ((hstack.of_frame hf2).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by omega) halign (hw.of_frame hf2) hdstsep
  have hfinal : LIR.program.Exec (dialect code)
      ⟨⟨.l103506, o2.values, o2.store⟩, []⟩ o3 := by
    apply Program.Exec.next (next := ⟨⟨.l102bd0, a3, o2.store⟩, []⟩) ?_ he3
    rw [Program.step, htail]
    rfl
  have hcontinuation : LIR.program.Exec (dialect code)
      ⟨⟨.l1034e6, o0.values, o0.store⟩, []⟩ o3 :=
    .of_sem ((reach1.trans reach2).exec hfinal.sem)
  have hresume0 := CFGCall.exec_reaches_resume he0 fourEntryFrame [] (by rw [tag0]; rfl)
  have hreach0 : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨.l1034d0, args, fr.original⟩, []⟩
      ⟨⟨.l1034e6, o0.values, o0.store⟩, []⟩ := by
    have hs : LIR.program.step (dialect code) ⟨⟨.l1034d0, args, fr.original⟩, []⟩ =
        .next ⟨⟨.l102bd0, a0, memStore saved (sp - 8) (0x1034e6#64)⟩, [fourEntryFrame]⟩ := by
      rw [Program.step, hcall0]
      simp only [Transfer.next, saved,
        show sp - 8 = fr.rsp - 32 by dsimp only [sp]; bv_omega]
    exact (Semantics.Reaches.single hs).trans hresume0
  have hexec : LIR.program.Exec (dialect code)
      ⟨⟨.l1034d0, args, fr.original⟩, []⟩ o3 :=
    .of_sem (hreach0.exec hcontinuation.sem)
  have hdone : Atom.All code o3.values o3.store (LIR.Fn1034d0.frameInfo.doneAtoms fr) := by
    change o3.values[4] = ⟨64, fr.rsp + 8⟩ ∧ o3.values[22] = ⟨1, 0⟩ ∧
      o3.values[3] = ⟨64, fr.rbx⟩ ∧ o3.values[5] = ⟨64, fr.rbp⟩ ∧
      o3.values[12] = ⟨64, fr.r12⟩ ∧ o3.values[13] = ⟨64, fr.r13⟩ ∧
      o3.values[14] = ⟨64, fr.r14⟩ ∧ o3.values[15] = ⟨64, fr.r15⟩ ∧
      o3.values[39] = ⟨32, fr.mxcsr⟩ ∧ o3.values[50] = ⟨16, fr.ftw⟩ ∧
      o3.values[51] = ⟨16, fr.fcw⟩ ∧ True
    have hf (r : Fin 53) (hr' : r.val ∈ [5, 12, 13, 15, 22, 39, 50, 51]) :
        o3.values[r] = args[r] :=
      (pres3 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; omega)).trans
        (stable3 r hr')
    refine ⟨sp3, (hf 22 (by decide)).trans hdf, ?_, (hf 5 (by decide)).trans h5,
      (hf 12 (by decide)).trans h12, (hf 13 (by decide)).trans h13, ?_,
      (hf 15 (by decide)).trans h15, (hf 39 (by decide)).trans h39,
      (hf 50 (by decide)).trans h50, (hf 51 (by decide)).trans h51, trivial⟩
    · exact (pres3 3 (by decide)).trans (h33.trans (congrArg (fun v => Value.mk 64 v) saved3))
    · exact (pres3 14 (by decide)).trans (h314.trans (congrArg (fun v => Value.mk 64 v) saved14))
  refine ⟨o3, hexec, tag3, hdone, typesOut,
    hf2.trans frame3 (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩), ?_⟩
  have e06 : a0[6].get 64 = memLoad saved fr.rsi 64 := by rw [h06]; rfl
  have e02 : a0[2].get 64 = memLoad saved (fr.rsi + 8) 64 := by rw [h02]; rfl
  have e36 : a3[6].get 64 = memLoad o2.store (fr.rsi + 48) 64 := by rw [h36]; rfl
  have e32 : a3[2].get 64 = memLoad o2.store (fr.rsi + 56) 64 := by rw [h32]; rfl
  have s0 := sourceLoad saved hfSavedFull 0 (by decide)
  have s8 := sourceLoad saved hfSavedFull 8 (by decide)
  have u16 := sourceLoad o0.store hf0 16 (by decide)
  have u24 := sourceLoad o0.store hf0 24 (by decide)
  have v32 := sourceLoad o1.store hf1 32 (by decide)
  have v40 := sourceLoad o1.store hf1 40 (by decide)
  have w48 := sourceLoad o2.store hf2 48 (by decide)
  have w56 := sourceLoad o2.store hf2 56 (by decide)
  have k0 := keyLoad o0.store hf0 0 (by decide)
  have k8 := keyLoad o0.store hf0 8 (by decide)
  have l0 := keyLoad o1.store hf1 0 (by decide)
  have l8 := keyLoad o1.store hf1 8 (by decide)
  have m0 := keyLoad o2.store hf2 0 (by decide)
  have m8 := keyLoad o2.store hf2 8 (by decide)
  have d0 := savedLoad 0 (by decide)
  have a8 := savedLoad 8 (by decide)
  have a16 := savedLoad 16 (by decide)
  have a24 := savedLoad 24 (by decide)
  simp only [fourMiddleOffset] at post1 post2
  rw [show fr.rsi + 16 + 8 = fr.rsi + 24 by bv_omega] at post1
  rw [show fr.rsi + 32 + 8 = fr.rsi + 40 by bv_omega] at post2
  simp only [BitVec.add_zero] at s0 s8 u16 u24 v32 v40 w48 w56
  simp only [BitVec.add_zero] at k0 k8 l0 l8 m0 m8 d0 a8 a16 a24
  simp only [BitVec.ofNat_eq_ofNat] at post0 post1 post2 post3 e06 e02 e36 e32
  simp only [e06, e02, s0, s8, d0, a8, a16, a24] at post0
  simp only [u16, u24, k0, k8, post0.1, post0.2] at post1
  simp only [v32, v40, l0, l8, post1.1, post1.2] at post2
  simp only [e36, e32, w48, w56, m0, m8, post2.1, post2.2] at post3
  simpa only [rawUpdateBlocks_four, BitVec.ofNat_eq_ofNat] using post3


end AesGcm.Proofs.Machine.GHASHUpdate
